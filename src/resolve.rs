//! Lexical name resolution for recovery-free surface syntax.

use std::{
    collections::{HashMap, HashSet},
    fmt,
    ops::{Deref, Range},
    sync::Arc,
};

use crate::{
    core::capture::CaptureGraphVisits,
    diagnostic::{Diagnostic, SourceLabel},
    interface::{
        CheckedRequirement, ConstrainedScheme, EvidenceSlot, ImplId, ImplMethodId,
        InterfaceConstraintBudget, InterfaceId, MatchedNominalIdentities, MethodId, RequirementId,
        RequirementOwner, collect_type_nominal_identities_with_constraint_budget,
    },
    module::{LoadedModule, ModuleDependency, ModuleId},
    resolved::{
        AuthorizedImplementationFact, Binder, BinderId, CandidateConstructor, CandidateEffect,
        CandidateFactSource, CandidateGlobal, CandidateHiddenNominal, CandidateInterface,
        CandidateMethod, CandidateNominal, CheckedImplementationFact, CheckedInterfaceFact,
        CheckedInterfaceMethodFact, DirectDependencyRoute, ExportSummary, ExportedConstructor,
        ExportedGlobal, ExportedType, ExportedTypeAccess, ImplementationAuthorization,
        ImplementationRouteRank, ImportedConstructorFact, ImportedFacts, ImportedGlobalScheme,
        ImportedNominalMergeFailure, ImportedTypeAccess, ResolvedApplicationExpr,
        ResolvedBinaryExpr, ResolvedBinding, ResolvedBlock, ResolvedBuildFailure,
        ResolvedConstructor, ResolvedConstructorOccurrence, ResolvedDefinition,
        ResolvedDefinitionKind, ResolvedDeterminationParameter, ResolvedDeterminationSide,
        ResolvedEffectDeclaration, ResolvedEffectInstance, ResolvedEffectOperation,
        ResolvedEquation, ResolvedEquationalGlobal, ResolvedExportCandidate, ResolvedExpr,
        ResolvedExprKind, ResolvedExternalInterface, ResolvedFunctionExpr, ResolvedHandleExpr,
        ResolvedHandlerClause, ResolvedImplementation, ResolvedImplementationMethodGroup,
        ResolvedInlineOperationalGlobal, ResolvedInlineOperationalHeader,
        ResolvedInterfaceApplication, ResolvedInterfaceDeclaration, ResolvedInterfaceDetermination,
        ResolvedInterfaceMethod, ResolvedInterfaceOccurrence, ResolvedLocalDeclaration,
        ResolvedMatchArm, ResolvedMatchExpr, ResolvedModule, ResolvedModuleParts,
        ResolvedNominalDeclarationKind, ResolvedNominalType, ResolvedOccurrence, ResolvedPattern,
        ResolvedPatternKind, ResolvedPerformExpr, ResolvedRecursiveGroup, ResolvedRecursiveMember,
        ResolvedRegistry, ResolvedRequirement, ResolvedResumeExpr, ResolvedTermName, ResolvedType,
        ResolvedTypeProvenance, ResolvedTypeProvenanceNode, ResolvedTypeVariable,
        ResolvedTypedPattern, ResumeId, ValidatedImportedNominalMerge, WithheldExport,
        WithheldExportKind, WithheldNamespace, clone_resolved_effect_with_budget,
        clone_resolved_type_variable_with_budget, clone_resolved_type_variables_with_budget,
        discard_resolved_definition_iteratively, discard_resolved_effect_iteratively,
        discard_resolved_equation_iteratively, discard_resolved_expression_iteratively,
        discard_resolved_implementation_iteratively, discard_resolved_interface_iteratively,
        discard_resolved_local_declaration_iteratively, discard_resolved_pattern_iteratively,
        discard_resolved_requirement,
        same_checked_implementation_fact_observing_nominals_with_budget,
        same_checked_interface_fact_observing_nominals_with_budget,
        same_imported_constructor_fact_observing_nominals_with_budget,
        same_imported_global_fact_observing_nominals_with_budget,
        same_imported_nominal_closure_with_constraint_budget,
    },
    source::{Origin, Span, discard_origin_iteratively},
    surface::{
        BinaryExpr, SurfaceBinding, SurfaceBlock, SurfaceConstructorDeclaration,
        SurfaceDeclarationIndex, SurfaceDefinition, SurfaceDefinitionKind,
        SurfaceEffectDeclaration, SurfaceExpr, SurfaceExprKind, SurfaceImplementation,
        SurfaceImportItem, SurfaceImportSelection, SurfaceInterfaceApplication,
        SurfaceInterfaceDeclaration, SurfaceInterfaceDetermination, SurfaceKind, SurfaceKindKind,
        SurfaceLocalDeclaration, SurfaceModule, SurfaceName, SurfaceNominalDeclarationKind,
        SurfacePattern, SurfacePatternKind, SurfaceRecursiveGroup, SurfaceReference,
        SurfaceRequirement, SurfaceType, SurfaceTypeDeclaration, SurfaceTypeKind,
        SurfaceTypeParameter, SurfaceTypeVisibility,
    },
    types::{
        ComputationType, ConstructorId, EffectId, EffectInstance, EffectRow, EffectRowVariable,
        IterativeTypeOwner, Kind, NominalTypeId, OperationId, Type, TypeVariableId, TypeWorkBudget,
        charge_kind_nodes, charge_type_cells, clone_type_with_budget,
        compare_effect_instances_with_budget, discard_type_iteratively,
        effect_row_from_canonical_source_parts_with_budget, same_kind_with_charge,
    },
};

struct ResolvedTypeBuffer(Vec<(Type, usize)>);

struct ImportedTypeCloneBuffer(Vec<Type>);

struct ImportedTypeVariableBuffer(Vec<ResolvedTypeVariable>);

struct ImportedConstructorFactBuffer(Vec<ImportedConstructorFact>);

fn build_source_effect_row_with_provenance(
    written: Vec<(EffectInstance, crate::source::Span, Box<[usize]>)>,
    tail: Option<EffectRowVariable>,
    span: crate::source::Span,
    budget: &mut TypeWorkBudget,
) -> Result<(EffectRow, Box<[usize]>), ResolveError> {
    for index in 0..written.len() {
        for earlier in 0..index {
            if compare_effect_instances_with_budget(&written[earlier].0, &written[index].0, budget)
                .map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        written[index].1,
                        "effect-row duplicate comparison exceeded its type-work budget",
                    )
                })?
                == std::cmp::Ordering::Equal
            {
                let mut failure = error(
                    ResolveReason::DuplicateEffect,
                    written[index].1,
                    "this exact effect instance is already present in the written row",
                );
                failure.0.related.push(SourceLabel::new(
                    written[earlier].1,
                    "the first exact effect instance is here",
                ));
                return Err(failure);
            }
        }
    }

    let mut canonical: Vec<(EffectInstance, Box<[usize]>)> = Vec::new();
    for (instance, instance_span, roots) in written {
        let mut position = 0;
        while position < canonical.len()
            && compare_effect_instances_with_budget(&canonical[position].0, &instance, budget)
                .map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        instance_span,
                        "effect-row canonicalization exceeded its type-work budget",
                    )
                })?
                == std::cmp::Ordering::Less
        {
            position += 1;
        }
        budget.charge(1).map_err(|()| {
            error(
                ResolveReason::TypeResourceExhausted,
                instance_span,
                "effect-row retention exceeded its type-work budget",
            )
        })?;
        canonical.try_reserve(1).map_err(|_| {
            error(
                ResolveReason::TypeResourceExhausted,
                instance_span,
                "effect-row retention could not reserve storage",
            )
        })?;
        canonical.insert(position, (instance, roots));
    }

    let root_count = canonical
        .iter()
        .try_fold(0usize, |count, (_, roots)| count.checked_add(roots.len()));
    let root_count = root_count.ok_or_else(|| {
        error(
            ResolveReason::TypeResourceExhausted,
            span,
            "effect-argument provenance exceeded its type-work budget",
        )
    })?;
    budget.charge(root_count).map_err(|()| {
        error(
            ResolveReason::TypeResourceExhausted,
            span,
            "effect-argument provenance exceeded its type-work budget",
        )
    })?;
    let mut roots = Vec::new();
    roots.try_reserve_exact(root_count).map_err(|_| {
        error(
            ResolveReason::TypeResourceExhausted,
            span,
            "effect-argument provenance could not reserve storage",
        )
    })?;
    budget.charge(canonical.len()).map_err(|()| {
        error(
            ResolveReason::TypeResourceExhausted,
            span,
            "effect-row retention exceeded its type-work budget",
        )
    })?;
    let mut instances = Vec::new();
    instances.try_reserve_exact(canonical.len()).map_err(|_| {
        error(
            ResolveReason::TypeResourceExhausted,
            span,
            "effect-row retention could not reserve storage",
        )
    })?;
    for (instance, argument_roots) in canonical {
        instances.push(instance);
        roots.extend(argument_roots);
    }
    let row = effect_row_from_canonical_source_parts_with_budget(instances, tail, budget).map_err(
        |()| {
            error(
                ResolveReason::TypeResourceExhausted,
                span,
                "effect-row rebuild exceeded its type-work budget",
            )
        },
    )?;
    Ok((row, roots.into_boxed_slice()))
}

#[derive(Clone, Copy)]
struct ValidatedImportedConstructorRoute<'summary> {
    exported: &'summary ExportedConstructor,
    requires_commit: bool,
}

impl ImportedConstructorFactBuffer {
    fn try_reserve(&mut self, additional: usize) -> Result<(), std::collections::TryReserveError> {
        self.0.try_reserve(additional)
    }

    fn push(&mut self, fact: ImportedConstructorFact) {
        self.0.push(fact);
    }

    fn into_vec(mut self) -> Vec<ImportedConstructorFact> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for ImportedConstructorFactBuffer {
    fn drop(&mut self) {
        for fact in self.0.drain(..) {
            fact.discard_iteratively();
        }
    }
}

impl ImportedTypeVariableBuffer {
    fn try_reserve(&mut self, additional: usize) -> Result<(), std::collections::TryReserveError> {
        self.0.try_reserve(additional)
    }

    fn push(&mut self, parameter: ResolvedTypeVariable) {
        self.0.push(parameter);
    }

    fn into_boxed_slice(mut self) -> Box<[ResolvedTypeVariable]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}

impl Drop for ImportedTypeVariableBuffer {
    fn drop(&mut self) {
        for parameter in self.0.drain(..) {
            discard_origin_iteratively(parameter.origin);
        }
    }
}

impl ImportedTypeCloneBuffer {
    fn push(&mut self, ty: Type) {
        self.0.push(ty);
    }

    fn pop_owned(&mut self) -> Option<IterativeTypeOwner> {
        self.0.pop().map(IterativeTypeOwner::new)
    }

    fn split_off(&mut self, at: usize) -> Self {
        Self(self.0.split_off(at))
    }

    fn into_vec(mut self) -> Vec<Type> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for ImportedTypeCloneBuffer {
    fn drop(&mut self) {
        while let Some(ty) = self.0.pop() {
            discard_type_iteratively(ty);
        }
    }
}

impl Deref for ResolvedTypeBuffer {
    type Target = Vec<(Type, usize)>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl ResolvedTypeBuffer {
    fn push(&mut self, value: (Type, usize)) {
        self.0.push(value);
    }

    fn pop_owned(&mut self) -> Option<(IterativeTypeOwner, usize)> {
        self.0
            .pop()
            .map(|(ty, root)| (IterativeTypeOwner::new(ty), root))
    }

    fn split_off(&mut self, at: usize) -> Self {
        Self(self.0.split_off(at))
    }

    fn into_vec(mut self) -> Vec<(Type, usize)> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for ResolvedTypeBuffer {
    fn drop(&mut self) {
        while let Some((ty, _)) = self.0.pop() {
            discard_type_iteratively(ty);
        }
    }
}

struct ResolvedExpressionOwner(Option<ResolvedExpr>);

impl ResolvedExpressionOwner {
    fn new(expression: ResolvedExpr) -> Self {
        Self(Some(expression))
    }

    fn into_inner(mut self) -> ResolvedExpr {
        self.0.take().expect("a resolved expression transfers once")
    }
}

impl Deref for ResolvedExpressionOwner {
    type Target = ResolvedExpr;

    fn deref(&self) -> &Self::Target {
        self.0
            .as_ref()
            .expect("a resolved expression remains owned")
    }
}

impl Drop for ResolvedExpressionOwner {
    fn drop(&mut self) {
        if let Some(expression) = self.0.take() {
            discard_resolved_expression_iteratively(expression);
        }
    }
}

struct ResolvedExpressionBuffer(Vec<ResolvedExpr>);

impl Deref for ResolvedExpressionBuffer {
    type Target = Vec<ResolvedExpr>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl ResolvedExpressionBuffer {
    fn push(&mut self, expression: ResolvedExpr) {
        self.0.push(expression);
    }

    fn pop_owned(&mut self) -> Option<ResolvedExpressionOwner> {
        self.0.pop().map(ResolvedExpressionOwner::new)
    }

    fn split_off(&mut self, at: usize) -> Self {
        Self(self.0.split_off(at))
    }

    fn into_vec(mut self) -> Vec<ResolvedExpr> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for ResolvedExpressionBuffer {
    fn drop(&mut self) {
        for expression in self.0.drain(..) {
            discard_resolved_expression_iteratively(expression);
        }
    }
}

struct ResolvedPatternOwner(Option<ResolvedPattern>);

impl ResolvedPatternOwner {
    fn new(pattern: ResolvedPattern) -> Self {
        Self(Some(pattern))
    }

    fn into_inner(mut self) -> ResolvedPattern {
        self.0.take().expect("a resolved pattern transfers once")
    }
}

impl Drop for ResolvedPatternOwner {
    fn drop(&mut self) {
        if let Some(pattern) = self.0.take() {
            discard_resolved_pattern_iteratively(pattern);
        }
    }
}

struct ResolvedPatternBuffer(Vec<ResolvedPattern>);

impl ResolvedPatternBuffer {
    fn pop(&mut self) -> Option<ResolvedPattern> {
        self.0.pop()
    }

    fn into_vec(mut self) -> Vec<ResolvedPattern> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for ResolvedPatternBuffer {
    fn drop(&mut self) {
        for pattern in self.0.drain(..) {
            discard_resolved_pattern_iteratively(pattern);
        }
    }
}

struct ResolvedDeclarationBuffer(Vec<ResolvedLocalDeclaration>);

impl Deref for ResolvedDeclarationBuffer {
    type Target = Vec<ResolvedLocalDeclaration>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl ResolvedDeclarationBuffer {
    fn push(&mut self, declaration: ResolvedLocalDeclaration) {
        self.0.push(declaration);
    }

    fn split_off(&mut self, at: usize) -> Self {
        Self(self.0.split_off(at))
    }

    fn into_vec(mut self) -> Vec<ResolvedLocalDeclaration> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for ResolvedDeclarationBuffer {
    fn drop(&mut self) {
        for declaration in self.0.drain(..) {
            discard_resolved_local_declaration_iteratively(declaration);
        }
    }
}

struct ResolvedTypeOccurrenceBuffer(Vec<ResolvedType>);

impl ResolvedTypeOccurrenceBuffer {
    fn into_vec(mut self) -> Vec<ResolvedType> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for ResolvedTypeOccurrenceBuffer {
    fn drop(&mut self) {
        for resolved in self.0.drain(..) {
            resolved.discard_iteratively();
        }
    }
}

struct ResolvedDeterminationParameterBuffer(Vec<ResolvedDeterminationParameter>);

impl ResolvedDeterminationParameterBuffer {
    fn into_boxed_slice(mut self) -> Box<[ResolvedDeterminationParameter]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}

impl Drop for ResolvedDeterminationParameterBuffer {
    fn drop(&mut self) {
        for parameter in self.0.drain(..) {
            discard_origin_iteratively(parameter.origin);
        }
    }
}

struct ResolvedTypeOccurrenceOwner(Option<ResolvedType>);

impl ResolvedTypeOccurrenceOwner {
    fn new(resolved: ResolvedType) -> Self {
        Self(Some(resolved))
    }

    fn into_inner(mut self) -> ResolvedType {
        self.0
            .take()
            .expect("a resolved type occurrence transfers once")
    }
}

impl Drop for ResolvedTypeOccurrenceOwner {
    fn drop(&mut self) {
        if let Some(resolved) = self.0.take() {
            resolved.discard_iteratively();
        }
    }
}

struct ResolvedMatchArmBuffer(Vec<ResolvedMatchArm>);

impl ResolvedMatchArmBuffer {
    fn into_vec(mut self) -> Vec<ResolvedMatchArm> {
        std::mem::take(&mut self.0)
    }
}

struct ResolvedInterfaceMethodBuffer(Vec<ResolvedInterfaceMethod>);

impl ResolvedInterfaceMethodBuffer {
    fn into_vec(mut self) -> Vec<ResolvedInterfaceMethod> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for ResolvedInterfaceMethodBuffer {
    fn drop(&mut self) {
        for method in self.0.drain(..) {
            method.annotation.discard_iteratively();
            for parameter in method.type_parameters.into_vec() {
                discard_origin_iteratively(parameter.origin);
            }
            discard_origin_iteratively(method.origin);
        }
    }
}

struct ResolvedInterfaceBuffer(Vec<ResolvedInterfaceDeclaration>);

impl ResolvedInterfaceBuffer {
    fn into_vec(mut self) -> Vec<ResolvedInterfaceDeclaration> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for ResolvedInterfaceBuffer {
    fn drop(&mut self) {
        for interface in self.0.drain(..) {
            discard_resolved_interface_iteratively(interface);
        }
    }
}

struct ResolvedRequirementBuffer(Vec<ResolvedRequirement>);

impl ResolvedRequirementBuffer {
    fn into_boxed_slice(mut self) -> Box<[ResolvedRequirement]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}

impl Drop for ResolvedRequirementBuffer {
    fn drop(&mut self) {
        for requirement in self.0.drain(..) {
            discard_resolved_requirement(requirement);
        }
    }
}

struct ResolvedEquationBuffer(Vec<ResolvedEquation>);

impl ResolvedEquationBuffer {
    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn into_vec(mut self) -> Vec<ResolvedEquation> {
        std::mem::take(&mut self.0)
    }

    fn into_boxed_slice(mut self) -> Box<[ResolvedEquation]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}

impl Drop for ResolvedEquationBuffer {
    fn drop(&mut self) {
        for equation in self.0.drain(..) {
            discard_resolved_equation_iteratively(equation);
        }
    }
}

struct ResolvedTypedPatternBuffer(Vec<ResolvedTypedPattern>);

impl ResolvedTypedPatternBuffer {
    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn into_vec(mut self) -> Vec<ResolvedTypedPattern> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for ResolvedTypedPatternBuffer {
    fn drop(&mut self) {
        for pattern in self.0.drain(..) {
            discard_resolved_pattern_iteratively(pattern.pattern);
            pattern.annotation.discard_iteratively();
        }
    }
}

struct ResolvedDefinitionBuffer(Vec<ResolvedDefinition>);

impl ResolvedDefinitionBuffer {
    fn into_vec(mut self) -> Vec<ResolvedDefinition> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for ResolvedDefinitionBuffer {
    fn drop(&mut self) {
        for definition in self.0.drain(..) {
            discard_resolved_definition_iteratively(definition);
        }
    }
}

struct ResolvedImplementationMethodGroupBuffer(Vec<ResolvedImplementationMethodGroup>);

impl ResolvedImplementationMethodGroupBuffer {
    fn into_boxed_slice(mut self) -> Box<[ResolvedImplementationMethodGroup]> {
        std::mem::take(&mut self.0).into_boxed_slice()
    }
}

impl Drop for ResolvedImplementationMethodGroupBuffer {
    fn drop(&mut self) {
        for group in self.0.drain(..) {
            for parameter in group.contextual_parameters.into_vec() {
                discard_origin_iteratively(parameter.origin);
            }
            discard_origin_iteratively(group.binder.origin);
            for equation in group.equations.into_vec() {
                discard_resolved_equation_iteratively(equation);
            }
        }
    }
}

struct ResolvedImplementationBuffer(Vec<ResolvedImplementation>);

impl ResolvedImplementationBuffer {
    fn into_vec(mut self) -> Vec<ResolvedImplementation> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for ResolvedImplementationBuffer {
    fn drop(&mut self) {
        for implementation in self.0.drain(..) {
            discard_resolved_implementation_iteratively(implementation);
        }
    }
}

struct ResolvedConstructorOwnerBuffer(Vec<ResolvedConstructor>);

impl ResolvedConstructorOwnerBuffer {
    fn into_vec(mut self) -> Vec<ResolvedConstructor> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for ResolvedConstructorOwnerBuffer {
    fn drop(&mut self) {
        for constructor in self.0.drain(..) {
            constructor.discard_iteratively();
        }
    }
}

struct ResolvedNominalOwnerBuffer(Vec<ResolvedNominalType>);

impl ResolvedNominalOwnerBuffer {
    fn into_vec(mut self) -> Vec<ResolvedNominalType> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for ResolvedNominalOwnerBuffer {
    fn drop(&mut self) {
        for nominal in self.0.drain(..) {
            if let Some(representation) = nominal.representation {
                discard_type_iteratively(representation);
            }
            discard_origin_iteratively(nominal.origin);
        }
    }
}

struct ResolvedNominalParameterOwnerBuffer(Vec<(NominalTypeId, Vec<ResolvedTypeVariable>)>);

impl ResolvedNominalParameterOwnerBuffer {
    fn into_vec(mut self) -> Vec<(NominalTypeId, Vec<ResolvedTypeVariable>)> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for ResolvedNominalParameterOwnerBuffer {
    fn drop(&mut self) {
        for (_, parameters) in self.0.drain(..) {
            for parameter in parameters {
                discard_origin_iteratively(parameter.origin);
            }
        }
    }
}

impl Drop for ResolvedMatchArmBuffer {
    fn drop(&mut self) {
        for arm in self.0.drain(..) {
            discard_resolved_pattern_iteratively(arm.pattern);
            discard_resolved_expression_iteratively(arm.body);
        }
    }
}

/// The semantic reason that prevented name resolution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResolveReason {
    /// Source evidence cannot introduce the compiler-owned cell provider.
    SealedProvider,
    /// Resource acquisition requires a direct compiler-owned cell dependency.
    ResourceBuiltinRequired,
    /// An occurrence has no binding in lexical scope.
    UnknownName,
    /// The equation head repeats a different name from its interface.
    EquationNameMismatch,
    /// A file contains a second global with the same spelling.
    DuplicateGlobal,
    /// A file contains a second nominal type spelling.
    DuplicateType,
    /// A file contains a second constructor spelling.
    DuplicateConstructor,
    /// A newtype constructor does not repeat its nominal spelling.
    NewtypeConstructorName,
    /// Two complete imports bind the same module alias.
    DuplicateModuleAlias,
    /// An imported spelling is private or otherwise unavailable.
    UnavailableExport,
    /// An import binding conflicts with another file-wide binding.
    ImportConflict,
    /// A source occurrence attempts to inspect an opaque constructor.
    OpaqueConstructor,
    /// A declaration repeats one type-parameter spelling.
    DuplicateTypeParameter,
    /// An explicit declaration type parameter has no header occurrence.
    UnusedTypeParameter,
    /// A source type occurrence names no declaration.
    UnknownType,
    /// An uppercase type name has the wrong sort or incompatible type roles.
    TypeKind,
    /// An interface position names no interface declaration.
    UnknownInterface,
    /// A nominal type or type parameter was used as an interface.
    InterfaceKind,
    /// An effect operation did not have one pure outer function arrow.
    EffectOperationShape,
    /// A source row or request names no effect declaration.
    UnknownEffect,
    /// A non-effect uppercase name was used as an effect.
    EffectKind,
    /// A written row repeats one exact effect instance.
    DuplicateEffect,
    /// A resume form occurs outside an operation clause.
    ResumeOutsideClause,
    /// An uppercase term or pattern names no constructor.
    UnknownConstructor,
    /// One pattern vector binds the same spelling more than once.
    DuplicatePatternBinder,
    /// A recursive group contains a second member with the same spelling.
    DuplicateRecursiveMember,
    /// The resolver cannot assign another distinct binder identity.
    BinderIdExhausted,
    /// Cumulative source-type resolution exceeded the compiler work budget.
    TypeResourceExhausted,
    /// Graph-wide interface and constraint processing exceeded its work budget.
    ConstraintResourceExhausted,
    /// An internal resolver invariant was lost.
    InternalState,
}

impl fmt::Display for ResolveReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::SealedProvider => "resolve.sealed-provider",
            Self::ResourceBuiltinRequired => "resolve.resource-builtin-required",
            Self::UnknownName => "resolve.unknown-name",
            Self::EquationNameMismatch => "resolve.equation-name-mismatch",
            Self::DuplicateGlobal => "resolve.duplicate-global",
            Self::DuplicateType => "resolve.duplicate-type",
            Self::DuplicateConstructor => "resolve.duplicate-constructor",
            Self::NewtypeConstructorName => "resolve.newtype-constructor-name",
            Self::DuplicateModuleAlias => "resolve.duplicate-module-alias",
            Self::UnavailableExport => "resolve.unavailable-export",
            Self::ImportConflict => "resolve.import-conflict",
            Self::OpaqueConstructor => "resolve.opaque-constructor",
            Self::DuplicateTypeParameter => "resolve.duplicate-type-parameter",
            Self::UnusedTypeParameter => "resolve.unused-type-parameter",
            Self::UnknownType => "resolve.unknown-type",
            Self::TypeKind => "resolve.type-kind",
            Self::UnknownInterface => "resolve.unknown-interface",
            Self::InterfaceKind => "resolve.interface-kind",
            Self::EffectOperationShape => "effect.operation-shape",
            Self::UnknownEffect => "effect.unknown",
            Self::EffectKind => "effect.kind",
            Self::DuplicateEffect => "effect.duplicate",
            Self::ResumeOutsideClause => "effect.resume-outside-clause",
            Self::UnknownConstructor => "resolve.unknown-constructor",
            Self::DuplicatePatternBinder => "pattern.duplicate-binder",
            Self::DuplicateRecursiveMember => "resolve.duplicate-recursive-member",
            Self::BinderIdExhausted => "resolve.binder-id-exhausted",
            Self::TypeResourceExhausted => "resolve.type-resource",
            Self::ConstraintResourceExhausted => "internal.resource.constraint-work",
            Self::InternalState => "resolve.internal-state",
        })
    }
}

/// A structured name-resolution failure kept compact in pipeline results.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolveError(Box<Diagnostic<ResolveReason>>, Option<ResolveContext>);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ResolveContext {
    WorkState {
        part: &'static str,
        problem: &'static str,
    },
    DeclarationOrder {
        kind: &'static str,
        problem: &'static str,
    },
    MissingFileScope,
    MissingLexicalScope,
    MissingNominalScope,
    MissingConstructorScope,
    DependencySummaryMismatch,
    DependencySummaryInvalid,
    Kind(crate::kind::KindFailureContext),
    Term,
    EffectOperation,
    Type,
    EffectRowParameter,
    InterfaceParameter,
    Constructor,
    Interface,
    Effect,
    ExportedEffect,
    PrivateExport,
    MissingExport,
    MissingModuleAlias,
    MixedTypeRowRoles,
    IdentityExhaustion(ResolveIdentitySpace),
}

/// The compiler identity space exhausted during resolution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ResolveIdentitySpace {
    /// Identifiers for interfaces in a module.
    Interface,
    /// Identifiers for methods in an interface.
    Method,
    /// Identifiers for effects in a module.
    Effect,
    /// Identifiers for operations in an effect.
    Operation,
    /// Identifiers for implementations in a module.
    Implementation,
    /// Identifiers for interface requirements in a declaration.
    Requirement,
    /// Identifiers for nominal types in a module.
    Nominal,
    /// Identifiers for constructors in a declaration.
    Constructor,
    /// Value binders, including generated implementation binders.
    TermBinder,
    /// Type binders, including lexical method parameters.
    TypeBinder,
    /// Local nominal declarations.
    LocalNominal,
    /// Handler, hook and registration continuations.
    Continuation,
    /// Lexical evidence identities, including resource providers.
    LexicalEvidence,
}

impl ResolveIdentitySpace {
    pub(crate) const fn diagnostic_name(self) -> &'static str {
        match self {
            Self::TermBinder => "term-binder",
            Self::Interface => "interface",
            Self::Method => "method",
            Self::Effect => "effect",
            Self::Operation => "operation",
            Self::Implementation => "implementation",
            Self::Requirement => "requirement",
            Self::Nominal => "nominal",
            Self::Constructor => "constructor",
            Self::TypeBinder => "type-binder",
            Self::LocalNominal => "local-nominal",
            Self::Continuation => "continuation",
            Self::LexicalEvidence => "lexical-evidence",
        }
    }
}

impl ResolveError {
    fn with_context(mut self, context: ResolveContext) -> Self {
        self.1 = Some(context);
        self
    }

    fn internal_message(&self) -> Option<(crate::message::Message<'static>, &'static str)> {
        use crate::message::Message;
        match self.1 {
            Some(ResolveContext::WorkState { part, problem }) => {
                Some((Message::resolve_work_state(part, problem), "work-state"))
            }
            Some(ResolveContext::DeclarationOrder { kind, problem }) => Some((
                Message::resolve_declaration_order(kind, problem),
                "declaration-order",
            )),
            Some(ResolveContext::MissingFileScope) => {
                Some((Message::resolve_missing_file_scope(), "missing-file-scope"))
            }
            Some(ResolveContext::MissingLexicalScope) => Some((
                Message::resolve_missing_lexical_scope(),
                "missing-lexical-scope",
            )),
            Some(ResolveContext::MissingNominalScope) => Some((
                Message::resolve_missing_nominal_scope(),
                "missing-nominal-scope",
            )),
            Some(ResolveContext::MissingConstructorScope) => Some((
                Message::resolve_missing_constructor_scope(),
                "missing-constructor-scope",
            )),
            Some(ResolveContext::DependencySummaryMismatch) => Some((
                Message::resolve_dependency_summary_mismatch(),
                "dependency-summary-mismatch",
            )),
            Some(ResolveContext::DependencySummaryInvalid) => Some((
                Message::resolve_dependency_summary_invalid(),
                "dependency-summary-invalid",
            )),
            _ => None,
        }
    }
    pub(crate) fn kind_context(&self) -> Option<crate::kind::KindFailureContext> {
        match self.1 {
            Some(ResolveContext::Kind(context)) => Some(context),
            _ => None,
        }
    }

    pub(crate) fn declaration_order_context(&self) -> Option<(&'static str, &'static str)> {
        match self.1 {
            Some(ResolveContext::DeclarationOrder { kind, problem }) => Some((kind, problem)),
            _ => None,
        }
    }

    pub(crate) fn work_state_context(&self) -> Option<(&'static str, &'static str)> {
        match self.1 {
            Some(ResolveContext::WorkState { part, problem }) => Some((part, problem)),
            _ => None,
        }
    }

    pub(crate) fn resource_name(&self) -> Option<&'static str> {
        match self.reason {
            ResolveReason::TypeResourceExhausted => Some("type-work"),
            ResolveReason::ConstraintResourceExhausted => Some("constraint-work"),
            _ => None,
        }
    }

    pub(crate) const fn is_source_rejection(&self) -> bool {
        !matches!(
            self.0.reason,
            ResolveReason::BinderIdExhausted
                | ResolveReason::TypeResourceExhausted
                | ResolveReason::ConstraintResourceExhausted
                | ResolveReason::InternalState
        )
    }

    fn identity_space(&self) -> Option<ResolveIdentitySpace> {
        match self.1 {
            Some(ResolveContext::IdentityExhaustion(space)) => Some(space),
            _ => None,
        }
    }

    const fn is_duplicate_declaration(&self) -> bool {
        matches!(
            self.0.reason,
            ResolveReason::DuplicateGlobal
                | ResolveReason::DuplicateType
                | ResolveReason::DuplicateConstructor
                | ResolveReason::DuplicateModuleAlias
                | ResolveReason::DuplicateTypeParameter
                | ResolveReason::DuplicatePatternBinder
                | ResolveReason::DuplicateRecursiveMember
        )
    }

    pub(crate) fn primary_message(&self) -> Option<(crate::message::Message<'_>, &'static str)> {
        if self.identity_space().is_some() {
            return Some((self.message()?, "identity_allocation"));
        }
        if let Some((message, _)) = self.internal_message() {
            return Some((message, "resolution_site"));
        }
        if let Some(context) = self.kind_context() {
            return Some((
                if context.span() == self.primary.span() {
                    context.message()
                } else {
                    crate::message::Message::resolve_kind_use()
                },
                "resolution_site",
            ));
        }
        if self.resource_name().is_some() {
            return Some((self.message()?, "resolution_site"));
        }
        match self.reason {
            ResolveReason::BinderIdExhausted => {
                return Some((self.message()?, "identity_allocation"));
            }
            ResolveReason::DuplicateEffect => {
                return Some((
                    crate::message::Message::resolve_duplicate_effect(),
                    "duplicate_effect_instance",
                ));
            }
            ResolveReason::EffectOperationShape => {
                return Some((self.message()?, "effect_operation_signature"));
            }
            ResolveReason::SealedProvider => {
                return Some((self.message()?, "sealed_provider_declaration"));
            }
            ResolveReason::ResourceBuiltinRequired => {
                return Some((self.message()?, "resource_acquisition"));
            }
            ResolveReason::ResumeOutsideClause => {
                return Some((self.message()?, "continuation_use"));
            }
            ResolveReason::TypeKind | ResolveReason::InterfaceKind | ResolveReason::EffectKind => {
                return Some((
                    crate::message::Message::incompatible_name_role(),
                    "incompatible_name_role",
                ));
            }
            ResolveReason::EquationNameMismatch | ResolveReason::NewtypeConstructorName => {
                return Some((crate::message::Message::incorrect_name(), "incorrect_name"));
            }
            ResolveReason::UnusedTypeParameter => {
                return Some((
                    crate::message::Message::unused_parameter(),
                    "unused_parameter",
                ));
            }
            ResolveReason::ImportConflict => {
                return Some((
                    crate::message::Message::conflicting_binding(),
                    "conflicting_binding",
                ));
            }
            ResolveReason::UnavailableExport | ResolveReason::OpaqueConstructor => {
                return Some((
                    crate::message::Message::inaccessible_name(),
                    "inaccessible_name",
                ));
            }
            _ => {}
        }
        if self.is_duplicate_declaration() {
            Some((crate::message::Message::duplicate_name(), "duplicate_name"))
        } else if self.1.is_some() {
            Some((
                crate::message::Message::unresolved_name(),
                "unresolved_name",
            ))
        } else {
            None
        }
    }

    pub(crate) fn related_message(
        &self,
        index: usize,
    ) -> Option<(crate::message::Message<'_>, &'static str)> {
        if index == 0 {
            match self.reason {
                ResolveReason::DuplicateEffect => {
                    return Some((
                        crate::message::Message::first_effect_instance(),
                        "first_effect_instance",
                    ));
                }
                ResolveReason::EquationNameMismatch | ResolveReason::NewtypeConstructorName => {
                    return Some((
                        crate::message::Message::required_name_declaration(),
                        "required_name_declaration",
                    ));
                }
                ResolveReason::UnavailableExport | ResolveReason::OpaqueConstructor => {
                    return Some((
                        crate::message::Message::inaccessible_declaration(),
                        "inaccessible_declaration",
                    ));
                }
                _ => {}
            }
        }
        if !self.is_duplicate_declaration() {
            return None;
        }
        match index {
            0 => Some((
                crate::message::Message::first_declaration(),
                "first_declaration",
            )),
            1 if self.reason == ResolveReason::DuplicateGlobal => Some((
                crate::message::Message::first_definition(),
                "first_definition",
            )),
            _ => None,
        }
    }

    pub(crate) const fn lookup_scope_name(&self) -> Option<&'static str> {
        match self.1 {
            Some(ResolveContext::Term) => Some("term"),
            Some(ResolveContext::EffectOperation) => Some("effect-operation"),
            Some(ResolveContext::Type) => Some("type"),
            Some(ResolveContext::EffectRowParameter) => Some("effect-row-parameter"),
            Some(ResolveContext::InterfaceParameter) => Some("interface-parameter"),
            Some(ResolveContext::Constructor) => Some("constructor"),
            Some(ResolveContext::Interface) => Some("interface"),
            Some(ResolveContext::Effect) => Some("effect"),
            Some(ResolveContext::ExportedEffect) => Some("exported-effect"),
            None
            | Some(
                ResolveContext::PrivateExport
                | ResolveContext::MissingExport
                | ResolveContext::MissingModuleAlias
                | ResolveContext::MixedTypeRowRoles
                | ResolveContext::Kind(_)
                | ResolveContext::DependencySummaryMismatch
                | ResolveContext::DependencySummaryInvalid
                | ResolveContext::DeclarationOrder { .. }
                | ResolveContext::WorkState { .. }
                | ResolveContext::MissingFileScope
                | ResolveContext::MissingLexicalScope
                | ResolveContext::MissingNominalScope
                | ResolveContext::MissingConstructorScope
                | ResolveContext::IdentityExhaustion(_),
            ) => None,
        }
    }

    pub(crate) fn subject_fact(&self) -> Option<(&'static str, &'static str, &str)> {
        if let Some(space) = self.identity_space() {
            return Some((
                "identity_space",
                "resolver-identity-space",
                space.diagnostic_name(),
            ));
        }
        if let Some((_, cause)) = self.internal_message() {
            return Some(("cause", "resolver-internal-cause", cause));
        }
        if let Some(context) = self.kind_context() {
            return Some(("kind_cause", "kind-internal-cause", context.name()));
        }
        if let Some(resource) = self.resource_name() {
            return Some(("resource", "resource", resource));
        }
        match self.reason {
            ResolveReason::BinderIdExhausted => Some((
                "identity_space",
                "resolver-identity-space",
                self.identity_space()?.diagnostic_name(),
            )),
            ResolveReason::ResourceBuiltinRequired => {
                Some(("required_builtin", "module-path", self.expected.as_deref()?))
            }
            ResolveReason::ResumeOutsideClause => {
                Some(("operation", "keyword", self.found.as_deref()?))
            }
            ResolveReason::EffectOperationShape
            | ResolveReason::SealedProvider
            | ResolveReason::DuplicateEffect => None,
            _ => Some(("name", "identifier", self.found.as_deref()?)),
        }
    }

    pub(crate) fn name_use(&self) -> Option<&'static str> {
        match self.reason {
            ResolveReason::TypeKind if self.1 == Some(ResolveContext::MixedTypeRowRoles) => {
                Some("mixed-type-and-row-tail")
            }
            ResolveReason::TypeKind => Some("interface-as-type"),
            ResolveReason::InterfaceKind => Some("interface-required"),
            ResolveReason::EffectKind => Some("effect-required"),
            _ => None,
        }
    }

    pub(crate) fn related_name(&self) -> Option<&str> {
        if self.is_duplicate_declaration() {
            self.found.as_deref()
        } else {
            // An imported spelling may differ from the inaccessible declaration's name.
            self.expected_name()
        }
    }

    pub(crate) fn expected_name(&self) -> Option<&str> {
        match self.reason {
            ResolveReason::EquationNameMismatch | ResolveReason::NewtypeConstructorName => {
                self.expected.as_deref()
            }
            _ => None,
        }
    }

    pub(crate) fn access_name(&self) -> Option<&'static str> {
        if self.reason == ResolveReason::OpaqueConstructor {
            return Some("opaque-constructor");
        }
        match self.1 {
            Some(ResolveContext::PrivateExport) => Some("private"),
            Some(ResolveContext::MissingExport) => Some("not-exported"),
            Some(ResolveContext::MissingModuleAlias) => Some("unknown-module-alias"),
            _ => None,
        }
    }

    pub(crate) fn message(&self) -> Option<crate::message::Message<'_>> {
        if let Some(space) = self.identity_space() {
            return Some(crate::message::Message::resolve_identity_exhausted(space));
        }
        if let Some((message, _)) = self.internal_message() {
            return Some(message);
        }
        if let Some(context) = self.kind_context() {
            return Some(context.message());
        }
        match self.reason {
            ResolveReason::TypeResourceExhausted => {
                return Some(crate::message::Message::resolve_type_resources());
            }
            ResolveReason::ConstraintResourceExhausted => {
                return Some(crate::message::Message::resolve_constraint_resources());
            }
            ResolveReason::BinderIdExhausted => {
                return Some(crate::message::Message::resolve_identity_exhausted(
                    self.identity_space()?,
                ));
            }
            ResolveReason::DuplicateEffect => {
                return Some(crate::message::Message::resolve_duplicate_effect());
            }
            ResolveReason::EffectOperationShape => {
                return Some(crate::message::Message::resolve_operation_shape());
            }
            ResolveReason::SealedProvider => {
                return Some(crate::message::Message::resolve_sealed_provider());
            }
            ResolveReason::ResourceBuiltinRequired => {
                return Some(crate::message::Message::resolve_builtin_required(
                    self.expected.as_deref()?,
                ));
            }
            ResolveReason::ResumeOutsideClause => {
                return Some(crate::message::Message::resolve_continuation_outside(
                    self.found.as_deref()?,
                ));
            }
            _ => {}
        }
        let name = self.found.as_deref()?;
        match self.reason {
            ResolveReason::TypeKind if self.1 == Some(ResolveContext::MixedTypeRowRoles) => {
                return Some(crate::message::Message::resolve_mixed_type_row_roles(name));
            }
            ResolveReason::TypeKind => {
                return Some(crate::message::Message::resolve_type_kind(name));
            }
            ResolveReason::InterfaceKind => {
                return Some(crate::message::Message::resolve_interface_kind(name));
            }
            ResolveReason::EffectKind => {
                return Some(crate::message::Message::resolve_effect_kind(name));
            }
            ResolveReason::EquationNameMismatch => {
                return Some(crate::message::Message::resolve_equation_name(
                    name,
                    self.expected_name()?,
                ));
            }
            ResolveReason::NewtypeConstructorName => {
                return Some(crate::message::Message::resolve_newtype_name(
                    name,
                    self.expected_name()?,
                ));
            }
            ResolveReason::UnusedTypeParameter => {
                return Some(crate::message::Message::resolve_unused_parameter(name));
            }
            ResolveReason::ImportConflict => {
                return Some(crate::message::Message::resolve_import_conflict(name));
            }
            ResolveReason::OpaqueConstructor => {
                return Some(crate::message::Message::resolve_opaque_constructor(name));
            }
            _ => {}
        }
        if self.is_duplicate_declaration() {
            return Some(match self.reason {
                ResolveReason::DuplicateGlobal => {
                    crate::message::Message::resolve_duplicate_global(name)
                }
                ResolveReason::DuplicateType => {
                    crate::message::Message::resolve_duplicate_type(name)
                }
                ResolveReason::DuplicateConstructor => {
                    crate::message::Message::resolve_duplicate_constructor(name)
                }
                ResolveReason::DuplicateModuleAlias => {
                    crate::message::Message::resolve_duplicate_alias(name)
                }
                ResolveReason::DuplicateTypeParameter => {
                    crate::message::Message::resolve_duplicate_parameter(name)
                }
                ResolveReason::DuplicatePatternBinder => {
                    crate::message::Message::resolve_duplicate_binder(name)
                }
                ResolveReason::DuplicateRecursiveMember => {
                    crate::message::Message::resolve_duplicate_recursive_member(name)
                }
                _ => return None,
            });
        }
        Some(match self.1? {
            ResolveContext::Term => crate::message::Message::resolve_unknown_term(name),
            ResolveContext::EffectOperation => {
                crate::message::Message::resolve_unknown_operation(name)
            }
            ResolveContext::Type => crate::message::Message::resolve_unknown_type(name),
            ResolveContext::EffectRowParameter => {
                crate::message::Message::resolve_unknown_row_parameter(name)
            }
            ResolveContext::InterfaceParameter => {
                crate::message::Message::resolve_unknown_interface_parameter(name)
            }
            ResolveContext::Constructor => {
                crate::message::Message::resolve_unknown_constructor(name)
            }
            ResolveContext::Interface => crate::message::Message::resolve_unknown_interface(name),
            ResolveContext::Effect => crate::message::Message::resolve_unknown_effect(name),
            ResolveContext::ExportedEffect => {
                crate::message::Message::resolve_unexported_effect(name)
            }
            ResolveContext::PrivateExport => crate::message::Message::resolve_private_export(name),
            ResolveContext::MissingExport => crate::message::Message::resolve_missing_export(name),
            ResolveContext::MissingModuleAlias => {
                crate::message::Message::resolve_missing_module_alias(name)
            }
            ResolveContext::MixedTypeRowRoles => {
                crate::message::Message::resolve_mixed_type_row_roles(name)
            }
            ResolveContext::IdentityExhaustion(_)
            | ResolveContext::Kind(_)
            | ResolveContext::DependencySummaryMismatch
            | ResolveContext::DependencySummaryInvalid
            | ResolveContext::DeclarationOrder { .. }
            | ResolveContext::WorkState { .. }
            | ResolveContext::MissingFileScope
            | ResolveContext::MissingLexicalScope
            | ResolveContext::MissingNominalScope
            | ResolveContext::MissingConstructorScope => return None,
        })
    }
    /// Returns the common structured diagnostic fields.
    /// Phase-specific diagnostic context remains on this failure owner.
    #[must_use]
    pub fn diagnostic(&self) -> &Diagnostic<ResolveReason> {
        &self.0
    }

    /// Consumes the failure and returns its common diagnostic fields.
    /// This legacy conversion does not retain phase-specific diagnostic context.
    #[must_use]
    pub fn into_diagnostic(self) -> Diagnostic<ResolveReason> {
        *self.0
    }
}

impl From<Diagnostic<ResolveReason>> for ResolveError {
    fn from(diagnostic: Diagnostic<ResolveReason>) -> Self {
        Self(Box::new(diagnostic), None)
    }
}

impl Deref for ResolveError {
    type Target = Diagnostic<ResolveReason>;

    fn deref(&self) -> &Self::Target {
        self.diagnostic()
    }
}

impl fmt::Display for ResolveError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0.render_plain())
    }
}

impl std::error::Error for ResolveError {}

/// A failure from the complete resolved-module pipeline.
#[derive(Debug)]
pub enum ResolveModuleError {
    /// Name and identity resolution rejected the source or lost an invariant.
    Resolution(ResolveError),
    /// Total resolved kind checking rejected the source or lost an invariant.
    Kind(crate::kind::KindFailure),
}

impl fmt::Display for ResolveModuleError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Resolution(error) => error.fmt(formatter),
            Self::Kind(error) => error.fmt(formatter),
        }
    }
}

impl std::error::Error for ResolveModuleError {}

/// One source import edge paired with its checked dependency summary.
#[derive(Clone, Copy, Debug)]
pub struct DependencyExports<'a> {
    edge: &'a ModuleDependency,
    summary: &'a ExportSummary,
}

impl<'a> DependencyExports<'a> {
    /// Authenticates a dependency edge and summary pair.
    ///
    /// # Errors
    ///
    /// Returns [`DependencyExportMismatch`] when the summary belongs to a
    /// different canonical module.
    pub fn new(
        edge: &'a ModuleDependency,
        summary: &'a ExportSummary,
    ) -> Result<Self, DependencyExportMismatch> {
        if edge.target() != summary.module() {
            return Err(DependencyExportMismatch);
        }
        Ok(Self { edge, summary })
    }
}

/// A dependency edge was paired with another module's summary.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct DependencyExportMismatch;

impl fmt::Display for DependencyExportMismatch {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("dependency export summary does not match its module edge")
    }
}

impl std::error::Error for DependencyExportMismatch {}

/// Resolves one declarations-only module from checked dependency summaries.
///
/// # Errors
///
/// Returns either a structured name/identity-resolution failure or a resolved
/// kind-stage failure. A successful result has passed both stages.
pub fn resolve_module(
    loaded: &LoadedModule,
    dependencies: &[DependencyExports<'_>],
) -> Result<ResolvedModule, ResolveModuleError> {
    let mut type_work = TypeWorkBudget::default();
    let mut constraint_work = InterfaceConstraintBudget::default();
    resolve_module_with_budget(loaded, dependencies, &mut type_work, &mut constraint_work)
}

/// Resolves one module while sharing type-work accounting across a graph pass.
pub(crate) fn resolve_module_with_budget(
    loaded: &LoadedModule,
    dependencies: &[DependencyExports<'_>],
    type_work: &mut TypeWorkBudget,
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<ResolvedModule, ResolveModuleError> {
    let admission =
        resolve_module_names_with_budget(loaded, dependencies, type_work, constraint_work)
            .map_err(ResolveModuleError::Resolution)?;
    crate::kind::check_resolved_module_with_budget(
        &admission.parts,
        &admission.constructor_payload_provenance,
        type_work,
    )
    .map_err(ResolveModuleError::Kind)?;
    Ok(ResolvedModule::new(admission.parts))
}

struct ResolvedModuleAdmission {
    parts: ResolvedModuleParts,
    constructor_payload_provenance: Vec<Vec<ConstructorPayloadProvenance>>,
}

/// Performs name and identity resolution without publishing unchecked output.
fn resolve_module_names_with_budget(
    loaded: &LoadedModule,
    dependencies: &[DependencyExports<'_>],
    type_work: &mut TypeWorkBudget,
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<ResolvedModuleAdmission, ResolveError> {
    let module = loaded.id();
    let surface = loaded.surface();
    reject_duplicate_module_aliases(surface)?;
    if dependencies.len() != loaded.dependencies().len()
        || surface.imports.len() != loaded.dependencies().len()
        || dependencies
            .iter()
            .zip(loaded.dependencies())
            .zip(&surface.imports)
            .any(|((dependency, loaded_edge), import)| {
                dependency.edge != loaded_edge
                    || loaded_edge.import_span() != import.span
                    || dependency.edge.target() != dependency.summary.module()
            })
    {
        return Err(error(
            ResolveReason::InternalState,
            surface.span,
            "the resolver received incomplete or mismatched dependency summaries",
        )
        .with_context(ResolveContext::DependencySummaryMismatch));
    }

    for dependency in dependencies {
        dependency
            .summary
            .authenticate(type_work, constraint_work)
            .map_err(|failure| {
                let (reason, message) = match failure {
                    ResolvedBuildFailure::Kind(context) => {
                        return kind_context_error(
                            context,
                            dependency.edge.import_span(),
                            "a dependency summary failed body-free authentication",
                        );
                    }
                    ResolvedBuildFailure::TypeResource => (
                        ResolveReason::TypeResourceExhausted,
                        "dependency-summary authentication exceeded its type-work budget",
                    ),
                    ResolvedBuildFailure::ConstraintResource => (
                        ResolveReason::ConstraintResourceExhausted,
                        "dependency-summary authentication exceeded its constraint-work budget",
                    ),
                    ResolvedBuildFailure::InvalidState => {
                        return error(
                            ResolveReason::InternalState,
                            dependency.edge.import_span(),
                            "a dependency summary failed body-free authentication",
                        )
                        .with_context(ResolveContext::DependencySummaryInvalid);
                    }
                };
                error(reason, dependency.edge.import_span(), message)
            })?;
    }

    let mut resolver = Resolver::with_budgets(
        module,
        std::mem::take(type_work),
        std::mem::take(constraint_work),
    );
    let result = (|| {
        resolver
            .constraint_work
            .charge(dependencies.len())
            .map_err(|()| {
                error(
                    ResolveReason::ConstraintResourceExhausted,
                    surface.span,
                    "direct dependency route retention exceeded its work budget",
                )
            })?;
        let mut direct_dependencies = Vec::new();
        direct_dependencies
            .try_reserve(dependencies.len())
            .map_err(|_| {
                error(
                    ResolveReason::ConstraintResourceExhausted,
                    surface.span,
                    "direct dependency route retention exceeded its work budget",
                )
            })?;
        direct_dependencies.extend(dependencies.iter().map(|dependency| {
            if dependency.edge.target().is_builtin_cell() {
                resolver.builtin_cell = Some(dependency.edge.target());
            }
            if dependency.edge.target().is_builtin_native_buffer() {
                resolver.builtin_native_buffer = Some(dependency.edge.target());
            }
            DirectDependencyRoute::new(dependency.edge.target(), dependency.edge.import_span())
        }));
        resolver.install_imports(surface, dependencies)?;
        resolver.validate_local_namespaces(surface)?;
        let declarations = resolver.resolve_declarations(surface)?;
        let imported = std::mem::take(&mut resolver.imported);
        let export_candidate = build_export_candidate(
            surface,
            &declarations.registry,
            &declarations.interfaces,
            &declarations.effects,
            &declarations.definitions,
            std::mem::take(&mut resolver.public_import_candidate),
            &mut resolver.type_work,
        )?;
        let declaration_order = retain_declaration_order(
            &surface.declaration_order,
            surface.span,
            &mut resolver.type_work,
        )?;
        let (
            registry,
            constructor_payload_provenance,
            interfaces,
            effects,
            implementations,
            definitions,
        ) = declarations.into_parts();
        Ok(ResolvedModuleAdmission {
            parts: ResolvedModuleParts {
                module,
                registry,
                imported,
                direct_dependencies,
                declaration_order,
                interfaces,
                effects,
                implementations,
                definitions,
                export_candidate,
                span: surface.span,
            },
            constructor_payload_provenance,
        })
    })();
    *type_work = std::mem::take(&mut resolver.type_work);
    *constraint_work = std::mem::take(&mut resolver.constraint_work);
    result
}

fn retain_declaration_order(
    source: &[SurfaceDeclarationIndex],
    span: crate::source::Span,
    budget: &mut TypeWorkBudget,
) -> Result<Vec<crate::resolved::ResolvedDeclarationIndex>, ResolveError> {
    budget.charge(source.len()).map_err(|()| {
        error(
            ResolveReason::TypeResourceExhausted,
            span,
            "resolved declaration-order retention exceeded its type-work budget",
        )
    })?;
    let mut retained = Vec::new();
    retained.try_reserve(source.len()).map_err(|_| {
        error(
            ResolveReason::TypeResourceExhausted,
            span,
            "resolved declaration-order retention could not reserve storage",
        )
    })?;
    retained.extend(source.iter().map(|declaration| match *declaration {
        SurfaceDeclarationIndex::Type(index) => {
            crate::resolved::ResolvedDeclarationIndex::Type(index)
        }
        SurfaceDeclarationIndex::Interface(index) => {
            crate::resolved::ResolvedDeclarationIndex::Interface(index)
        }
        SurfaceDeclarationIndex::Effect(index) => {
            crate::resolved::ResolvedDeclarationIndex::Effect(index)
        }
        SurfaceDeclarationIndex::Global(index) => {
            crate::resolved::ResolvedDeclarationIndex::Global(index)
        }
        SurfaceDeclarationIndex::Implementation(index) => {
            crate::resolved::ResolvedDeclarationIndex::Implementation(index)
        }
    }));
    Ok(retained)
}

fn reject_duplicate_module_aliases(surface: &SurfaceModule) -> Result<(), ResolveError> {
    let mut aliases = HashMap::new();
    for import in &surface.imports {
        let SurfaceImportSelection::Qualified { alias } = &import.selection else {
            continue;
        };
        if let Some(first) = aliases.insert(alias.text.as_str(), alias.span) {
            let mut diagnostic = Diagnostic::new(
                ResolveReason::DuplicateModuleAlias,
                SourceLabel::new(alias.span, "this module alias is already bound"),
            );
            diagnostic
                .related
                .push(SourceLabel::new(first, "the first module alias is here"));
            diagnostic.found = Some(alias.text.clone());
            return Err(diagnostic.into());
        }
    }
    Ok(())
}

fn build_export_candidate(
    surface: &SurfaceModule,
    registry: &ResolvedRegistry,
    interfaces: &[ResolvedInterfaceDeclaration],
    effects: &[ResolvedEffectDeclaration],
    definitions: &[ResolvedDefinition],
    mut candidate: ResolvedExportCandidate,
    type_work: &mut TypeWorkBudget,
) -> Result<ResolvedExportCandidate, ResolveError> {
    for (source, resolved) in surface.definitions.iter().zip(definitions) {
        if !source.public {
            let binder = definition_binder(resolved);
            candidate
                .try_insert_withheld(
                    WithheldNamespace::Term,
                    binder.spelling.clone(),
                    WithheldExport {
                        kind: WithheldExportKind::Private,
                        owner: None,
                        origin: Some(binder.origin.clone()),
                    },
                    type_work,
                )
                .map_err(|()| {
                    export_candidate_resource_error(
                        surface_definition_name(source).span,
                        "local export candidate retention exceeded its type-work budget",
                    )
                })?;
            continue;
        }
        let binder = definition_binder(resolved);
        candidate
            .try_insert_term(
                binder.spelling.clone(),
                CandidateGlobal {
                    binder: binder.id,
                    source: CandidateFactSource::Local,
                    origin: binder.origin.clone(),
                },
                type_work,
            )
            .map_err(|()| {
                export_candidate_resource_error(
                    surface_definition_name(source).span,
                    "local export candidate retention exceeded its type-work budget",
                )
            })?;
    }

    for (source, resolved) in surface.type_declarations.iter().zip(registry.nominals()) {
        if source.visibility == SurfaceTypeVisibility::Private {
            candidate
                .try_insert_hidden_nominal(
                    CandidateHiddenNominal {
                        id: resolved.id,
                        parameter_count: source.parameters.len(),
                        spelling: source.name.text.clone(),
                        origin: resolved.origin.clone(),
                    },
                    type_work,
                )
                .map_err(|()| {
                    export_candidate_resource_error(
                        source.name.span,
                        "local export candidate retention exceeded its type-work budget",
                    )
                })?;
            candidate
                .try_insert_withheld(
                    WithheldNamespace::Nominal,
                    source.name.text.clone(),
                    WithheldExport {
                        kind: WithheldExportKind::Private,
                        owner: None,
                        origin: Some(resolved.origin.clone()),
                    },
                    type_work,
                )
                .map_err(|()| {
                    export_candidate_resource_error(
                        source.name.span,
                        "local export candidate retention exceeded its type-work budget",
                    )
                })?;
            for (constructor, id) in source.constructors.iter().zip(&resolved.constructors) {
                let resolved_constructor = registry.constructor(*id).ok_or_else(|| {
                    error(
                        ResolveReason::InternalState,
                        constructor.span,
                        "the resolver lost a private constructor",
                    )
                })?;
                candidate
                    .try_insert_withheld(
                        WithheldNamespace::Constructor,
                        constructor.name.text.clone(),
                        WithheldExport {
                            kind: WithheldExportKind::Private,
                            owner: Some(resolved.id),
                            origin: Some(resolved_constructor.origin.clone()),
                        },
                        type_work,
                    )
                    .map_err(|()| {
                        export_candidate_resource_error(
                            constructor.name.span,
                            "local export candidate retention exceeded its type-work budget",
                        )
                    })?;
            }
            continue;
        }
        let access = match source.visibility {
            SurfaceTypeVisibility::PublicOpaque => ExportedTypeAccess::Opaque,
            SurfaceTypeVisibility::PublicTransparent => ExportedTypeAccess::Transparent,
            SurfaceTypeVisibility::Private => {
                return Err(error(
                    ResolveReason::InternalState,
                    source.name.span,
                    "a private nominal reached public export candidate construction",
                ));
            }
        };
        candidate
            .try_insert_nominal(
                source.name.text.clone(),
                CandidateNominal {
                    id: resolved.id,
                    access,
                    source: CandidateFactSource::Local,
                    origin: resolved.origin.clone(),
                },
                type_work,
            )
            .map_err(|()| {
                export_candidate_resource_error(
                    source.name.span,
                    "local export candidate retention exceeded its type-work budget",
                )
            })?;
        if source.visibility != SurfaceTypeVisibility::PublicTransparent {
            for (constructor, id) in source.constructors.iter().zip(&resolved.constructors) {
                let resolved_constructor = registry.constructor(*id).ok_or_else(|| {
                    error(
                        ResolveReason::InternalState,
                        constructor.span,
                        "the resolver lost an opaque constructor",
                    )
                })?;
                candidate
                    .try_insert_withheld(
                        WithheldNamespace::Constructor,
                        constructor.name.text.clone(),
                        WithheldExport {
                            kind: WithheldExportKind::OpaqueConstructor,
                            owner: Some(resolved.id),
                            origin: Some(resolved_constructor.origin.clone()),
                        },
                        type_work,
                    )
                    .map_err(|()| {
                        export_candidate_resource_error(
                            constructor.name.span,
                            "local export candidate retention exceeded its type-work budget",
                        )
                    })?;
            }
            continue;
        }
        for (constructor, id) in source.constructors.iter().zip(&resolved.constructors) {
            let resolved_constructor = registry.constructor(*id).ok_or_else(|| {
                error(
                    ResolveReason::InternalState,
                    constructor.span,
                    "the resolver lost a public constructor",
                )
            })?;
            candidate
                .try_insert_constructor(
                    constructor.name.text.clone(),
                    CandidateConstructor {
                        id: *id,
                        source: CandidateFactSource::Local,
                        origin: resolved_constructor.origin.clone(),
                    },
                    type_work,
                )
                .map_err(|()| {
                    export_candidate_resource_error(
                        constructor.name.span,
                        "local export candidate retention exceeded its type-work budget",
                    )
                })?;
        }
    }

    for interface in interfaces {
        if !interface.public {
            candidate
                .try_insert_withheld(
                    WithheldNamespace::Nominal,
                    interface.spelling.clone(),
                    WithheldExport {
                        kind: WithheldExportKind::Private,
                        owner: None,
                        origin: Some(interface.origin.clone()),
                    },
                    type_work,
                )
                .map_err(|()| {
                    export_candidate_resource_error(
                        interface.span,
                        "local export candidate retention exceeded its type-work budget",
                    )
                })?;
            for method in &interface.methods {
                candidate
                    .try_insert_withheld(
                        WithheldNamespace::Term,
                        method.spelling.clone(),
                        WithheldExport {
                            kind: WithheldExportKind::Private,
                            owner: None,
                            origin: Some(method.origin.clone()),
                        },
                        type_work,
                    )
                    .map_err(|()| {
                        export_candidate_resource_error(
                            method.span,
                            "local export candidate retention exceeded its type-work budget",
                        )
                    })?;
            }
            continue;
        }
        candidate
            .try_insert_interface(
                interface.spelling.clone(),
                CandidateInterface {
                    id: interface.id,
                    source: CandidateFactSource::Local,
                },
                type_work,
            )
            .map_err(|()| {
                export_candidate_resource_error(
                    interface.span,
                    "local export candidate retention exceeded its type-work budget",
                )
            })?;
        for method in &interface.methods {
            candidate
                .try_insert_method(
                    method.spelling.clone(),
                    CandidateMethod {
                        id: method.id,
                        source: CandidateFactSource::Local,
                    },
                    type_work,
                )
                .map_err(|()| {
                    export_candidate_resource_error(
                        method.span,
                        "local export candidate retention exceeded its type-work budget",
                    )
                })?;
        }
    }
    for effect in effects {
        if !effect.public {
            candidate
                .try_insert_withheld(
                    WithheldNamespace::Nominal,
                    effect.spelling.clone(),
                    WithheldExport {
                        kind: WithheldExportKind::Private,
                        owner: None,
                        origin: Some(effect.origin.clone()),
                    },
                    type_work,
                )
                .map_err(|()| {
                    export_candidate_resource_error(
                        effect.span,
                        "local export candidate retention exceeded its type-work budget",
                    )
                })?;
            continue;
        }
        candidate
            .try_insert_effect(
                effect.spelling.clone(),
                CandidateEffect {
                    id: effect.id,
                    source: CandidateFactSource::Local,
                },
                type_work,
            )
            .map_err(|()| {
                export_candidate_resource_error(
                    effect.span,
                    "local export candidate retention exceeded its type-work budget",
                )
            })?;
    }
    Ok(candidate)
}

fn export_candidate_resource_error(span: crate::source::Span, message: &str) -> ResolveError {
    error(ResolveReason::TypeResourceExhausted, span, message)
}

fn definition_binder(definition: &ResolvedDefinition) -> &Binder {
    match &definition.kind {
        ResolvedDefinitionKind::Equational(global) => &global.interface.name,
        ResolvedDefinitionKind::InlineOperational(global) => &global.header.name,
    }
}

fn surface_definition_name(definition: &SurfaceDefinition) -> &crate::surface::SurfaceName {
    match &definition.kind {
        SurfaceDefinitionKind::Equational(global) => &global.interface.name,
        SurfaceDefinitionKind::InlineOperational(global) => &global.header.name,
    }
}

struct Resolver {
    module: ModuleId,
    builtin_cell: Option<ModuleId>,
    builtin_native_buffer: Option<ModuleId>,
    next_binder: u32,
    next_type_variable: u32,
    next_lexical_nominal: u32,
    next_lexical_evidence: u32,
    resolved_interfaces: ResolvedInterfaceBuffer,
    lexical_method_parameters: ImportedTypeVariableBuffer,
    scopes: Vec<HashMap<String, ResolvedTermBinding>>,
    globals: HashMap<String, GlobalFact>,
    type_names: HashMap<String, NominalTypeId>,
    interface_names: HashMap<String, InterfaceId>,
    effect_names: HashMap<String, EffectId>,
    local_operation_names: HashMap<EffectId, HashMap<String, OperationId>>,
    method_names: HashMap<String, ResolvedTermBinding>,
    global_requirement_counts: HashMap<BinderId, usize>,
    constructor_names: HashMap<String, ConstructorId>,
    lexical_nominal_scopes: Vec<HashMap<String, NominalTypeId>>,
    lexical_constructor_scopes: Vec<HashMap<String, ConstructorId>>,
    lexical_nominals: ResolvedNominalOwnerBuffer,
    lexical_constructors: ResolvedConstructorOwnerBuffer,
    lexical_nominal_parameters: ResolvedNominalParameterOwnerBuffer,
    module_aliases: HashMap<String, ImportedNamespaces>,
    targeted_withheld: HashMap<(String, WithheldNamespace), WithheldImport>,
    public_import_candidate: ResolvedExportCandidate,
    imported: ImportedFacts,
    implementation_route_ranks: HashMap<ImplId, ImplementationRouteRank>,
    public_implementation_route_ranks: HashMap<ImplId, ImplementationRouteRank>,
    type_scopes: Vec<HashMap<String, TypeVariableId>>,
    nominal_parameter_counts: HashMap<NominalTypeId, usize>,
    active_resumes: Vec<ResumeId>,
    next_resume: u32,
    type_work: TypeWorkBudget,
    constraint_work: InterfaceConstraintBudget,
    #[cfg(test)]
    max_type_pending_tasks: usize,
}

struct GlobalFact {
    name_span: crate::source::Span,
    definition_span: crate::source::Span,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ResolvedTermBinding {
    term: ResolvedTermName,
    import_span: Option<crate::source::Span>,
}

impl ResolvedTermBinding {
    const fn local(term: ResolvedTermName) -> Self {
        Self {
            term,
            import_span: None,
        }
    }

    const fn imported(term: ResolvedTermName, import_span: crate::source::Span) -> Self {
        Self {
            term,
            import_span: Some(import_span),
        }
    }
}

struct PendingImplementation {
    id: ImplId,
    head_parameters: Vec<ResolvedTypeVariable>,
    prerequisite_only_parameters: Vec<ResolvedTypeVariable>,
    method_groups: Vec<PendingImplementationMethodGroup>,
}

struct NominalDeclarationIdentity {
    id: NominalTypeId,
    constructors: Vec<ConstructorId>,
}

fn validate_newtype_shape(
    declaration: &SurfaceTypeDeclaration,
) -> Result<(&SurfaceConstructorDeclaration, &SurfaceType), ResolveError> {
    let [constructor] = declaration.constructors.as_slice() else {
        return Err(error(
            ResolveReason::InternalState,
            declaration.span,
            "a projected newtype does not retain exactly one constructor",
        ));
    };
    let [representation] = constructor.fields.as_slice() else {
        return Err(error(
            ResolveReason::InternalState,
            constructor.span,
            "a projected newtype does not retain exactly one representation",
        ));
    };
    if constructor.name.text != declaration.name.text {
        let mut diagnostic = Diagnostic::new(
            ResolveReason::NewtypeConstructorName,
            SourceLabel::new(
                constructor.name.span,
                "this newtype constructor must use the nominal type's spelling",
            ),
        );
        diagnostic.related.push(SourceLabel::new(
            declaration.name.span,
            "this nominal declaration defines the required spelling",
        ));
        diagnostic.expected = Some(declaration.name.text.clone());
        diagnostic.found = Some(constructor.name.text.clone());
        return Err(diagnostic.into());
    }
    Ok((constructor, representation))
}

fn resolved_newtype_fact_pair(
    declaration: &SurfaceTypeDeclaration,
    constructor: &SurfaceConstructorDeclaration,
    id: NominalTypeId,
    constructor_id: ConstructorId,
    representation: IterativeTypeOwner,
    provenance: ResolvedTypeProvenance,
) -> Result<(ResolvedNominalType, ResolvedConstructor), ResolveError> {
    let nominal_spelling = try_clone_resolution_string(
        &declaration.name.text,
        declaration.name.span,
        "newtype nominal spelling storage could not be reserved",
    )?;
    let constructor_spelling = try_clone_resolution_string(
        &constructor.name.text,
        constructor.name.span,
        "newtype constructor spelling storage could not be reserved",
    )?;
    Ok((
        ResolvedNominalType {
            id,
            declaration_kind: ResolvedNominalDeclarationKind::Newtype,
            spelling: nominal_spelling,
            constructors: Box::new([constructor_id]),
            representation: Some(representation.into_inner()),
            representation_provenance: Some(provenance),
            origin: Origin::Source(declaration.span),
        },
        ResolvedConstructor {
            id: constructor_id,
            owner: id,
            spelling: constructor_spelling,
            payload: None,
            origin: Origin::Source(constructor.span),
        },
    ))
}

struct InterfaceDeclarationIdentity {
    id: InterfaceId,
    methods: Vec<MethodId>,
}

struct EffectDeclarationIdentity {
    id: EffectId,
    operations: Vec<OperationId>,
}

struct PendingInterfaceTypeParameters {
    parameters: Vec<ResolvedTypeVariable>,
    methods: Vec<Vec<ResolvedTypeVariable>>,
}

struct PendingImplementationMethodGroup {
    equations: Range<usize>,
    binder: Option<Binder>,
}

struct ResolvedDeclarations {
    registry: Arc<ResolvedRegistry>,
    constructor_payload_provenance: Vec<Vec<ConstructorPayloadProvenance>>,
    interfaces: Vec<ResolvedInterfaceDeclaration>,
    effects: Vec<ResolvedEffectDeclaration>,
    implementations: Vec<ResolvedImplementation>,
    definitions: Vec<ResolvedDefinition>,
}

type ResolvedDeclarationParts = (
    Arc<ResolvedRegistry>,
    Vec<Vec<ConstructorPayloadProvenance>>,
    Vec<ResolvedInterfaceDeclaration>,
    Vec<ResolvedEffectDeclaration>,
    Vec<ResolvedImplementation>,
    Vec<ResolvedDefinition>,
);

impl ResolvedDeclarations {
    fn into_parts(mut self) -> ResolvedDeclarationParts {
        (
            std::mem::take(&mut self.registry),
            std::mem::take(&mut self.constructor_payload_provenance),
            std::mem::take(&mut self.interfaces),
            std::mem::take(&mut self.effects),
            std::mem::take(&mut self.implementations),
            std::mem::take(&mut self.definitions),
        )
    }
}

#[derive(Debug)]
pub(crate) struct ConstructorPayloadProvenance {
    pub(crate) constructor: ConstructorId,
    pub(crate) fields: Vec<ResolvedTypeProvenance>,
}

impl Drop for ResolvedDeclarations {
    fn drop(&mut self) {
        for interface in self.interfaces.drain(..) {
            discard_resolved_interface_iteratively(interface);
        }
        for effect in self.effects.drain(..) {
            discard_resolved_effect_iteratively(effect);
        }
        for implementation in self.implementations.drain(..) {
            discard_resolved_implementation_iteratively(implementation);
        }
        for definition in self.definitions.drain(..) {
            discard_resolved_definition_iteratively(definition);
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum LocalTypeDeclarationKind {
    Nominal,
    Interface,
    Effect,
}

#[derive(Debug, Default)]
struct ImportedNamespaces {
    terms: HashMap<String, ResolvedTermBinding>,
    nominals: HashMap<String, ImportedNominalName>,
    interfaces: HashMap<String, InterfaceId>,
    effects: HashMap<String, EffectId>,
    constructors: HashMap<String, ConstructorId>,
    withheld: HashMap<(String, WithheldNamespace), WithheldImport>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ImportedInterfaceAccess {
    PublicExport,
    HiddenSummaryClosure,
}

#[derive(Clone, Copy, Debug)]
struct WithheldImport {
    kind: WithheldExportKind,
    declaration: Option<crate::source::Span>,
}

#[derive(Clone, Copy, Debug)]
struct ImportedNominalName {
    id: NominalTypeId,
}

#[derive(Clone, Copy, Debug)]
struct ImplementationImportSelection {
    direct_dependency: ModuleId,
    selector_span: crate::source::Span,
    import_span: crate::source::Span,
    public: bool,
    route_rank: ImplementationRouteRank,
}

fn effective_implementation_route_precedes(
    candidate: &ImplementationAuthorization,
    candidate_rank: ImplementationRouteRank,
    existing: &ImplementationAuthorization,
    existing_rank: ImplementationRouteRank,
    span: crate::source::Span,
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<bool, ResolveError> {
    candidate
        .candidate_precedes(candidate_rank, existing, existing_rank, constraint_work)
        .map_err(|()| {
            error(
                ResolveReason::ConstraintResourceExhausted,
                span,
                "effective implementation route comparison exceeded its work budget",
            )
        })
}

fn public_implementation_route_precedes(
    candidate: &ImplementationAuthorization,
    candidate_rank: ImplementationRouteRank,
    existing: &ImplementationAuthorization,
    existing_rank: ImplementationRouteRank,
    span: crate::source::Span,
    constraint_work: &mut InterfaceConstraintBudget,
) -> Result<bool, ResolveError> {
    candidate
        .candidate_precedes(candidate_rank, existing, existing_rank, constraint_work)
        .map_err(|()| {
            error(
                ResolveReason::ConstraintResourceExhausted,
                span,
                "public implementation route comparison exceeded its work budget",
            )
        })
}

impl Resolver {
    fn resource_builtin(&self, kind: crate::surface::SurfaceResourceKind) -> Option<ModuleId> {
        match kind {
            crate::surface::SurfaceResourceKind::Cell => self.builtin_cell,
            crate::surface::SurfaceResourceKind::NativeBuffer => self.builtin_native_buffer,
        }
    }
    #[cfg(test)]
    fn new(module: ModuleId) -> Self {
        Self::with_budgets(
            module,
            TypeWorkBudget::default(),
            InterfaceConstraintBudget::default(),
        )
    }

    #[cfg(test)]
    fn with_type_work(module: ModuleId, type_work: TypeWorkBudget) -> Self {
        Self::with_budgets(module, type_work, InterfaceConstraintBudget::default())
    }

    fn with_budgets(
        module: ModuleId,
        type_work: TypeWorkBudget,
        constraint_work: InterfaceConstraintBudget,
    ) -> Self {
        Self {
            module,
            next_binder: 0,
            builtin_cell: None,
            builtin_native_buffer: None,
            next_type_variable: 0,
            next_lexical_nominal: 0,
            next_lexical_evidence: 0,
            resolved_interfaces: ResolvedInterfaceBuffer(Vec::new()),
            lexical_method_parameters: ImportedTypeVariableBuffer(Vec::new()),
            scopes: vec![HashMap::new()],
            globals: HashMap::new(),
            type_names: HashMap::new(),
            interface_names: HashMap::new(),
            effect_names: HashMap::new(),
            local_operation_names: HashMap::new(),
            method_names: HashMap::new(),
            global_requirement_counts: HashMap::new(),
            constructor_names: HashMap::new(),
            lexical_nominal_scopes: Vec::new(),
            lexical_constructor_scopes: Vec::new(),
            lexical_nominals: ResolvedNominalOwnerBuffer(Vec::new()),
            lexical_constructors: ResolvedConstructorOwnerBuffer(Vec::new()),
            lexical_nominal_parameters: ResolvedNominalParameterOwnerBuffer(Vec::new()),
            module_aliases: HashMap::new(),
            targeted_withheld: HashMap::new(),
            public_import_candidate: ResolvedExportCandidate::default(),
            imported: ImportedFacts::default(),
            implementation_route_ranks: HashMap::new(),
            public_implementation_route_ranks: HashMap::new(),
            type_scopes: Vec::new(),
            nominal_parameter_counts: HashMap::new(),
            active_resumes: Vec::new(),
            next_resume: 0,
            type_work,
            constraint_work,
            #[cfg(test)]
            max_type_pending_tasks: 0,
        }
    }

    fn validate_local_namespaces(&self, surface: &SurfaceModule) -> Result<(), ResolveError> {
        let mut type_names: HashMap<&str, (crate::source::Span, LocalTypeDeclarationKind)> =
            HashMap::new();
        let mut term_names: HashMap<&str, (crate::source::Span, Option<crate::source::Span>)> =
            HashMap::new();

        for declaration in &surface.declaration_order {
            match *declaration {
                SurfaceDeclarationIndex::Type(index) => {
                    let declaration = surface.type_declarations.get(index).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the surface declaration order contains an invalid type index",
                        )
                        .with_context(ResolveContext::DeclarationOrder {
                            kind: "nominal",
                            problem: "invalid-index",
                        })
                    })?;
                    self.validate_local_type_name(
                        &declaration.name,
                        LocalTypeDeclarationKind::Nominal,
                        &mut type_names,
                    )?;
                }
                SurfaceDeclarationIndex::Interface(index) => {
                    let declaration = surface.interfaces.get(index).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the surface declaration order contains an invalid interface index",
                        )
                        .with_context(ResolveContext::DeclarationOrder {
                            kind: "interface",
                            problem: "invalid-index",
                        })
                    })?;
                    self.validate_local_type_name(
                        &declaration.name,
                        LocalTypeDeclarationKind::Interface,
                        &mut type_names,
                    )?;
                    for method in &declaration.methods {
                        self.validate_local_term_name(&method.name, None, &mut term_names)?;
                    }
                }
                SurfaceDeclarationIndex::Effect(index) => {
                    let declaration = surface.effects.get(index).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the surface declaration order contains an invalid effect index",
                        )
                        .with_context(ResolveContext::DeclarationOrder {
                            kind: "effect",
                            problem: "invalid-index",
                        })
                    })?;
                    self.validate_local_type_name(
                        &declaration.name,
                        LocalTypeDeclarationKind::Effect,
                        &mut type_names,
                    )?;
                    let mut operations = HashMap::new();
                    for operation in &declaration.operations {
                        if let Some(first) =
                            operations.insert(&operation.name.text, operation.name.span)
                        {
                            let mut diagnostic = Diagnostic::new(
                                ResolveReason::DuplicateGlobal,
                                SourceLabel::new(
                                    operation.name.span,
                                    "this effect operation is already declared",
                                ),
                            );
                            diagnostic
                                .related
                                .push(SourceLabel::new(first, "the first operation is here"));
                            diagnostic.found = Some(operation.name.text.clone());
                            return Err(diagnostic.into());
                        }
                    }
                }
                SurfaceDeclarationIndex::Global(index) => {
                    let definition = surface.definitions.get(index).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the surface declaration order contains an invalid global index",
                        )
                        .with_context(ResolveContext::DeclarationOrder {
                            kind: "global",
                            problem: "invalid-index",
                        })
                    })?;
                    let name = surface_definition_name(definition);
                    self.validate_local_term_name(name, Some(definition.span), &mut term_names)?;
                }
                SurfaceDeclarationIndex::Implementation(index) => {
                    if surface.implementations.get(index).is_none() {
                        return Err(error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the surface declaration order contains an invalid impl index",
                        )
                        .with_context(ResolveContext::DeclarationOrder {
                            kind: "implementation",
                            problem: "invalid-index",
                        }));
                    }
                }
            }
        }
        Ok(())
    }

    fn validate_local_type_name<'a>(
        &self,
        name: &'a crate::surface::SurfaceName,
        kind: LocalTypeDeclarationKind,
        names: &mut HashMap<&'a str, (crate::source::Span, LocalTypeDeclarationKind)>,
    ) -> Result<(), ResolveError> {
        if self.module_aliases.contains_key(&name.text)
            || self.type_names.contains_key(&name.text)
            || self.interface_names.contains_key(&name.text)
            || self.effect_names.contains_key(&name.text)
        {
            return Err(import_conflict(name.span, &name.text));
        }
        if let Some((first, first_kind)) = names.insert(&name.text, (name.span, kind)) {
            if first_kind == LocalTypeDeclarationKind::Nominal
                && kind == LocalTypeDeclarationKind::Nominal
            {
                let mut diagnostic = Diagnostic::new(
                    ResolveReason::DuplicateType,
                    SourceLabel::new(name.span, "this nominal type name is already defined"),
                );
                diagnostic
                    .related
                    .push(SourceLabel::new(first, "the first nominal type is here"));
                diagnostic.found = Some(name.text.clone());
                return Err(diagnostic.into());
            }
            let mut diagnostic = Diagnostic::new(
                ResolveReason::DuplicateType,
                SourceLabel::new(name.span, "this type-namespace name is already declared"),
            );
            diagnostic
                .related
                .push(SourceLabel::new(first, "the first declaration is here"));
            diagnostic.found = Some(name.text.clone());
            return Err(diagnostic.into());
        }
        Ok(())
    }

    fn validate_local_term_name<'a>(
        &self,
        name: &'a crate::surface::SurfaceName,
        complete_definition: Option<crate::source::Span>,
        names: &mut HashMap<&'a str, (crate::source::Span, Option<crate::source::Span>)>,
    ) -> Result<(), ResolveError> {
        if self.module_aliases.contains_key(&name.text)
            || self.constructor_names.contains_key(&name.text)
            || self.method_names.contains_key(&name.text)
            || self
                .scopes
                .first()
                .is_some_and(|scope| scope.contains_key(&name.text))
        {
            return Err(import_conflict(name.span, &name.text));
        }
        if let Some((first, first_definition)) =
            names.insert(&name.text, (name.span, complete_definition))
        {
            if let (Some(first_definition), Some(_)) = (first_definition, complete_definition) {
                let mut diagnostic = Diagnostic::new(
                    ResolveReason::DuplicateGlobal,
                    SourceLabel::new(name.span, "this global name is already defined"),
                );
                diagnostic
                    .related
                    .push(SourceLabel::new(first, "the first global name is here"));
                diagnostic.related.push(SourceLabel::new(
                    first_definition,
                    "the first complete definition is here",
                ));
                diagnostic.found = Some(name.text.clone());
                return Err(diagnostic.into());
            }
            let mut diagnostic = Diagnostic::new(
                ResolveReason::DuplicateGlobal,
                SourceLabel::new(name.span, "this term name is already declared"),
            );
            diagnostic
                .related
                .push(SourceLabel::new(first, "the first term name is here"));
            if let Some(first_definition) = first_definition {
                diagnostic.related.push(SourceLabel::new(
                    first_definition,
                    "the first complete definition is here",
                ));
            }
            diagnostic.found = Some(name.text.clone());
            return Err(diagnostic.into());
        }
        Ok(())
    }

    fn install_interface_identities(
        &mut self,
        declarations: &[SurfaceInterfaceDeclaration],
    ) -> Result<Vec<InterfaceDeclarationIdentity>, ResolveError> {
        let mut identities = Vec::with_capacity(declarations.len());
        for (index, declaration) in declarations.iter().enumerate() {
            let index = u32::try_from(index).map_err(|_| {
                error(
                    ResolveReason::InternalState,
                    declaration.span,
                    "the file contains too many interface declarations",
                )
                .with_context(ResolveContext::IdentityExhaustion(
                    ResolveIdentitySpace::Interface,
                ))
            })?;
            let id = InterfaceId::new(self.module, index);
            self.interface_names
                .insert(declaration.name.text.clone(), id);
            let mut methods = Vec::with_capacity(declaration.methods.len());
            for (method_index, method) in declaration.methods.iter().enumerate() {
                let method_index = u32::try_from(method_index).map_err(|_| {
                    error(
                        ResolveReason::InternalState,
                        method.span,
                        "the interface contains too many method declarations",
                    )
                    .with_context(ResolveContext::IdentityExhaustion(
                        ResolveIdentitySpace::Method,
                    ))
                })?;
                let method_id = MethodId::new(id, method_index);
                self.method_names.insert(
                    method.name.text.clone(),
                    ResolvedTermBinding::local(ResolvedTermName::Method(method_id)),
                );
                methods.push(method_id);
            }
            identities.push(InterfaceDeclarationIdentity { id, methods });
        }
        Ok(identities)
    }

    fn install_effect_identities(
        &mut self,
        declarations: &[SurfaceEffectDeclaration],
    ) -> Result<Vec<EffectDeclarationIdentity>, ResolveError> {
        let mut identities = Vec::new();
        identities
            .try_reserve_exact(declarations.len())
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    declarations
                        .last()
                        .expect("nonempty effect storage can fail to reserve")
                        .span,
                    "effect identity storage could not be reserved",
                )
            })?;
        for (declaration_index, declaration) in declarations.iter().enumerate() {
            let declaration_index = u32::try_from(declaration_index).map_err(|_| {
                error(
                    ResolveReason::InternalState,
                    declaration.span,
                    "the file contains too many effect declarations",
                )
                .with_context(ResolveContext::IdentityExhaustion(
                    ResolveIdentitySpace::Effect,
                ))
            })?;
            let id = EffectId::new(self.module, declaration_index);
            self.effect_names.insert(declaration.name.text.clone(), id);
            self.type_work
                .charge(declaration.operations.len().checked_add(1).ok_or_else(|| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        declaration.span,
                        "effect operation-name retention exceeded its type-work budget",
                    )
                })?)
                .map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        declaration.span,
                        "effect operation-name retention exceeded its type-work budget",
                    )
                })?;
            self.local_operation_names.try_reserve(1).map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    declaration.span,
                    "effect operation-name storage could not be reserved",
                )
            })?;
            let mut operation_names = HashMap::new();
            operation_names
                .try_reserve(declaration.operations.len())
                .map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        declaration.span,
                        "effect operation-name storage could not be reserved",
                    )
                })?;
            let mut operations = Vec::new();
            operations
                .try_reserve_exact(declaration.operations.len())
                .map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        declaration.span,
                        "effect operation identity storage could not be reserved",
                    )
                })?;
            for (operation_index, operation) in declaration.operations.iter().enumerate() {
                let operation_index = u32::try_from(operation_index).map_err(|_| {
                    error(
                        ResolveReason::InternalState,
                        operation.span,
                        "the effect contains too many operations",
                    )
                    .with_context(ResolveContext::IdentityExhaustion(
                        ResolveIdentitySpace::Operation,
                    ))
                })?;
                let operation_id = OperationId::new(id, operation_index);
                let operation_name = try_clone_resolution_string(
                    &operation.name.text,
                    operation.name.span,
                    "effect operation name could not be retained",
                )?;
                operation_names.insert(operation_name, operation_id);
                operations.push(operation_id);
            }
            self.local_operation_names.insert(id, operation_names);
            identities.push(EffectDeclarationIdentity { id, operations });
        }
        Ok(identities)
    }

    fn allocate_effect_type_parameters(
        &mut self,
        declaration: &SurfaceEffectDeclaration,
    ) -> Result<Vec<ResolvedTypeVariable>, ResolveError> {
        validate_explicit_type_parameters(Some(&declaration.parameters))?;
        let mut parameters = Vec::new();
        parameters
            .try_reserve_exact(declaration.parameters.len())
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    declaration.span,
                    "effect parameter storage could not be reserved",
                )
            })?;
        for parameter in &declaration.parameters {
            let resolved =
                self.allocate_type_variable(&parameter.name, parameter.kind.as_ref(), Kind::Type)?;
            parameters.push(resolved);
        }
        Ok(parameters)
    }

    fn resolve_effect_declarations(
        &mut self,
        declarations: &[SurfaceEffectDeclaration],
        identities: Vec<EffectDeclarationIdentity>,
        parameters: Vec<Vec<ResolvedTypeVariable>>,
        module_span: crate::source::Span,
    ) -> Result<(Vec<ResolvedEffectDeclaration>, Vec<ResolvedTypeVariable>), ResolveError> {
        if declarations.len() != identities.len() || declarations.len() != parameters.len() {
            return Err(error(
                ResolveReason::InternalState,
                module_span,
                "the resolver retained mismatched effect preparation records",
            ));
        }
        let mut resolved_effects = Vec::new();
        let mut registry_parameters = Vec::new();
        resolved_effects
            .try_reserve_exact(declarations.len())
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    module_span,
                    "effect storage could not be reserved",
                )
            })?;
        for ((declaration, identity), parameters) in
            declarations.iter().zip(identities).zip(parameters)
        {
            if declaration.operations.len() != identity.operations.len() {
                return Err(error(
                    ResolveReason::InternalState,
                    declaration.span,
                    "the resolver retained mismatched operation identities",
                ));
            }
            for parameter in &parameters {
                registry_parameters.push(self.clone_type_variable_for_retention(
                    parameter,
                    declaration.span,
                    "effect parameter registry retention exceeded its type-work budget",
                )?);
            }
            let checkpoint = self.type_scopes.len();
            self.type_scopes.push(
                parameters
                    .iter()
                    .map(|parameter| (parameter.spelling.clone(), parameter.id))
                    .collect(),
            );
            let operations = (|| {
                let mut resolved = Vec::new();
                resolved
                    .try_reserve_exact(declaration.operations.len())
                    .map_err(|_| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            declaration.span,
                            "effect operation storage could not be reserved",
                        )
                    })?;
                for (operation, id) in declaration.operations.iter().zip(identity.operations) {
                    if !matches!(
                        &operation.annotation.kind,
                        SurfaceTypeKind::Function(function) if function.effects.is_none()
                    ) {
                        return Err(error(
                            ResolveReason::EffectOperationShape,
                            operation.annotation.span,
                            "an effect operation must have one outer function arrow with a pure result",
                        ));
                    }
                    let annotation = self.resolve_type(&operation.annotation)?;
                    let shape = annotation.ty.function_view();
                    if shape.is_none_or(|view| view.effects().is_some()) {
                        return Err(error(
                            ResolveReason::EffectOperationShape,
                            operation.annotation.span,
                            "an effect operation must have one outer function arrow with a pure result",
                        ));
                    }
                    resolved.push(ResolvedEffectOperation {
                        id,
                        spelling: operation.name.text.clone(),
                        annotation,
                        origin: Origin::Source(operation.name.span),
                        span: operation.span,
                    });
                }
                Ok::<_, ResolveError>(resolved)
            })();
            self.type_scopes.truncate(checkpoint);
            resolved_effects.push(ResolvedEffectDeclaration {
                id: identity.id,
                public: declaration.public,
                spelling: declaration.name.text.clone(),
                parameters: parameters.into_boxed_slice(),
                operations: operations?.into_boxed_slice(),
                origin: Origin::Source(declaration.name.span),
                span: declaration.span,
            });
        }
        Ok((resolved_effects, registry_parameters))
    }

    fn prepare_interface_type_parameters(
        &mut self,
        declaration: &SurfaceInterfaceDeclaration,
    ) -> Result<PendingInterfaceTypeParameters, ResolveError> {
        if declaration.parameters.is_empty() {
            return Err(error(
                ResolveReason::InternalState,
                declaration.span,
                "the projected interface parameter vector is empty",
            ));
        }
        validate_interface_type_parameters(
            &declaration.parameters,
            declaration.span,
            &mut self.type_work,
        )?;
        let mut parameters = Vec::new();
        parameters
            .try_reserve_exact(declaration.parameters.len())
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    declaration.span,
                    "interface type-parameter storage could not be reserved",
                )
            })?;
        for parameter in &declaration.parameters {
            parameters.push(self.allocate_type_variable(
                &parameter.name,
                parameter.kind.as_ref(),
                Kind::Type,
            )?);
        }
        let first_parameter = declaration.parameters.first().ok_or_else(|| {
            error(
                ResolveReason::InternalState,
                declaration.span,
                "the projected interface parameter vector is empty",
            )
        })?;
        let mut methods = Vec::new();
        methods
            .try_reserve_exact(declaration.methods.len())
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    declaration.span,
                    "interface type-parameter preparation storage could not be reserved",
                )
            })?;
        for method in &declaration.methods {
            let explicit = method.type_parameters.as_deref();
            let mut names = Vec::new();
            let mut seen = HashMap::new();
            self.type_work
                .charge(declaration.parameters.len())
                .map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        method.span,
                        "method free-name owner installation exceeded its type-work budget",
                    )
                })?;
            seen.try_reserve(declaration.parameters.len())
                .map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        first_parameter.name.span,
                        "method free-name storage could not reserve interface parameters",
                    )
                })?;
            for parameter in &declaration.parameters {
                seen.insert(parameter.name.text.as_str(), None);
            }
            let declared = validate_method_type_parameters(
                &declaration.parameters,
                explicit,
                declaration.span,
                &mut self.type_work,
            )?;
            collect_free_type_names(
                &method.annotation,
                &self.type_names,
                &self.interface_names,
                &declared,
                &mut seen,
                &mut names,
                false,
                &mut self.type_work,
            )?;
            let type_parameters =
                self.allocate_declaration_type_parameters(explicit, &names, false)?;
            methods.push(type_parameters);
        }
        Ok(PendingInterfaceTypeParameters {
            parameters,
            methods,
        })
    }

    fn resolve_interface_declarations(
        &mut self,
        declarations: &[SurfaceInterfaceDeclaration],
        identities: Vec<InterfaceDeclarationIdentity>,
        parameters: Vec<PendingInterfaceTypeParameters>,
        module_span: crate::source::Span,
    ) -> Result<(Vec<ResolvedInterfaceDeclaration>, Vec<ResolvedTypeVariable>), ResolveError> {
        if declarations.len() != identities.len() || declarations.len() != parameters.len() {
            return Err(error(
                ResolveReason::InternalState,
                declarations
                    .last()
                    .map_or(module_span, |declaration| declaration.span),
                "the resolver retained mismatched interface preparation records",
            ));
        }

        let mut resolved = ResolvedInterfaceBuffer(Vec::with_capacity(declarations.len()));
        let mut retained_type_variables = Vec::new();
        for ((declaration, identity), pending) in
            declarations.iter().zip(identities).zip(parameters)
        {
            if declaration.methods.len() != identity.methods.len()
                || declaration.methods.len() != pending.methods.len()
            {
                return Err(error(
                    ResolveReason::InternalState,
                    declaration.span,
                    "the resolver retained mismatched interface method preparation records",
                ));
            }
            retained_type_variables
                .try_reserve(pending.parameters.len())
                .map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        declaration.span,
                        "interface parameter registry storage could not be reserved",
                    )
                })?;
            for (parameter, source_parameter) in
                pending.parameters.iter().zip(declaration.parameters.iter())
            {
                retained_type_variables.push(self.clone_type_variable_for_retention(
                    parameter,
                    source_parameter.name.span,
                    "interface parameter retention exceeded its type-work budget",
                )?);
            }
            let mut methods =
                ResolvedInterfaceMethodBuffer(Vec::with_capacity(declaration.methods.len()));
            for ((method, method_id), type_parameters) in declaration
                .methods
                .iter()
                .zip(identity.methods)
                .zip(pending.methods)
            {
                retained_type_variables
                    .try_reserve(type_parameters.len())
                    .map_err(|_| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            method.span,
                            "interface method parameter registry storage could not be reserved",
                        )
                    })?;
                for type_parameter in &type_parameters {
                    retained_type_variables.push(self.clone_type_variable_for_retention(
                        type_parameter,
                        method.span,
                        "interface method parameter retention exceeded its type-work budget",
                    )?);
                }
                let scope_width = pending
                    .parameters
                    .len()
                    .checked_add(type_parameters.len())
                    .ok_or_else(|| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            method.span,
                            "interface method type scope size is not representable",
                        )
                    })?;
                self.type_work.charge(scope_width).map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        method.span,
                        "interface method type-scope retention exceeded its type-work budget",
                    )
                })?;
                let mut scope = HashMap::new();
                scope.try_reserve(scope_width).map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        method.span,
                        "interface method type-scope storage could not be reserved",
                    )
                })?;
                for parameter in pending.parameters.iter().chain(&type_parameters) {
                    let spelling = try_clone_resolution_string(
                        &parameter.spelling,
                        method.span,
                        "interface method type-scope spelling could not be retained",
                    )?;
                    if scope.insert(spelling, parameter.id).is_some() {
                        return Err(error(
                            ResolveReason::InternalState,
                            method.span,
                            "an interface method type scope repeats a prepared binder",
                        ));
                    }
                }
                self.type_scopes.try_reserve(1).map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        method.span,
                        "interface method type-scope stack could not be reserved",
                    )
                })?;
                self.type_scopes.push(scope);
                let annotation = self.resolve_type(&method.annotation);
                let _ = self.type_scopes.pop();
                methods.0.push(ResolvedInterfaceMethod {
                    id: method_id,
                    spelling: method.name.text.clone(),
                    annotation: annotation?,
                    type_parameters: type_parameters.into_boxed_slice(),
                    has_explicit_type_parameters: method.type_parameters.is_some(),
                    origin: Origin::Source(method.span),
                    span: method.span,
                });
            }
            let determination = declaration
                .determination
                .as_ref()
                .map(|determination| {
                    self.resolve_interface_determination(determination, &pending.parameters)
                })
                .transpose()?;
            resolved.0.push(ResolvedInterfaceDeclaration {
                id: identity.id,
                public: declaration.public,
                spelling: declaration.name.text.clone(),
                parameters: pending.parameters.into_boxed_slice(),
                determination,
                methods: methods.into_vec().into_boxed_slice(),
                origin: Origin::Source(declaration.span),
                span: declaration.span,
            });
        }
        Ok((resolved.into_vec(), retained_type_variables))
    }

    fn prepare_implementation(
        &mut self,
        index: usize,
        implementation: &SurfaceImplementation,
    ) -> Result<PendingImplementation, ResolveError> {
        let index = u32::try_from(index).map_err(|_| {
            error(
                ResolveReason::InternalState,
                implementation.span,
                "the file contains too many implementation declarations",
            )
            .with_context(ResolveContext::IdentityExhaustion(
                ResolveIdentitySpace::Implementation,
            ))
        })?;
        let id = ImplId::new(self.module, index);

        let declared =
            validate_explicit_type_parameters(implementation.type_parameters.as_deref())?;
        let mut seen = HashMap::new();
        let mut head_names = Vec::new();
        if implementation.head.arguments.is_empty() {
            return Err(error(
                ResolveReason::InternalState,
                implementation.head.span,
                "the projected implementation head argument vector is empty",
            ));
        }
        for head_argument in &implementation.head.arguments {
            collect_free_type_names(
                head_argument,
                &self.type_names,
                &self.interface_names,
                &declared,
                &mut seen,
                &mut head_names,
                false,
                &mut self.type_work,
            )?;
        }
        let head_parameters = self.allocate_declaration_type_parameters(
            implementation.type_parameters.as_deref(),
            &head_names,
            false,
        )?;

        let mut prerequisite_only_names = Vec::new();
        for prerequisite in &implementation.prerequisites {
            for argument in &prerequisite.arguments {
                collect_free_type_names(
                    argument,
                    &self.type_names,
                    &self.interface_names,
                    &declared,
                    &mut seen,
                    &mut prerequisite_only_names,
                    false,
                    &mut self.type_work,
                )?;
            }
        }
        let prerequisite_only_parameters = prerequisite_only_names
            .into_iter()
            .map(|free| self.allocate_type_variable(&free.name, None, Kind::Type))
            .collect::<Result<Vec<_>, _>>()?;

        let mut method_groups = Vec::new();
        let mut start = 0;
        while let Some(first) = implementation.equations.get(start) {
            let mut end = start + 1;
            while implementation
                .equations
                .get(end)
                .is_some_and(|equation| equation.name.text == first.name.text)
            {
                end += 1;
            }
            method_groups.push(PendingImplementationMethodGroup {
                equations: start..end,
                binder: None,
            });
            start = end;
        }

        Ok(PendingImplementation {
            id,
            head_parameters,
            prerequisite_only_parameters,
            method_groups,
        })
    }

    fn install_imports(
        &mut self,
        surface: &SurfaceModule,
        dependencies: &[DependencyExports<'_>],
    ) -> Result<(), ResolveError> {
        for (dependency_summary_order, (import, dependency)) in
            surface.imports.iter().zip(dependencies).enumerate()
        {
            let mut retained_constructor_owners = HashSet::new();
            let mut capture_graph_visits = CaptureGraphVisits::default();
            self.retain_dependency_interface_facts(
                dependency.summary,
                dependency.edge.target(),
                import.span,
            )?;
            match &import.selection {
                SurfaceImportSelection::Qualified { alias } => {
                    if self.file_name_is_bound(&alias.text) {
                        return Err(import_conflict(alias.span, &alias.text));
                    }
                    let namespaces = self.clone_summary_namespaces(
                        dependency.summary,
                        import.span,
                        &mut capture_graph_visits,
                    )?;
                    self.module_aliases.insert(alias.text.clone(), namespaces);
                }
                SurfaceImportSelection::Targeted(items) => {
                    for (selector_source_order, item) in items.iter().enumerate() {
                        if let SurfaceImportItem::Implementation { interface, span } = item {
                            let route_rank = ImplementationRouteRank::new(
                                dependency_summary_order,
                                dependency_summary_order,
                                selector_source_order,
                            );
                            self.select_imported_implementations(
                                dependency.summary,
                                interface,
                                ImplementationImportSelection {
                                    direct_dependency: dependency.edge.target(),
                                    selector_span: *span,
                                    import_span: import.span,
                                    public: import.public,
                                    route_rank,
                                },
                                &mut capture_graph_visits,
                            )?;
                            continue;
                        }
                        let SurfaceImportItem::Name { name, alias, span } = item else {
                            continue;
                        };
                        let local = alias.as_ref().unwrap_or(name);
                        if self.module_aliases.contains_key(&local.text) {
                            return Err(import_conflict(local.span, &local.text));
                        }
                        let mut selected = false;
                        if let Some(exported) = dependency.summary.term(&name.text) {
                            selected = true;
                            if self.constructor_names.contains_key(&local.text)
                                || self.method_names.contains_key(&local.text)
                            {
                                return Err(import_conflict(local.span, &local.text));
                            }
                            let scope = self.scopes.first_mut().ok_or_else(|| {
                                error(
                                    ResolveReason::InternalState,
                                    *span,
                                    "the resolver lost the file scope",
                                )
                                .with_context(ResolveContext::MissingFileScope)
                            })?;
                            if scope.contains_key(&local.text) {
                                return Err(import_conflict(local.span, &local.text));
                            }
                            scope.insert(
                                local.text.clone(),
                                ResolvedTermBinding::imported(
                                    ResolvedTermName::Global(exported.binder),
                                    *span,
                                ),
                            );
                            self.retain_imported_global(
                                exported,
                                dependency.summary,
                                *span,
                                &mut capture_graph_visits,
                            )?;
                            if import.public {
                                self.public_import_candidate.try_insert_term(
                                    local.text.clone(),
                                    CandidateGlobal {
                                        binder: exported.binder,
                                        source: CandidateFactSource::Imported,
                                        origin: exported.origin.clone(),
                                    },
                                    &mut self.type_work,
                                ).map_err(|()| export_candidate_resource_error(
                                    *span,
                                    "public import candidate retention exceeded its type-work budget",
                                ))?;
                            }
                        }
                        if let Some(method) = dependency.summary.method(&name.text) {
                            selected = true;
                            if self.constructor_names.contains_key(&local.text)
                                || self.method_names.contains_key(&local.text)
                                || self
                                    .scopes
                                    .first()
                                    .is_some_and(|scope| scope.contains_key(&local.text))
                            {
                                return Err(import_conflict(local.span, &local.text));
                            }
                            self.method_names.insert(
                                local.text.clone(),
                                ResolvedTermBinding::imported(
                                    ResolvedTermName::Method(method),
                                    *span,
                                ),
                            );
                            if import.public {
                                self.public_import_candidate.try_insert_method(
                                    local.text.clone(),
                                    CandidateMethod {
                                        id: method,
                                        source: CandidateFactSource::Imported,
                                    },
                                    &mut self.type_work,
                                ).map_err(|()| export_candidate_resource_error(
                                    *span,
                                    "public import candidate retention exceeded its type-work budget",
                                ))?;
                            }
                        }
                        if let Some(exported) = dependency.summary.nominal(&name.text) {
                            selected = true;
                            if self.type_names.contains_key(&local.text)
                                || self.interface_names.contains_key(&local.text)
                                || self.effect_names.contains_key(&local.text)
                            {
                                return Err(import_conflict(local.span, &local.text));
                            }
                            self.type_names.insert(local.text.clone(), exported.id);
                            self.nominal_parameter_counts
                                .insert(exported.id, exported.parameter_count);
                            self.retain_imported_nominal(
                                exported,
                                dependency.summary,
                                Some(&name.text),
                                *span,
                                &mut retained_constructor_owners,
                            )?;
                            if import.public {
                                self.public_import_candidate.try_insert_nominal(
                                    local.text.clone(),
                                    CandidateNominal {
                                        id: exported.id,
                                        access: exported.access,
                                        source: CandidateFactSource::Imported,
                                        origin: exported.origin.clone(),
                                    },
                                    &mut self.type_work,
                                ).map_err(|()| export_candidate_resource_error(
                                    *span,
                                    "public import candidate retention exceeded its type-work budget",
                                ))?;
                                if exported.access == ExportedTypeAccess::Opaque {
                                    self.type_work
                                        .charge(dependency.summary.withheld_count())
                                        .map_err(|()| {
                                            export_candidate_resource_error(
                                                *span,
                                                "opaque constructor-family scan exceeded its type-work budget",
                                            )
                                        })?;
                                    for (spelling, withheld) in
                                        dependency.summary.opaque_constructors(exported.id)
                                    {
                                        let spelling = if spelling == name.text {
                                            local.text.clone()
                                        } else {
                                            spelling.to_owned()
                                        };
                                        self.public_import_candidate.try_insert_withheld(
                                            WithheldNamespace::Constructor,
                                            spelling,
                                            withheld.clone(),
                                            &mut self.type_work,
                                        ).map_err(|()| export_candidate_resource_error(
                                            *span,
                                            "public import candidate retention exceeded its type-work budget",
                                        ))?;
                                    }
                                }
                            }
                        }
                        if let Some(exported) = dependency.summary.interface(&name.text) {
                            selected = true;
                            if self.type_names.contains_key(&local.text)
                                || self.interface_names.contains_key(&local.text)
                                || self.effect_names.contains_key(&local.text)
                            {
                                return Err(import_conflict(local.span, &local.text));
                            }
                            self.interface_names.insert(local.text.clone(), exported.id);
                            if import.public {
                                self.public_import_candidate.try_insert_interface(
                                    local.text.clone(),
                                    CandidateInterface {
                                        id: exported.id,
                                        source: CandidateFactSource::Imported,
                                    },
                                    &mut self.type_work,
                                ).map_err(|()| export_candidate_resource_error(
                                    *span,
                                    "public import candidate retention exceeded its type-work budget",
                                ))?;
                            }
                        }
                        if let Some(effect) = dependency.summary.effect(&name.text) {
                            selected = true;
                            if self.type_names.contains_key(&local.text)
                                || self.interface_names.contains_key(&local.text)
                                || self.effect_names.contains_key(&local.text)
                            {
                                return Err(import_conflict(local.span, &local.text));
                            }
                            self.effect_names.insert(local.text.clone(), effect.id);
                            self.retain_imported_effect(effect, *span)?;
                            if import.public {
                                self.public_import_candidate
                                    .try_insert_effect(
                                        local.text.clone(),
                                        CandidateEffect {
                                            id: effect.id,
                                            source: CandidateFactSource::Imported,
                                        },
                                        &mut self.type_work,
                                    )
                                    .map_err(|()| {
                                        export_candidate_resource_error(
                                            *span,
                                            "public import candidate retention exceeded its type-work budget",
                                        )
                                    })?;
                            }
                        }
                        if let Some(exported) = dependency.summary.constructor(&name.text) {
                            selected = true;
                            if self.constructor_names.contains_key(&local.text)
                                || self.method_names.contains_key(&local.text)
                                || self
                                    .scopes
                                    .first()
                                    .is_some_and(|scope| scope.contains_key(&local.text))
                            {
                                return Err(import_conflict(local.span, &local.text));
                            }
                            self.constructor_names
                                .insert(local.text.clone(), exported.id);
                            self.retain_imported_constructor_once_per_route(
                                exported,
                                dependency.summary,
                                *span,
                                &mut retained_constructor_owners,
                            )?;
                            if import.public {
                                self.public_import_candidate.try_insert_constructor(
                                    local.text.clone(),
                                    CandidateConstructor {
                                        id: exported.id,
                                        source: CandidateFactSource::Imported,
                                        origin: exported.origin.clone(),
                                    },
                                    &mut self.type_work,
                                ).map_err(|()| export_candidate_resource_error(
                                    *span,
                                    "public import candidate retention exceeded its type-work budget",
                                ))?;
                            }
                        }
                        if !selected {
                            let withheld = [
                                WithheldNamespace::Term,
                                WithheldNamespace::Nominal,
                                WithheldNamespace::Constructor,
                            ]
                            .into_iter()
                            .filter_map(|namespace| {
                                dependency.summary.withheld_export(namespace, &name.text)
                            })
                            .map(|withheld| WithheldImport {
                                kind: withheld.kind,
                                declaration: withheld
                                    .origin
                                    .as_ref()
                                    .map(crate::source::Origin::primary_span),
                            })
                            .min_by_key(|withheld| {
                                match withheld.kind {
                                    WithheldExportKind::Private => 0,
                                    WithheldExportKind::OpaqueConstructor => 1,
                                }
                            });
                            return Err(withheld_export_error(name.span, &name.text, withheld));
                        }
                        for namespace in [
                            WithheldNamespace::Term,
                            WithheldNamespace::Nominal,
                            WithheldNamespace::Constructor,
                        ] {
                            let Some(withheld) =
                                dependency.summary.withheld_export(namespace, &name.text)
                            else {
                                continue;
                            };
                            self.targeted_withheld.insert(
                                (local.text.clone(), namespace),
                                WithheldImport {
                                    kind: withheld.kind,
                                    declaration: withheld
                                        .origin
                                        .as_ref()
                                        .map(crate::source::Origin::primary_span),
                                },
                            );
                            if import.public {
                                self.public_import_candidate.try_insert_withheld(
                                    namespace,
                                    local.text.clone(),
                                    WithheldExport {
                                        kind: withheld.kind,
                                        owner: withheld.owner,
                                        origin: withheld.origin.clone(),
                                    },
                                    &mut self.type_work,
                                ).map_err(|()| export_candidate_resource_error(
                                    *span,
                                    "public import candidate retention exceeded its type-work budget",
                                ))?;
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn select_imported_implementations<'a>(
        &mut self,
        summary: &'a ExportSummary,
        interface: &crate::surface::SurfaceName,
        selection: ImplementationImportSelection,
        capture_graph_visits: &mut CaptureGraphVisits<'a>,
    ) -> Result<(), ResolveError> {
        self.constraint_work.charge(1).map_err(|()| {
            error(
                ResolveReason::ConstraintResourceExhausted,
                selection.selector_span,
                "implementation selector processing exceeded its work budget",
            )
        })?;
        self.charge_implementation_selector_summary_probe(selection.selector_span)?;
        let selected_interface = match summary.interface(&interface.text) {
            Some(exported) => exported.id,
            None => {
                self.charge_implementation_selector_summary_probe(selection.selector_span)?;
                if summary.nominal(&interface.text).is_some() {
                    return Err(interface_kind_error(interface.span, &interface.text));
                }
                self.charge_implementation_selector_summary_probe(selection.selector_span)?;
                if summary.constructor(&interface.text).is_some() {
                    return Err(interface_kind_error(interface.span, &interface.text));
                }
                self.charge_implementation_selector_summary_probe(selection.selector_span)?;
                if summary.term(&interface.text).is_some() {
                    return Err(interface_kind_error(interface.span, &interface.text));
                }
                self.charge_implementation_selector_summary_probe(selection.selector_span)?;
                if summary.method(&interface.text).is_some() {
                    return Err(interface_kind_error(interface.span, &interface.text));
                }
                self.charge_implementation_selector_summary_probe(selection.selector_span)?;
                let withheld = summary
                    .withheld_export(WithheldNamespace::Nominal, &interface.text)
                    .map(|withheld| WithheldImport {
                        kind: withheld.kind,
                        declaration: withheld
                            .origin
                            .as_ref()
                            .map(crate::source::Origin::primary_span),
                    });
                return Err(withheld_export_error(
                    interface.span,
                    &interface.text,
                    withheld,
                ));
            }
        };

        for implementation in summary.implementations() {
            self.constraint_work.charge(1).map_err(|()| {
                error(
                    ResolveReason::ConstraintResourceExhausted,
                    selection.selector_span,
                    "implementation selector summary inspection exceeded its work budget",
                )
            })?;
            if implementation.fact().interface() == selected_interface {
                self.retain_imported_implementation_fact(
                    implementation,
                    summary,
                    selection,
                    capture_graph_visits,
                )?;
            }
        }
        Ok(())
    }

    fn charge_implementation_selector_summary_probe(
        &mut self,
        span: crate::source::Span,
    ) -> Result<(), ResolveError> {
        self.constraint_work.charge(1).map_err(|()| {
            error(
                ResolveReason::ConstraintResourceExhausted,
                span,
                "implementation selector summary lookup exceeded its work budget",
            )
        })
    }

    fn clone_summary_namespaces<'a>(
        &mut self,
        summary: &'a ExportSummary,
        import_span: crate::source::Span,
        capture_graph_visits: &mut CaptureGraphVisits<'a>,
    ) -> Result<ImportedNamespaces, ResolveError> {
        let mut namespaces = ImportedNamespaces::default();
        let mut retained_constructor_owners = HashSet::new();
        let entry_count = summary.namespace_entry_count().ok_or_else(|| {
            error(
                ResolveReason::TypeResourceExhausted,
                import_span,
                "imported namespace retention exceeded its work budget",
            )
        })?;
        self.type_work.charge(entry_count).map_err(|()| {
            error(
                ResolveReason::TypeResourceExhausted,
                import_span,
                "imported namespace retention exceeded its work budget",
            )
        })?;
        let (
            term_count,
            nominal_count,
            interface_count,
            effect_count,
            constructor_count,
            withheld_count,
        ) = summary.namespace_capacities().ok_or_else(|| {
            error(
                ResolveReason::TypeResourceExhausted,
                import_span,
                "imported namespace capacity exceeded its work budget",
            )
        })?;
        namespaces.terms.try_reserve(term_count).map_err(|_| {
            error(
                ResolveReason::TypeResourceExhausted,
                import_span,
                "imported term namespace storage exceeded its work budget",
            )
        })?;
        namespaces
            .nominals
            .try_reserve(nominal_count)
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    import_span,
                    "imported nominal namespace storage exceeded its work budget",
                )
            })?;
        namespaces
            .interfaces
            .try_reserve(interface_count)
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    import_span,
                    "imported interface namespace storage exceeded its work budget",
                )
            })?;
        namespaces.effects.try_reserve(effect_count).map_err(|_| {
            error(
                ResolveReason::TypeResourceExhausted,
                import_span,
                "imported effect namespace storage exceeded its work budget",
            )
        })?;
        namespaces
            .constructors
            .try_reserve(constructor_count)
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    import_span,
                    "imported constructor namespace storage exceeded its work budget",
                )
            })?;
        namespaces
            .withheld
            .try_reserve(withheld_count)
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    import_span,
                    "imported withheld namespace storage exceeded its work budget",
                )
            })?;

        for (spelling, exported) in summary.terms() {
            namespaces.terms.insert(
                spelling.to_owned(),
                ResolvedTermBinding::imported(
                    ResolvedTermName::Global(exported.binder),
                    import_span,
                ),
            );
            self.retain_imported_global(exported, summary, import_span, capture_graph_visits)?;
        }

        for (spelling, method) in summary.method_names() {
            if namespaces
                .terms
                .insert(
                    spelling.to_owned(),
                    ResolvedTermBinding::imported(ResolvedTermName::Method(method), import_span),
                )
                .is_some()
            {
                return Err(error(
                    ResolveReason::InternalState,
                    import_span,
                    "an export summary contains duplicate term spellings",
                ));
            }
        }

        for (spelling, exported) in summary.nominals() {
            namespaces
                .nominals
                .insert(spelling.to_owned(), ImportedNominalName { id: exported.id });
            self.retain_imported_nominal(
                exported,
                summary,
                Some(spelling),
                import_span,
                &mut retained_constructor_owners,
            )?;
        }

        for (spelling, interface) in summary.interface_names() {
            if namespaces
                .interfaces
                .insert(spelling.to_owned(), interface)
                .is_some()
            {
                return Err(error(
                    ResolveReason::InternalState,
                    import_span,
                    "an export summary contains duplicate interface spellings",
                ));
            }
        }

        for (spelling, effect) in summary.effect_names() {
            if namespaces
                .effects
                .insert(spelling.to_owned(), effect)
                .is_some()
            {
                return Err(error(
                    ResolveReason::InternalState,
                    import_span,
                    "an export summary contains duplicate effect spellings",
                ));
            }
            let fact = summary.effect(spelling).ok_or_else(|| {
                error(
                    ResolveReason::InternalState,
                    import_span,
                    "an export summary lost an effect fact",
                )
            })?;
            self.retain_imported_effect(fact, import_span)?;
        }

        for (spelling, exported) in summary.constructors() {
            namespaces
                .constructors
                .insert(spelling.to_owned(), exported.id);
            self.retain_imported_constructor_once_per_route(
                exported,
                summary,
                import_span,
                &mut retained_constructor_owners,
            )?;
        }
        for (namespace, spelling, withheld) in summary.withheld() {
            namespaces
                .withheld
                .entry((spelling.to_owned(), namespace))
                .or_insert_with(|| WithheldImport {
                    kind: withheld.kind,
                    declaration: withheld
                        .origin
                        .as_ref()
                        .map(crate::source::Origin::primary_span),
                });
        }
        Ok(namespaces)
    }

    fn retain_imported_effect(
        &mut self,
        exported: &ResolvedEffectDeclaration,
        span: crate::source::Span,
    ) -> Result<(), ResolveError> {
        let retained =
            clone_resolved_effect_with_budget(exported, &mut self.type_work).map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    span,
                    "imported effect retention exceeded its type-work budget",
                )
            })?;
        if let Some(existing) = self.imported.effect(exported.id) {
            let matches = existing == &retained;
            discard_resolved_effect_iteratively(retained);
            if !matches {
                return Err(error(
                    ResolveReason::InternalState,
                    span,
                    "alternate effect routes disagree on the canonical fact",
                ));
            }
            return Ok(());
        }
        self.imported
            .insert_effect(retained, &mut self.type_work)
            .map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    span,
                    "imported effect storage exceeded its type-work budget",
                )
            })
    }

    fn retain_dependency_interface_facts(
        &mut self,
        summary: &ExportSummary,
        direct_dependency: ModuleId,
        import_span: crate::source::Span,
    ) -> Result<(), ResolveError> {
        for interface in summary.interfaces() {
            self.retain_imported_interface_fact(
                interface,
                summary,
                ImportedInterfaceAccess::PublicExport,
                direct_dependency,
                import_span,
            )?;
        }
        for interface in summary.hidden_interfaces() {
            self.retain_imported_interface_fact(
                interface,
                summary,
                ImportedInterfaceAccess::HiddenSummaryClosure,
                direct_dependency,
                import_span,
            )?;
        }

        Ok(())
    }

    fn retain_imported_interface_fact(
        &mut self,
        exported: &CheckedInterfaceFact,
        summary: &ExportSummary,
        access: ImportedInterfaceAccess,
        direct_dependency: ModuleId,
        span: crate::source::Span,
    ) -> Result<(), ResolveError> {
        self.constraint_work.charge(1).map_err(|()| {
            error(
                ResolveReason::ConstraintResourceExhausted,
                span,
                "imported interface route retention exceeded its work budget",
            )
        })?;
        let owner_is_summary = exported.id.module() == summary.module();
        if access == ImportedInterfaceAccess::HiddenSummaryClosure && owner_is_summary {
            return Err(error(
                ResolveReason::InternalState,
                span,
                "an interface summary contains an identity at the wrong visibility boundary",
            ));
        }
        if let Some(existing) = self.imported.interface(exported.id) {
            let mut nominal_identities = MatchedNominalIdentities::default();
            let matches = same_checked_interface_fact_observing_nominals_with_budget(
                existing,
                exported,
                &mut self.type_work,
                &mut self.constraint_work,
                &mut nominal_identities,
            )
            .map_err(|failure| imported_fact_comparison_error(failure, span))?;
            if !matches {
                return Err(error(
                    ResolveReason::InternalState,
                    span,
                    "alternate interface routes disagree on the checked fact",
                ));
            }
            self.compare_retained_nominal_closure(&nominal_identities, summary, span)?;
            self.imported.merge_interface_route(
                exported.id,
                direct_dependency,
                span,
                access == ImportedInterfaceAccess::PublicExport,
            );
            return Ok(());
        }
        self.imported.reserve_interface().map_err(|()| {
            error(
                ResolveReason::ConstraintResourceExhausted,
                span,
                "imported interface storage exceeded its work budget",
            )
        })?;
        let retained_fact_count = exported.methods.len().checked_add(1).ok_or_else(|| {
            error(
                ResolveReason::ConstraintResourceExhausted,
                span,
                "imported interface retention accounting overflowed",
            )
        })?;
        self.constraint_work
            .charge(retained_fact_count)
            .map_err(|()| {
                error(
                    ResolveReason::ConstraintResourceExhausted,
                    span,
                    "imported interface retention exceeded its work budget",
                )
            })?;
        self.type_work.charge(retained_fact_count).map_err(|()| {
            error(
                ResolveReason::TypeResourceExhausted,
                span,
                "imported interface retention exceeded its type-work budget",
            )
        })?;
        let mut methods = Vec::new();
        let mut authority_method_indices: Vec<usize> = Vec::new();
        methods.try_reserve(exported.methods.len()).map_err(|_| {
            error(
                ResolveReason::ConstraintResourceExhausted,
                span,
                "imported interface retention exceeded its work budget",
            )
        })?;
        for method in &exported.methods {
            if method.id.interface() != exported.id {
                return Err(error(
                    ResolveReason::InternalState,
                    span,
                    "an interface summary contains a method from another interface",
                ));
            }
            let authority_work = method.authoritative_type_parameters().len();
            if authority_work != 0 {
                self.constraint_work.charge(1).map_err(|()| {
                    error(
                        ResolveReason::ConstraintResourceExhausted,
                        span,
                        "imported method authority index exceeded its work budget",
                    )
                })?;
                authority_method_indices.try_reserve(1).map_err(|_| {
                    error(
                        ResolveReason::ConstraintResourceExhausted,
                        span,
                        "imported method authority index exceeded its work budget",
                    )
                })?;
            }
            self.constraint_work.charge(authority_work).map_err(|()| {
                error(
                    ResolveReason::ConstraintResourceExhausted,
                    span,
                    "imported method authority exceeded its work budget",
                )
            })?;
            self.type_work.charge(authority_work).map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    span,
                    "imported method authority exceeded its type-work budget",
                )
            })?;
            self.constraint_work
                .charge_type(&method.value_type)
                .map_err(|()| {
                    error(
                        ResolveReason::ConstraintResourceExhausted,
                        span,
                        "imported method signature exceeded its work budget",
                    )
                })?;
            self.retain_type_nominals(&method.value_type, summary, span)?;
            let value_type = IterativeTypeOwner::new(
                clone_type_with_budget(&method.value_type, &mut self.type_work).map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        span,
                        "imported method signature exceeded its type-work budget",
                    )
                })?,
            );
            let type_parameters = clone_resolved_type_variables_with_budget(
                method.type_parameters(),
                &mut self.type_work,
            )
            .map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    span,
                    "imported method parameters exceeded their type-work budget",
                )
            })?;
            methods.push(
                CheckedInterfaceMethodFact::clone_with_binder_authority(
                    method,
                    type_parameters.into_boxed_slice(),
                    value_type.into_inner(),
                    &mut self.type_work,
                    &mut self.constraint_work,
                )
                .map_err(|failure| match failure {
                    ResolvedBuildFailure::Kind(context) => kind_context_error(
                        context,
                        span,
                        "an imported method authority disagrees with its checked mirror",
                    ),
                    ResolvedBuildFailure::TypeResource => error(
                        ResolveReason::TypeResourceExhausted,
                        span,
                        "imported method authority exceeded its type-work budget",
                    ),
                    ResolvedBuildFailure::ConstraintResource => error(
                        ResolveReason::ConstraintResourceExhausted,
                        span,
                        "imported method authority exceeded its work budget",
                    ),
                    ResolvedBuildFailure::InvalidState => error(
                        ResolveReason::InternalState,
                        span,
                        "an imported method authority disagrees with its checked mirror",
                    ),
                })?,
            );
            if authority_work != 0 {
                authority_method_indices.push(methods.len() - 1);
            }
        }
        let mut parameters = ImportedTypeVariableBuffer(Vec::new());
        parameters
            .try_reserve(exported.parameters.len())
            .map_err(|_| {
                error(
                    ResolveReason::ConstraintResourceExhausted,
                    span,
                    "imported interface parameters exceeded their work budget",
                )
            })?;
        for parameter in &exported.parameters {
            parameters.push(self.clone_type_variable_for_retention(
                parameter,
                span,
                "imported interface parameter exceeded its type-work budget",
            )?);
        }
        let determination = exported
            .determination()
            .map(|key| key.clone_with_budget(&mut self.constraint_work))
            .transpose()
            .map_err(|()| {
                error(
                    ResolveReason::ConstraintResourceExhausted,
                    span,
                    "imported interface determinant key exceeded its work budget",
                )
            })?;
        let retained = CheckedInterfaceFact::new(
            exported.id,
            exported.spelling.clone(),
            parameters.into_boxed_slice(),
            determination,
            methods.into_boxed_slice(),
            exported.origin.clone(),
            exported.span,
        );
        self.imported.insert_interface_with_authority_indices(
            retained,
            authority_method_indices.into_boxed_slice(),
            direct_dependency,
            span,
            access == ImportedInterfaceAccess::PublicExport,
        );
        Ok(())
    }

    fn retain_imported_implementation_fact<'a>(
        &mut self,
        exported: &'a AuthorizedImplementationFact,
        summary: &ExportSummary,
        selection: ImplementationImportSelection,
        capture_graph_visits: &mut CaptureGraphVisits<'a>,
    ) -> Result<(), ResolveError> {
        let span = selection.selector_span;
        self.constraint_work.charge(1).map_err(|()| {
            error(
                ResolveReason::ConstraintResourceExhausted,
                span,
                "imported implementation route retention exceeded its work budget",
            )
        })?;
        let fact = exported.fact();
        let authorization_is_well_formed = exported
            .authorization()
            .is_well_formed_for(summary.module(), fact, &mut self.constraint_work)
            .map_err(|()| {
                error(
                    ResolveReason::ConstraintResourceExhausted,
                    span,
                    "implementation authorization inspection exceeded its work budget",
                )
            })?;
        if selection.direct_dependency != summary.module() || !authorization_is_well_formed {
            return Err(error(
                ResolveReason::InternalState,
                span,
                "an implementation summary contains an invalid authorization route",
            ));
        }
        if let Some(existing) = self.imported.implementation(fact.id) {
            let mut nominal_identities = MatchedNominalIdentities::default();
            let matches = same_checked_implementation_fact_observing_nominals_with_budget(
                existing,
                fact,
                &mut self.type_work,
                &mut self.constraint_work,
                &mut nominal_identities,
            )
            .map_err(|failure| imported_fact_comparison_error(failure, span))?;
            if !matches {
                return Err(error(
                    ResolveReason::InternalState,
                    span,
                    "alternate implementation routes disagree on the checked fact",
                ));
            }
            self.compare_retained_nominal_closure(&nominal_identities, summary, span)?;
        }
        let authorization = ImplementationAuthorization::prepend(
            self.module,
            selection.direct_dependency,
            selection.import_span,
            exported.authorization(),
            &mut self.constraint_work,
        )
        .map_err(|()| {
            error(
                ResolveReason::ConstraintResourceExhausted,
                span,
                "imported implementation route retention exceeded its work budget",
            )
        })?;
        let mut public_authorization = selection
            .public
            .then(|| {
                ImplementationAuthorization::prepend(
                    self.module,
                    selection.direct_dependency,
                    selection.import_span,
                    exported.authorization(),
                    &mut self.constraint_work,
                )
            })
            .transpose()
            .map_err(|()| {
                error(
                    ResolveReason::ConstraintResourceExhausted,
                    span,
                    "public implementation route retention exceeded its work budget",
                )
            })?;
        let needs_public_order = public_authorization.is_some()
            && match self.imported.implementation_import(fact.id) {
                Some(existing) => existing.public_authorization().is_none(),
                None => true,
            };
        if needs_public_order {
            self.constraint_work.charge(1).map_err(|()| {
                error(
                    ResolveReason::ConstraintResourceExhausted,
                    span,
                    "public implementation ordering exceeded its work budget",
                )
            })?;
            self.imported
                .reserve_public_implementation()
                .map_err(|()| {
                    error(
                        ResolveReason::ConstraintResourceExhausted,
                        span,
                        "public implementation ordering exceeded its work budget",
                    )
                })?;
            self.public_implementation_route_ranks
                .try_reserve(1)
                .map_err(|_| {
                    error(
                        ResolveReason::ConstraintResourceExhausted,
                        span,
                        "public implementation route ordering exceeded its work budget",
                    )
                })?;
        }
        if self.imported.implementation(fact.id).is_some() {
            let existing_rank = self
                .implementation_route_ranks
                .get(&fact.id)
                .copied()
                .ok_or_else(|| {
                    error(
                        ResolveReason::InternalState,
                        span,
                        "an effective implementation route lost its transient ordering rank",
                    )
                })?;
            let existing_public_rank = self
                .public_implementation_route_ranks
                .get(&fact.id)
                .copied();
            let existing = self
                .imported
                .implementation_import(fact.id)
                .ok_or_else(|| {
                    error(
                        ResolveReason::InternalState,
                        span,
                        "an implementation route rank has no selected fact",
                    )
                })?;
            let replace_effective_rank = effective_implementation_route_precedes(
                &authorization,
                selection.route_rank,
                &existing.authorization,
                existing_rank,
                span,
                &mut self.constraint_work,
            )?;
            if existing.public_authorization.is_some() != existing_public_rank.is_some() {
                return Err(error(
                    ResolveReason::InternalState,
                    span,
                    "a public implementation route lost its transient ordering rank",
                ));
            }
            let replace_public_rank = if let Some(candidate) = &public_authorization {
                match (&existing.public_authorization, existing_public_rank) {
                    (Some(selected), Some(selected_rank)) => public_implementation_route_precedes(
                        candidate,
                        selection.route_rank,
                        selected,
                        selected_rank,
                        span,
                        &mut self.constraint_work,
                    )?,
                    (None, None) => true,
                    (Some(_), None) | (None, Some(_)) => {
                        return Err(error(
                            ResolveReason::InternalState,
                            span,
                            "a public implementation route lost its transient ordering rank",
                        ));
                    }
                }
            } else {
                false
            };
            let effective_replacement = replace_effective_rank.then_some(authorization);
            let public_replacement = replace_public_rank
                .then(|| public_authorization.take())
                .flatten();
            self.imported
                .commit_existing_implementation_routes(
                    fact.id,
                    effective_replacement,
                    public_replacement,
                    needs_public_order,
                )
                .map_err(|()| {
                    error(
                        ResolveReason::InternalState,
                        span,
                        "an implementation route rank has no selected fact",
                    )
                })?;
            if replace_effective_rank {
                self.implementation_route_ranks
                    .insert(fact.id, selection.route_rank);
            }
            if replace_public_rank {
                self.public_implementation_route_ranks
                    .insert(fact.id, selection.route_rank);
            }
            return Ok(());
        }
        self.constraint_work
            .charge(
                fact.head_parameters
                    .len()
                    .saturating_add(fact.prerequisites.len())
                    .saturating_add(fact.methods.len())
                    .saturating_add(1),
            )
            .map_err(|()| {
                error(
                    ResolveReason::ConstraintResourceExhausted,
                    span,
                    "imported implementation retention exceeded its work budget",
                )
            })?;
        for argument in fact.arguments() {
            self.constraint_work.charge_type(argument).map_err(|()| {
                error(
                    ResolveReason::ConstraintResourceExhausted,
                    span,
                    "imported implementation head exceeded its work budget",
                )
            })?;
            self.retain_type_nominals(argument, summary, span)?;
        }

        self.type_work
            .charge(fact.prerequisites.len().saturating_add(fact.methods.len()))
            .map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    span,
                    "imported implementation retention exceeded its type-work budget",
                )
            })?;
        let mut prerequisites = Vec::new();
        prerequisites
            .try_reserve(fact.prerequisites.len())
            .map_err(|_| {
                error(
                    ResolveReason::ConstraintResourceExhausted,
                    span,
                    "imported prerequisite retention exceeded its work budget",
                )
            })?;
        for (index, prerequisite) in fact.prerequisites.iter().enumerate() {
            if prerequisite.id.owner() != RequirementOwner::Impl(fact.id)
                || usize::try_from(prerequisite.id.declaration()) != Ok(index)
            {
                return Err(error(
                    ResolveReason::InternalState,
                    span,
                    "an implementation summary contains an invalid prerequisite identity",
                ));
            }
            for argument in prerequisite.arguments() {
                self.constraint_work.charge_type(argument).map_err(|()| {
                    error(
                        ResolveReason::ConstraintResourceExhausted,
                        span,
                        "imported prerequisite exceeded its work budget",
                    )
                })?;
                self.retain_type_nominals(argument, summary, span)?;
            }
            prerequisites.push(CheckedRequirement {
                id: prerequisite.id,
                application: prerequisite
                    .application()
                    .clone_with_budget(&mut self.type_work)
                    .map_err(|()| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            span,
                            "imported prerequisite exceeded its type-work budget",
                        )
                    })?,
                origin: prerequisite.origin.clone(),
                span: prerequisite.span,
            });
        }
        let mut head_parameters = ImportedTypeVariableBuffer(Vec::new());
        head_parameters
            .try_reserve(fact.head_parameters.len())
            .map_err(|_| {
                error(
                    ResolveReason::ConstraintResourceExhausted,
                    span,
                    "imported implementation parameters exceeded their work budget",
                )
            })?;
        for parameter in &fact.head_parameters {
            head_parameters.push(self.clone_type_variable_for_retention(
                parameter,
                span,
                "imported implementation parameters exceeded their type-work budget",
            )?);
        }
        let mut methods = Vec::new();
        methods.try_reserve(fact.methods.len()).map_err(|_| {
            error(
                ResolveReason::ConstraintResourceExhausted,
                span,
                "imported implementation methods exceeded their work budget",
            )
        })?;
        let defining_interface = summary
            .interfaces()
            .chain(summary.hidden_interfaces())
            .find(|interface| interface.id == fact.interface())
            .ok_or_else(|| {
                error(
                    ResolveReason::InternalState,
                    span,
                    "an implementation summary has no defining interface fact",
                )
            })?;
        for (index, method) in fact.methods.iter().enumerate() {
            let method_retention_work = method
                .scheme
                .type_parameters
                .len()
                .checked_add(method.scheme.requirements.len())
                .and_then(|work| work.checked_add(1))
                .ok_or_else(|| {
                    error(
                        ResolveReason::ConstraintResourceExhausted,
                        span,
                        "imported implementation method accounting overflowed",
                    )
                })?;
            self.constraint_work
                .charge(method_retention_work)
                .map_err(|()| {
                    error(
                        ResolveReason::ConstraintResourceExhausted,
                        span,
                        "imported implementation method exceeded its work budget",
                    )
                })?;
            let interface_method = defining_interface.methods.get(index).ok_or_else(|| {
                error(
                    ResolveReason::InternalState,
                    span,
                    "an implementation summary has an incomplete method relation",
                )
            })?;
            let expected_parameter_count = fact
                .head_parameters
                .len()
                .checked_add(interface_method.authoritative_type_parameters().len())
                .ok_or_else(|| {
                    error(
                        ResolveReason::ConstraintResourceExhausted,
                        span,
                        "imported implementation method parameter accounting overflowed",
                    )
                })?;
            let method_identity_is_valid = method.id.implementation() == fact.id
                && method.id.method() == method.method
                && method.method.interface() == fact.interface()
                && usize::try_from(method.method.declaration()) == Ok(index)
                && interface_method.id == method.method
                && method.binder.module() == Some(fact.id.module())
                && method.head_type_parameter_count() == fact.head_parameters.len()
                && method.scheme.type_parameters.len() == expected_parameter_count;
            if !method_identity_is_valid {
                return Err(error(
                    ResolveReason::InternalState,
                    span,
                    "an implementation summary contains an unauthenticated method scheme",
                ));
            }
            let parameters_match = same_kinded_parameters_with_two_binder_slices(
                &method.scheme.type_parameters,
                &fact.head_parameters,
                interface_method.authoritative_type_parameters(),
                &mut self.constraint_work,
            )
            .map_err(|()| {
                error(
                    ResolveReason::ConstraintResourceExhausted,
                    span,
                    "imported implementation method binder authentication exceeded its work budget",
                )
            })?;
            let method_identity_is_valid = parameters_match
                && method.scheme.requirements.len() == fact.prerequisites.len()
                && method
                    .scheme
                    .requirements
                    .iter()
                    .zip(&fact.prerequisites)
                    .all(|(requirement, prerequisite)| {
                        requirement.id == prerequisite.id
                            && requirement.interface() == prerequisite.interface()
                            && requirement.arguments().len() == prerequisite.arguments().len()
                    });
            if !method_identity_is_valid {
                return Err(error(
                    ResolveReason::InternalState,
                    span,
                    "an implementation summary contains an unauthenticated method scheme",
                ));
            }
            self.constraint_work
                .charge_type(&method.scheme.value_type)
                .map_err(|()| {
                    error(
                        ResolveReason::ConstraintResourceExhausted,
                        span,
                        "imported implementation method type exceeded its work budget",
                    )
                })?;
            for requirement in &method.scheme.requirements {
                for argument in requirement.arguments() {
                    self.constraint_work.charge_type(argument).map_err(|()| {
                        error(
                            ResolveReason::ConstraintResourceExhausted,
                            span,
                            "imported implementation method requirement exceeded its work budget",
                        )
                    })?;
                }
            }
            self.retain_scheme_nominals(&method.scheme, summary, span)?;
            if capture_graph_visits
                .visit(&method.capture, &mut self.type_work)
                .map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        span,
                        "imported implementation capture graph tracking exceeded its work budget",
                    )
                })?
            {
                for ty in method.capture.types(&mut self.type_work).map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        span,
                        "imported implementation capture type scan exceeded its work budget",
                    )
                })? {
                    self.retain_capture_type_metadata(ty, summary, span)?;
                }
                for effect in method.capture.effects(&mut self.type_work).map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        span,
                        "imported implementation capture effect scan exceeded its work budget",
                    )
                })? {
                    let declaration = summary.effect_by_id(effect).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            span,
                            "an implementation capture graph references missing effect metadata",
                        )
                    })?;
                    self.retain_imported_effect(declaration, span)?;
                }
            }
            methods.push(crate::resolved::CheckedImplementationMethodFact {
                capture: method
                    .capture
                    .clone_with_budget(&mut self.type_work)
                    .map_err(|()| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            span,
                            "imported implementation capture retention exceeded its work budget",
                        )
                    })?,
                id: method.id,
                method: method.method,
                binder: method.binder,
                scheme: method
                    .scheme
                    .clone_with_budget(&mut self.type_work)
                    .map_err(|()| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            span,
                            "imported implementation method scheme exceeded its type-work budget",
                        )
                    })?,
                head_type_parameter_count: method.head_type_parameter_count(),
                origin: method.origin.clone(),
                span: method.span,
            });
        }
        let cloned_fact = CheckedImplementationFact {
            id: fact.id,
            application: fact
                .application()
                .clone_with_budget(&mut self.type_work)
                .map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        span,
                        "imported implementation head exceeded its type-work budget",
                    )
                })?,
            head_parameters: head_parameters.into_boxed_slice(),
            prerequisites: prerequisites.into_boxed_slice(),
            methods: methods.into_boxed_slice(),
            origin: fact.origin.clone(),
            span: fact.span,
        };
        self.imported.reserve_implementation().map_err(|()| {
            error(
                ResolveReason::ConstraintResourceExhausted,
                span,
                "imported implementation storage exceeded its work budget",
            )
        })?;
        self.implementation_route_ranks
            .try_reserve(1)
            .map_err(|_| {
                error(
                    ResolveReason::ConstraintResourceExhausted,
                    span,
                    "implementation route ordering exceeded its work budget",
                )
            })?;
        if self
            .implementation_route_ranks
            .insert(fact.id, selection.route_rank)
            .is_some()
        {
            return Err(error(
                ResolveReason::InternalState,
                span,
                "an implementation route rank was retained twice",
            ));
        }
        if public_authorization.is_some()
            && self
                .public_implementation_route_ranks
                .insert(fact.id, selection.route_rank)
                .is_some()
        {
            return Err(error(
                ResolveReason::InternalState,
                span,
                "a public implementation route rank was retained twice",
            ));
        }
        self.imported
            .insert_implementation(cloned_fact, authorization, public_authorization);
        if needs_public_order {
            self.imported
                .mark_implementation_public(fact.id)
                .map_err(|()| {
                    error(
                        ResolveReason::InternalState,
                        span,
                        "a public implementation lost its selected fact",
                    )
                })?;
        }
        Ok(())
    }

    fn retain_imported_global<'a>(
        &mut self,
        exported: &'a ExportedGlobal,
        summary: &ExportSummary,
        span: crate::source::Span,
        capture_graph_visits: &mut CaptureGraphVisits<'a>,
    ) -> Result<(), ResolveError> {
        let constrained = !exported.scheme.requirements.is_empty();
        if constrained {
            self.constraint_work.charge(1).map_err(|()| {
                error(
                    ResolveReason::ConstraintResourceExhausted,
                    span,
                    "imported constraint route retention exceeded its work budget",
                )
            })?;
        }
        if let Some(existing) = self.imported.global(exported.binder) {
            let mut nominal_identities = MatchedNominalIdentities::default();
            let matches = same_imported_global_fact_observing_nominals_with_budget(
                existing,
                exported,
                &mut self.type_work,
                &mut self.constraint_work,
                &mut nominal_identities,
            )
            .map_err(|failure| imported_fact_comparison_error(failure, span))?;
            if !matches {
                return Err(error(
                    ResolveReason::InternalState,
                    span,
                    "alternate global routes disagree on the checked fact",
                ));
            }
            self.compare_retained_nominal_closure(&nominal_identities, summary, span)?;
            return Ok(());
        }
        if constrained {
            self.constraint_work
                .charge(
                    exported
                        .scheme
                        .type_parameters
                        .len()
                        .saturating_add(exported.scheme.requirements.len())
                        .saturating_add(1),
                )
                .map_err(|()| {
                    error(
                        ResolveReason::ConstraintResourceExhausted,
                        span,
                        "imported constrained scheme exceeded its work budget",
                    )
                })?;
            self.constraint_work
                .charge_type(&exported.scheme.value_type)
                .map_err(|()| {
                    error(
                        ResolveReason::ConstraintResourceExhausted,
                        span,
                        "imported constrained value type exceeded its work budget",
                    )
                })?;
            for requirement in &exported.scheme.requirements {
                for argument in requirement.arguments() {
                    self.constraint_work.charge_type(argument).map_err(|()| {
                        error(
                            ResolveReason::ConstraintResourceExhausted,
                            span,
                            "imported requirement type exceeded its work budget",
                        )
                    })?;
                }
            }
        }
        let scheme = exported
            .scheme
            .clone_with_budget(&mut self.type_work)
            .map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    span,
                    "imported type retention exceeded its work budget",
                )
            })?;
        self.imported
            .insert_global(
                ImportedGlobalScheme {
                    capture: exported
                        .capture
                        .clone_with_budget(&mut self.type_work)
                        .map_err(|()| {
                            error(
                                ResolveReason::TypeResourceExhausted,
                                span,
                                "imported capture summary retention exceeded its work budget",
                            )
                        })?,
                    binder: exported.binder,
                    scheme,
                    origin: exported.origin.clone(),
                },
                &mut self.type_work,
            )
            .map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    span,
                    "imported global order retention exceeded its type-work budget",
                )
            })?;
        self.global_requirement_counts
            .insert(exported.binder, exported.scheme.requirements.len());
        self.retain_scheme_nominals(&exported.scheme, summary, span)?;
        if capture_graph_visits
            .visit(&exported.capture, &mut self.type_work)
            .map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    span,
                    "imported capture graph tracking exceeded its work budget",
                )
            })?
        {
            for ty in exported.capture.types(&mut self.type_work).map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    span,
                    "imported capture type scan exceeded its work budget",
                )
            })? {
                self.retain_capture_type_metadata(ty, summary, span)?;
            }
            for effect in exported
                .capture
                .effects(&mut self.type_work)
                .map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        span,
                        "imported capture effect scan exceeded its work budget",
                    )
                })?
            {
                let declaration = summary.effect_by_id(effect).ok_or_else(|| {
                    error(
                        ResolveReason::InternalState,
                        span,
                        "an exported capture graph references missing effect metadata",
                    )
                })?;
                self.retain_imported_effect(declaration, span)?;
            }
        }
        Ok(())
    }

    fn retain_scheme_nominals(
        &mut self,
        scheme: &ConstrainedScheme,
        summary: &ExportSummary,
        span: crate::source::Span,
    ) -> Result<(), ResolveError> {
        self.retain_type_nominals(&scheme.value_type, summary, span)?;
        for requirement in &scheme.requirements {
            for argument in requirement.arguments() {
                self.retain_type_nominals(argument, summary, span)?;
            }
        }
        Ok(())
    }

    fn constructor_scheme_retention_type_work(scheme: &ConstrainedScheme) -> Result<usize, ()> {
        let mut work = TypeWorkBudget::unbounded();
        work.charge(scheme.requirements.len())?;
        work.charge(scheme.type_parameters.len())?;
        for (_, kind) in &scheme.type_parameters {
            charge_kind_nodes(kind, &mut work)?;
        }
        for requirement in &scheme.requirements {
            for argument in requirement.arguments() {
                charge_type_cells(argument, &mut work)?;
            }
        }
        charge_type_cells(scheme.value_type(), &mut work)?;
        Ok(work.used())
    }

    fn constructor_payload_retention_type_work(payload: Option<&Type>) -> Result<usize, ()> {
        let mut work = TypeWorkBudget::unbounded();
        if let Some(payload) = payload {
            charge_type_cells(payload, &mut work)?;
        }
        Ok(work.used())
    }

    fn collect_exported_constructor_nominal_identities(
        &mut self,
        exported: &ExportedConstructor,
        nominal_identities: &mut MatchedNominalIdentities,
        span: crate::source::Span,
    ) -> Result<(), ResolveError> {
        for requirement in &exported.scheme.requirements {
            for argument in requirement.arguments() {
                collect_type_nominal_identities_with_constraint_budget(
                    argument,
                    &mut self.constraint_work,
                    nominal_identities,
                )
                .map_err(|()| {
                    imported_fact_comparison_error(ResolvedBuildFailure::ConstraintResource, span)
                })?;
            }
        }
        collect_type_nominal_identities_with_constraint_budget(
            exported.scheme.value_type(),
            &mut self.constraint_work,
            nominal_identities,
        )
        .map_err(|()| {
            imported_fact_comparison_error(ResolvedBuildFailure::ConstraintResource, span)
        })?;
        if let Some(payload) = exported.payload.as_ref() {
            collect_type_nominal_identities_with_constraint_budget(
                payload,
                &mut self.constraint_work,
                nominal_identities,
            )
            .map_err(|()| {
                imported_fact_comparison_error(ResolvedBuildFailure::ConstraintResource, span)
            })?;
        }
        Ok(())
    }

    fn clone_imported_string_after_precharge(
        value: &str,
        span: crate::source::Span,
    ) -> Result<String, ResolveError> {
        let mut cloned = String::new();
        cloned.try_reserve_exact(value.len()).map_err(|_| {
            error(
                ResolveReason::TypeResourceExhausted,
                span,
                "imported constructor spelling retention could not reserve storage",
            )
        })?;
        cloned.push_str(value);
        Ok(cloned)
    }

    fn clone_imported_payload_with_budget(
        payload: &Type,
        span: crate::source::Span,
        type_work: &mut TypeWorkBudget,
    ) -> Result<IterativeTypeOwner, ResolveError> {
        enum Task<'a> {
            Visit(&'a Type),
            Sequence(std::slice::Iter<'a, Type>),
            Tuple(usize),
            Application,
            Function,
            EffectfulFunction(EffectRow),
        }

        const MESSAGE: &str =
            "imported constructor payload retention exceeded its type-work budget";
        let start = type_work.used();
        charge_type_cells(payload, type_work)
            .map_err(|()| error(ResolveReason::TypeResourceExhausted, span, MESSAGE))?;
        let type_cells = type_work
            .used()
            .checked_sub(start)
            .ok_or_else(|| error(ResolveReason::InternalState, span, MESSAGE))?;

        let mut work = Vec::new();
        work.try_reserve(type_cells)
            .map_err(|_| error(ResolveReason::TypeResourceExhausted, span, MESSAGE))?;
        work.push(Task::Visit(payload));
        let mut rebuilt = ImportedTypeCloneBuffer(Vec::new());
        rebuilt
            .0
            .try_reserve(type_cells)
            .map_err(|_| error(ResolveReason::TypeResourceExhausted, span, MESSAGE))?;
        while let Some(task) = work.pop() {
            match task {
                Task::Visit(Type::Int) => rebuilt.push(Type::Int),
                Task::Visit(Type::Bool) => rebuilt.push(Type::Bool),
                Task::Visit(Type::Unit) => rebuilt.push(Type::Unit),
                Task::Visit(Type::Variable(id)) => rebuilt.push(Type::Variable(*id)),
                Task::Visit(Type::Inference(id)) => rebuilt.push(Type::Inference(*id)),
                Task::Visit(Type::Nominal(id)) => rebuilt.push(Type::Nominal(*id)),
                Task::Visit(Type::Tuple(elements)) => {
                    work.push(Task::Tuple(elements.len()));
                    work.push(Task::Sequence(elements.iter()));
                }
                Task::Visit(Type::Application(function, argument)) => {
                    work.push(Task::Application);
                    work.push(Task::Visit(argument));
                    work.push(Task::Visit(function));
                }
                Task::Visit(Type::Function(domain, codomain)) => {
                    work.push(Task::Function);
                    work.push(Task::Visit(codomain));
                    work.push(Task::Visit(domain));
                }
                Task::Visit(Type::EffectfulFunction(domain, codomain)) => {
                    work.push(Task::EffectfulFunction(codomain.effects().clone()));
                    work.push(Task::Visit(codomain.value()));
                    work.push(Task::Visit(domain));
                }
                Task::Visit(Type::Forall(_, _)) => {
                    return Err(error(ResolveReason::InternalState, span, MESSAGE));
                }
                Task::Sequence(mut remaining) => {
                    if let Some(next) = remaining.next() {
                        work.push(Task::Sequence(remaining));
                        work.push(Task::Visit(next));
                    }
                }
                Task::Tuple(count) => {
                    let elements = rebuilt.split_off(rebuilt.0.len() - count).into_vec();
                    rebuilt.push(Type::Tuple(elements.into_boxed_slice()));
                }
                Task::Application => {
                    let argument = rebuilt
                        .pop_owned()
                        .expect("an authenticated application retains its argument");
                    let function = rebuilt
                        .pop_owned()
                        .expect("an authenticated application retains its function");
                    rebuilt.push(Type::Application(
                        Box::new(function.into_inner()),
                        Box::new(argument.into_inner()),
                    ));
                }
                Task::Function => {
                    let codomain = rebuilt
                        .pop_owned()
                        .expect("an authenticated function retains its codomain");
                    let domain = rebuilt
                        .pop_owned()
                        .expect("an authenticated function retains its domain");
                    rebuilt.push(Type::Function(
                        Box::new(domain.into_inner()),
                        Box::new(codomain.into_inner()),
                    ));
                }
                Task::EffectfulFunction(effects) => {
                    let codomain = rebuilt
                        .pop_owned()
                        .expect("an authenticated effectful function retains its codomain");
                    let domain = rebuilt
                        .pop_owned()
                        .expect("an authenticated effectful function retains its domain");
                    rebuilt.push(Type::function_computation(
                        domain.into_inner(),
                        ComputationType::new(codomain.into_inner(), effects),
                    ));
                }
            }
        }
        let cloned = rebuilt
            .pop_owned()
            .ok_or_else(|| error(ResolveReason::InternalState, span, MESSAGE))?;
        if !rebuilt.0.is_empty() {
            return Err(error(ResolveReason::InternalState, span, MESSAGE));
        }
        Ok(cloned)
    }

    fn retain_type_nominals(
        &mut self,
        scheme: &Type,
        summary: &ExportSummary,
        span: crate::source::Span,
    ) -> Result<(), ResolveError> {
        self.retain_type_nominals_with(scheme, summary, span, false)
    }

    fn retain_capture_type_metadata(
        &mut self,
        ty: &Type,
        summary: &ExportSummary,
        span: crate::source::Span,
    ) -> Result<(), ResolveError> {
        self.retain_type_nominals_with(ty, summary, span, true)
    }

    fn retain_type_nominals_with(
        &mut self,
        scheme: &Type,
        summary: &ExportSummary,
        span: crate::source::Span,
        external_capture_facts: bool,
    ) -> Result<(), ResolveError> {
        enum Task<'a> {
            Type(&'a Type),
            Sequence(std::slice::Iter<'a, Type>),
        }

        let type_work_start = self.type_work.used();
        charge_type_cells(scheme, &mut self.type_work).map_err(|()| {
            error(
                ResolveReason::TypeResourceExhausted,
                span,
                "imported nominal retention exceeded its work budget",
            )
        })?;
        let type_cells = self.type_work.used().saturating_sub(type_work_start);
        let mut pending = Vec::new();
        pending.try_reserve(type_cells).map_err(|_| {
            error(
                ResolveReason::TypeResourceExhausted,
                span,
                "imported nominal traversal could not reserve work storage",
            )
        })?;
        pending.push(Task::Type(scheme));
        let mut seen = Vec::new();
        seen.try_reserve(type_cells).map_err(|_| {
            error(
                ResolveReason::TypeResourceExhausted,
                span,
                "imported nominal ordering could not reserve storage",
            )
        })?;
        let mut seen_effects = Vec::new();
        seen_effects.try_reserve(type_cells).map_err(|_| {
            error(
                ResolveReason::TypeResourceExhausted,
                span,
                "imported effect ordering could not reserve storage",
            )
        })?;
        while let Some(task) = pending.pop() {
            let Task::Type(ty) = task else {
                let Task::Sequence(mut remaining) = task else {
                    unreachable!()
                };
                if let Some(next) = remaining.next() {
                    pending.push(Task::Sequence(remaining));
                    pending.push(Task::Type(next));
                }
                continue;
            };
            match ty {
                Type::Nominal(id) => {
                    // Only capture metadata may mention internal lexical IDs.
                    // Keep traversing its complete types, including embedded
                    // effect instances, but demand no ordinary fact for them.
                    if external_capture_facts && id.is_lexical() {
                        continue;
                    }
                    let mut already_seen = false;
                    for retained in &seen {
                        self.type_work.charge(1).map_err(|()| {
                            error(
                                ResolveReason::TypeResourceExhausted,
                                span,
                                "imported nominal membership exceeded its type-work budget",
                            )
                        })?;
                        if retained == id {
                            already_seen = true;
                            break;
                        }
                    }
                    if !already_seen {
                        self.type_work.charge(1).map_err(|()| {
                            error(
                                ResolveReason::TypeResourceExhausted,
                                span,
                                "imported nominal ordering exceeded its type-work budget",
                            )
                        })?;
                        seen.push(*id);
                    }
                }
                Type::Application(function, argument) => {
                    pending.push(Task::Type(argument));
                    pending.push(Task::Type(function));
                }
                Type::Tuple(elements) => pending.push(Task::Sequence(elements.iter())),
                Type::Function(domain, codomain) => {
                    pending.push(Task::Type(codomain));
                    pending.push(Task::Type(domain));
                }
                Type::EffectfulFunction(domain, codomain) => {
                    for instance in codomain.effects().known() {
                        let identity = instance.effect();
                        let mut already_seen = false;
                        for retained in &seen_effects {
                            self.type_work.charge(1).map_err(|()| {
                                error(
                                    ResolveReason::TypeResourceExhausted,
                                    span,
                                    "imported effect membership exceeded its type-work budget",
                                )
                            })?;
                            if retained == &identity {
                                already_seen = true;
                                break;
                            }
                        }
                        if !already_seen {
                            self.type_work.charge(1).map_err(|()| {
                                error(
                                    ResolveReason::TypeResourceExhausted,
                                    span,
                                    "imported effect ordering exceeded its type-work budget",
                                )
                            })?;
                            seen_effects.push(identity);
                        }
                    }
                    for argument in codomain.effect_arguments() {
                        pending.push(Task::Type(argument));
                    }
                    pending.push(Task::Type(codomain.value()));
                    pending.push(Task::Type(domain));
                }
                Type::Forall(_, body) => pending.push(Task::Type(body)),
                Type::Int | Type::Bool | Type::Unit | Type::Variable(_) | Type::Inference(_) => {}
            }
        }
        for id in seen {
            let exported = Self::scheme_nominal_fact(summary, id, span)?;
            self.retain_scheme_nominal_fact(exported, span)?;
        }
        for id in seen_effects {
            let exported = summary.effect_by_id(id).ok_or_else(|| {
                error(
                    ResolveReason::InternalState,
                    span,
                    "an exported scheme references missing effect metadata",
                )
            })?;
            self.retain_imported_effect(exported, span)?;
        }
        Ok(())
    }

    fn scheme_nominal_fact<'a>(
        summary: &'a ExportSummary,
        id: NominalTypeId,
        span: crate::source::Span,
    ) -> Result<crate::resolved::ImportedNominalFactRef<'a>, ResolveError> {
        let exported = summary.nominal_fact(id).ok_or_else(|| {
            error(
                ResolveReason::InternalState,
                span,
                "an exported scheme references missing nominal metadata",
            )
        })?;
        if exported.declaration_kind == ResolvedNominalDeclarationKind::Newtype
            && exported.access == ImportedTypeAccess::Opaque
        {
            return summary.canonical_nominal_fact(id).ok_or_else(|| {
                error(
                    ResolveReason::InternalState,
                    span,
                    "an opaque newtype scheme is missing its canonical representation",
                )
            });
        }
        Ok(exported)
    }

    fn compare_retained_nominal_closure(
        &mut self,
        nominal_identities: &MatchedNominalIdentities,
        summary: &ExportSummary,
        span: crate::source::Span,
    ) -> Result<(), ResolveError> {
        for id in nominal_identities.identities() {
            let existing = self.imported.nominal(*id).ok_or_else(|| {
                error(
                    ResolveReason::InternalState,
                    span,
                    "an alternate route lost its retained nominal closure",
                )
            })?;
            let candidate = Self::scheme_nominal_fact(summary, *id, span)?;
            let matches = same_imported_nominal_closure_with_constraint_budget(
                existing,
                candidate,
                &mut self.constraint_work,
            )
            .map_err(|failure| imported_fact_comparison_error(failure, span))?;
            if !matches {
                return Err(error(
                    ResolveReason::InternalState,
                    span,
                    "alternate routes disagree on retained nominal metadata",
                ));
            }
        }
        Ok(())
    }

    fn retain_scheme_nominal_fact(
        &mut self,
        exported: crate::resolved::ImportedNominalFactRef<'_>,
        span: crate::source::Span,
    ) -> Result<(), ResolveError> {
        let prepared = self
            .imported
            .prepare_nominal_merge(
                crate::resolved::ImportedNominalFactRef {
                    constructors: &[],
                    access: ImportedTypeAccess::Hidden,
                    ..exported
                },
                &mut self.type_work,
                &mut self.constraint_work,
            )
            .map_err(|failure| imported_nominal_merge_error(failure, span))?;
        self.imported
            .commit_nominal_merge(prepared)
            .map_err(|failure| imported_nominal_merge_error(failure, span))
    }

    fn retain_imported_nominal(
        &mut self,
        exported: &ExportedType,
        summary: &ExportSummary,
        display_spelling: Option<&str>,
        span: crate::source::Span,
        retained_constructor_owners: &mut HashSet<NominalTypeId>,
    ) -> Result<(), ResolveError> {
        let candidate = crate::resolved::ImportedNominalFactRef {
            id: exported.id,
            declaration_kind: exported.declaration_kind,
            parameter_count: exported.parameter_count,
            constructor_count: exported.constructor_count,
            parameters: &exported.parameters,
            representation: (exported.access == ExportedTypeAccess::Transparent)
                .then_some(exported.representation.as_ref())
                .flatten(),
            representation_provenance: (exported.access == ExportedTypeAccess::Transparent)
                .then_some(exported.representation_provenance.as_ref())
                .flatten(),
            constructors: &exported.constructors,
            access: exported.access.into(),
            display_spelling,
            display_is_private: false,
            origin: &exported.origin,
        };
        if exported.access == ExportedTypeAccess::Transparent {
            self.retain_imported_constructor_family_once_per_route(
                candidate,
                summary,
                span,
                retained_constructor_owners,
            )
        } else {
            let canonical_representation = summary
                .canonical_nominal_fact(exported.id)
                .and_then(|fact| Some((fact.representation?, fact.representation_provenance?)));
            if exported.declaration_kind == ResolvedNominalDeclarationKind::Newtype
                && canonical_representation.is_none()
            {
                return Err(error(
                    ResolveReason::InternalState,
                    span,
                    "an opaque newtype export is missing its canonical representation",
                ));
            }
            if exported.declaration_kind == ResolvedNominalDeclarationKind::Data
                && canonical_representation.is_some()
            {
                return Err(error(
                    ResolveReason::InternalState,
                    span,
                    "an ordinary opaque type cannot retain a canonical representation",
                ));
            }
            let prepared = self
                .imported
                .prepare_nominal_merge(candidate, &mut self.type_work, &mut self.constraint_work)
                .map_err(|failure| imported_nominal_merge_error(failure, span))?;
            if let Some((representation, provenance)) = canonical_representation {
                self.imported
                    .retain_canonical_representation(
                        exported.id,
                        representation,
                        provenance,
                        &mut self.type_work,
                        &mut self.constraint_work,
                    )
                    .map_err(|failure| imported_nominal_merge_error(failure, span))?;
            }
            self.imported
                .commit_nominal_merge(prepared)
                .map_err(|failure| imported_nominal_merge_error(failure, span))
        }
    }

    #[cfg(test)]
    fn clone_type_variables_for_retention(
        &mut self,
        parameters: &[ResolvedTypeVariable],
        span: crate::source::Span,
        message: &'static str,
    ) -> Result<Box<[ResolvedTypeVariable]>, ResolveError> {
        let mut cloned = ImportedTypeVariableBuffer(Vec::new());
        cloned
            .try_reserve(parameters.len())
            .map_err(|_| error(ResolveReason::TypeResourceExhausted, span, message))?;
        for parameter in parameters {
            cloned.push(self.clone_type_variable_for_retention(parameter, span, message)?);
        }
        Ok(cloned.into_boxed_slice())
    }

    fn clone_global_type_parameters_for_registry(
        &mut self,
        parameters: &[Vec<ResolvedTypeVariable>],
        span: crate::source::Span,
    ) -> Result<Vec<ResolvedTypeVariable>, ResolveError> {
        const MESSAGE: &str = "global type-parameter registry retention exceeded its work budget";
        let retained_count = parameters
            .iter()
            .try_fold(0_usize, |count, parameters| {
                count.checked_add(parameters.len())
            })
            .ok_or_else(|| error(ResolveReason::TypeResourceExhausted, span, MESSAGE))?;
        let mut retained = Vec::new();
        retained
            .try_reserve(retained_count)
            .map_err(|_| error(ResolveReason::TypeResourceExhausted, span, MESSAGE))?;
        for parameter in parameters.iter().flatten() {
            retained.push(self.clone_type_variable_for_retention(parameter, span, MESSAGE)?);
        }
        Ok(retained)
    }

    fn retain_imported_constructor_family(
        &mut self,
        owner: crate::resolved::ImportedNominalFactRef<'_>,
        summary: &ExportSummary,
        span: crate::source::Span,
    ) -> Result<(), ResolveError> {
        let owner_was_retained = self.imported.nominal(owner.id).is_some();
        let validated_owner = self
            .imported
            .validate_nominal_merge_shape(owner, &mut self.constraint_work)
            .map_err(|failure| imported_nominal_merge_error(failure, span))?;
        self.constraint_work
            .charge(owner.constructors.len())
            .map_err(|()| {
                error(
                    ResolveReason::ConstraintResourceExhausted,
                    span,
                    "constructor-family transaction planning exceeded its constraint-work budget",
                )
            })?;
        let mut constructor_routes = Vec::new();
        constructor_routes
            .try_reserve_exact(owner.constructors.len())
            .map_err(|_| {
                error(
                    ResolveReason::ConstraintResourceExhausted,
                    span,
                    "constructor-family transaction planning could not reserve storage",
                )
            })?;
        let mut nominal_identities = MatchedNominalIdentities::default();
        let mut new_constructor_count = 0_usize;
        for identity in owner.constructors {
            let exported = summary.constructor_by_id(*identity).ok_or_else(|| {
                error(
                    ResolveReason::InternalState,
                    span,
                    "a transparent type summary lost one of its constructors",
                )
            })?;
            if let Some(existing) = self.imported.constructor(*identity) {
                let matches = same_imported_constructor_fact_observing_nominals_with_budget(
                    existing,
                    exported,
                    &mut self.type_work,
                    &mut self.constraint_work,
                    &mut nominal_identities,
                )
                .map_err(|failure| imported_fact_comparison_error(failure, span))?;
                if !matches {
                    return Err(error(
                        ResolveReason::InternalState,
                        span,
                        "alternate constructor routes disagree on the checked fact",
                    ));
                }
                constructor_routes.push(ValidatedImportedConstructorRoute {
                    exported,
                    requires_commit: false,
                });
            } else {
                self.collect_exported_constructor_nominal_identities(
                    exported,
                    &mut nominal_identities,
                    span,
                )?;
                new_constructor_count = new_constructor_count.checked_add(1).ok_or_else(|| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        span,
                        "constructor-family staging exceeded its type-work budget",
                    )
                })?;
                constructor_routes.push(ValidatedImportedConstructorRoute {
                    exported,
                    requires_commit: true,
                });
            }
        }

        let mut foreign_validated = Vec::<ValidatedImportedNominalMerge<'_>>::new();
        let mut owner_metadata_observed = false;
        for id in nominal_identities.identities() {
            let candidate = summary.nominal_fact(*id).ok_or_else(|| {
                error(
                    ResolveReason::InternalState,
                    span,
                    "an exported constructor references missing nominal metadata",
                )
            })?;
            if *id == owner.id {
                owner_metadata_observed = true;
                if owner_was_retained {
                    self.imported
                        .validate_nominal_merge_metadata(
                            &validated_owner,
                            &mut self.constraint_work,
                        )
                        .map_err(|failure| imported_nominal_merge_error(failure, span))?;
                }
            } else if let Some(existing) = self.imported.nominal(*id) {
                let matches = same_imported_nominal_closure_with_constraint_budget(
                    existing,
                    candidate,
                    &mut self.constraint_work,
                )
                .map_err(|failure| imported_fact_comparison_error(failure, span))?;
                if !matches {
                    return Err(error(
                        ResolveReason::InternalState,
                        span,
                        "alternate constructor routes disagree on retained nominal metadata",
                    ));
                }
            } else {
                let validated = self
                    .imported
                    .validate_nominal_merge_shape(
                        crate::resolved::ImportedNominalFactRef {
                            constructors: &[],
                            access: ImportedTypeAccess::Hidden,
                            ..candidate
                        },
                        &mut self.constraint_work,
                    )
                    .map_err(|failure| imported_nominal_merge_error(failure, span))?;
                self.constraint_work.charge(1).map_err(|()| {
                    imported_fact_comparison_error(ResolvedBuildFailure::ConstraintResource, span)
                })?;
                foreign_validated.try_reserve(1).map_err(|_| {
                    imported_fact_comparison_error(ResolvedBuildFailure::ConstraintResource, span)
                })?;
                foreign_validated.push(validated);
            }
        }
        if owner_was_retained && !owner_metadata_observed {
            self.imported
                .validate_nominal_merge_metadata(&validated_owner, &mut self.constraint_work)
                .map_err(|failure| imported_nominal_merge_error(failure, span))?;
        }

        let prepared_count = foreign_validated
            .len()
            .checked_add(usize::from(validated_owner.requires_commit()))
            .ok_or_else(|| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    span,
                    "nominal transaction staging exceeded its type-work budget",
                )
            })?;
        let mut retention_work = validated_owner
            .retention_type_work()
            .map_err(|failure| imported_nominal_merge_error(failure, span))?
            .checked_add(prepared_count)
            .and_then(|work| work.checked_add(new_constructor_count))
            .ok_or_else(|| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    span,
                    "constructor-family retention exceeded its type-work budget",
                )
            })?;
        for validated in &foreign_validated {
            retention_work = retention_work
                .checked_add(
                    validated
                        .retention_type_work()
                        .map_err(|failure| imported_nominal_merge_error(failure, span))?,
                )
                .ok_or_else(|| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        span,
                        "nominal-closure retention exceeded its type-work budget",
                    )
                })?;
        }
        for route in &constructor_routes {
            if !route.requires_commit {
                continue;
            }
            let exported = route.exported;
            let constructor_work =
                Self::constructor_payload_retention_type_work(exported.payload.as_ref())
                    .and_then(|work| {
                        work.checked_add(Self::constructor_scheme_retention_type_work(
                            &exported.scheme,
                        )?)
                        .and_then(|work| work.checked_add(1))
                        .ok_or(())
                    })
                    .map_err(|()| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            span,
                            "constructor fact retention exceeded its type-work budget",
                        )
                    })?;
            retention_work = retention_work
                .checked_add(constructor_work)
                .ok_or_else(|| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        span,
                        "constructor-family retention exceeded its type-work budget",
                    )
                })?;
        }
        self.type_work.charge(retention_work).map_err(|()| {
            error(
                ResolveReason::TypeResourceExhausted,
                span,
                "constructor-family retention exceeded its type-work budget",
            )
        })?;

        let mut prepared_nominals = Vec::new();
        prepared_nominals
            .try_reserve_exact(prepared_count)
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    span,
                    "nominal transaction staging could not reserve storage",
                )
            })?;
        if validated_owner.requires_commit() {
            prepared_nominals.push(
                self.imported
                    .materialize_nominal_merge_after_precharge(validated_owner)
                    .map_err(|failure| imported_nominal_merge_error(failure, span))?,
            );
        }
        for validated in foreign_validated {
            prepared_nominals.push(
                self.imported
                    .materialize_nominal_merge_after_precharge(validated)
                    .map_err(|failure| imported_nominal_merge_error(failure, span))?,
            );
        }

        let mut staged_constructors = ImportedConstructorFactBuffer(Vec::new());
        staged_constructors
            .try_reserve(new_constructor_count)
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    span,
                    "constructor transaction staging could not reserve storage",
                )
            })?;
        for route in &constructor_routes {
            if !route.requires_commit {
                continue;
            }
            let exported = route.exported;
            let mut unbounded = TypeWorkBudget::unbounded();
            let payload = exported
                .payload
                .as_ref()
                .map(|payload| {
                    Self::clone_imported_payload_with_budget(payload, span, &mut unbounded)
                })
                .transpose()?;
            let scheme = exported
                .scheme
                .clone_with_budget(&mut unbounded)
                .map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        span,
                        "imported constructor scheme retention could not reserve storage",
                    )
                })?;
            staged_constructors.push(ImportedConstructorFact {
                id: exported.id,
                spelling: Self::clone_imported_string_after_precharge(&exported.spelling, span)?,
                payload: payload.map(IterativeTypeOwner::into_inner),
                scheme,
                origin: exported.origin.clone(),
            });
        }

        self.imported
            .reserve_prepared_nominal_merges(&prepared_nominals)
            .map_err(|failure| imported_nominal_merge_error(failure, span))?;
        self.imported
            .reserve_constructor_inserts(new_constructor_count)
            .map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    span,
                    "constructor transaction publication could not reserve storage",
                )
            })?;
        self.imported
            .commit_prepared_nominal_merges(&mut prepared_nominals);
        self.imported
            .commit_constructor_inserts(staged_constructors.into_vec());
        if summary.has_effect_facts() {
            for route in &constructor_routes {
                let exported = route.exported;
                if let Some(payload) = &exported.payload {
                    self.retain_type_nominals(payload, summary, span)?;
                }
                self.retain_scheme_nominals(&exported.scheme, summary, span)?;
            }
        }
        Ok(())
    }

    fn retain_imported_constructor_family_once_per_route(
        &mut self,
        owner: crate::resolved::ImportedNominalFactRef<'_>,
        summary: &ExportSummary,
        span: crate::source::Span,
        retained_constructor_owners: &mut HashSet<NominalTypeId>,
    ) -> Result<(), ResolveError> {
        self.constraint_work.charge(1).map_err(|()| {
            error(
                ResolveReason::ConstraintResourceExhausted,
                span,
                "constructor-family route lookup exceeded its constraint-work budget",
            )
        })?;
        if retained_constructor_owners.contains(&owner.id) {
            return Ok(());
        }
        self.constraint_work.charge(1).map_err(|()| {
            error(
                ResolveReason::ConstraintResourceExhausted,
                span,
                "constructor-family route retention exceeded its constraint-work budget",
            )
        })?;
        retained_constructor_owners.try_reserve(1).map_err(|_| {
            error(
                ResolveReason::ConstraintResourceExhausted,
                span,
                "constructor-family route retention could not reserve storage",
            )
        })?;
        self.retain_imported_constructor_family(owner, summary, span)?;
        let inserted = retained_constructor_owners.insert(owner.id);
        debug_assert!(inserted);
        Ok(())
    }

    fn retain_imported_constructor_once_per_route(
        &mut self,
        exported: &ExportedConstructor,
        summary: &ExportSummary,
        span: crate::source::Span,
        retained_constructor_owners: &mut HashSet<NominalTypeId>,
    ) -> Result<(), ResolveError> {
        let owner = summary.nominal_fact(exported.id.owner()).ok_or_else(|| {
            error(
                ResolveReason::InternalState,
                span,
                "an exported constructor references missing owner metadata",
            )
        })?;
        self.retain_imported_constructor_family_once_per_route(
            owner,
            summary,
            span,
            retained_constructor_owners,
        )
    }

    #[cfg(test)]
    fn retain_imported_constructor(
        &mut self,
        exported: &ExportedConstructor,
        summary: &ExportSummary,
        span: crate::source::Span,
    ) -> Result<(), ResolveError> {
        let owner = summary.nominal_fact(exported.id.owner()).ok_or_else(|| {
            error(
                ResolveReason::InternalState,
                span,
                "an exported constructor references missing owner metadata",
            )
        })?;
        self.retain_imported_constructor_family(owner, summary, span)
    }

    fn file_name_is_bound(&self, spelling: &str) -> bool {
        self.module_aliases.contains_key(spelling)
            || self.type_names.contains_key(spelling)
            || self.interface_names.contains_key(spelling)
            || self.constructor_names.contains_key(spelling)
            || self.method_names.contains_key(spelling)
            || self
                .scopes
                .first()
                .is_some_and(|scope| scope.contains_key(spelling))
    }

    fn expression_name_is_bound(&self, spelling: &str) -> bool {
        self.module_aliases.contains_key(spelling)
            || self.constructor_names.contains_key(spelling)
            || self.method_names.contains_key(spelling)
            || self
                .scopes
                .first()
                .is_some_and(|scope| scope.contains_key(spelling))
    }

    fn imported_namespace(
        &self,
        reference: &SurfaceReference,
    ) -> Result<Option<&ImportedNamespaces>, ResolveError> {
        let SurfaceReference::Qualified(qualified) = reference else {
            return Ok(None);
        };
        self.module_aliases
            .get(&qualified.qualifier.text)
            .map(Some)
            .ok_or_else(|| {
                lookup_error(
                    ResolveContext::MissingModuleAlias,
                    qualified.qualifier.span,
                    &qualified.qualifier.text,
                    "this module alias is not bound",
                )
            })
    }

    fn nominal_reference(
        &mut self,
        reference: &SurfaceReference,
    ) -> Result<ImportedNominalName, ResolveError> {
        if let Some(namespace) = self.imported_namespace(reference)? {
            if namespace.interfaces.contains_key(&reference.member().text) {
                return Err(type_kind_error(
                    reference.member().span,
                    &reference.member().text,
                ));
            }
            return namespace
                .nominals
                .get(&reference.member().text)
                .copied()
                .ok_or_else(|| {
                    withheld_export_error(
                        reference.member().span,
                        &reference.member().text,
                        namespace
                            .withheld
                            .get(&(reference.member().text.clone(), WithheldNamespace::Nominal))
                            .copied(),
                    )
                });
        }
        let name = reference.member();
        if let Some(id) = charged_lexical_scope_lookup(
            &self.lexical_nominal_scopes,
            &name.text,
            name.span,
            &mut self.type_work,
            "lexical nominal lookup exceeded its type-work budget",
        )? {
            return Ok(ImportedNominalName { id });
        }
        if self.interface_names.contains_key(&name.text) {
            return Err(type_kind_error(name.span, &name.text));
        }
        let id = self.type_names.get(&name.text).copied().ok_or_else(|| {
            if let Some(withheld) = self
                .targeted_withheld
                .get(&(name.text.clone(), WithheldNamespace::Nominal))
                .copied()
            {
                return withheld_export_error(name.span, &name.text, Some(withheld));
            }
            let mut diagnostic = Diagnostic::new(
                ResolveReason::UnknownType,
                SourceLabel::new(name.span, "this nominal type is not declared"),
            );
            diagnostic.found = Some(name.text.clone());
            ResolveError(Box::new(diagnostic), Some(ResolveContext::Type))
        })?;
        Ok(ImportedNominalName { id })
    }

    fn interface_reference(
        &self,
        reference: &SurfaceReference,
    ) -> Result<ResolvedInterfaceOccurrence, ResolveError> {
        let member = reference.member();
        if let Some(namespace) = self.imported_namespace(reference)? {
            if let Some(id) = namespace.interfaces.get(&member.text).copied() {
                return Ok(ResolvedInterfaceOccurrence {
                    id,
                    spelling: member.text.clone(),
                    origin: Origin::Source(reference.span()),
                });
            }
            if namespace.nominals.contains_key(&member.text)
                || namespace.constructors.contains_key(&member.text)
                || namespace.terms.contains_key(&member.text)
            {
                return Err(interface_kind_error(member.span, &member.text));
            }
            return Err(withheld_export_error(
                member.span,
                &member.text,
                namespace
                    .withheld
                    .get(&(member.text.clone(), WithheldNamespace::Nominal))
                    .copied(),
            ));
        }
        if let Some(id) = self.interface_names.get(&member.text).copied() {
            return Ok(ResolvedInterfaceOccurrence {
                id,
                spelling: member.text.clone(),
                origin: Origin::Source(reference.span()),
            });
        }
        if self.file_name_is_bound(&member.text)
            || self
                .type_scopes
                .iter()
                .rev()
                .any(|scope| scope.contains_key(&member.text))
        {
            return Err(interface_kind_error(member.span, &member.text));
        }
        if let Some(withheld) = self
            .targeted_withheld
            .get(&(member.text.clone(), WithheldNamespace::Nominal))
            .copied()
        {
            return Err(withheld_export_error(
                member.span,
                &member.text,
                Some(withheld),
            ));
        }
        Err(unknown_interface_error(member.span, &member.text))
    }

    fn effect_reference(&self, reference: &SurfaceReference) -> Result<EffectId, ResolveError> {
        let member = reference.member();
        if let Some(namespace) = self.imported_namespace(reference)? {
            if let Some(id) = namespace.effects.get(&member.text).copied() {
                return Ok(id);
            }
            if namespace.nominals.contains_key(&member.text)
                || namespace.interfaces.contains_key(&member.text)
            {
                return Err(effect_kind_error(member.span, &member.text));
            }
            return Err(lookup_error(
                ResolveContext::ExportedEffect,
                member.span,
                &member.text,
                "this effect is not exported by the selected module",
            ));
        }
        if let Some(id) = self.effect_names.get(&member.text).copied() {
            return Ok(id);
        }
        if self.type_names.contains_key(&member.text)
            || self.interface_names.contains_key(&member.text)
        {
            return Err(effect_kind_error(member.span, &member.text));
        }
        Err(lookup_error(
            ResolveContext::Effect,
            member.span,
            &member.text,
            "this effect is not declared",
        ))
    }

    #[allow(clippy::type_complexity)]
    fn resolve_effect_row(
        &mut self,
        row: &crate::surface::SurfaceEffectRow,
    ) -> Result<(EffectRow, Box<[ResolvedTypeProvenance]>, Box<[usize]>), ResolveError> {
        let argument_count = row.effects.iter().try_fold(0usize, |count, instance| {
            count.checked_add(instance.arguments.len())
        });
        let argument_count = argument_count.ok_or_else(|| {
            error(
                ResolveReason::TypeResourceExhausted,
                row.span,
                "effect-argument provenance exceeded its type-work budget",
            )
        })?;
        self.type_work.charge(argument_count).map_err(|()| {
            error(
                ResolveReason::TypeResourceExhausted,
                row.span,
                "effect-argument provenance exceeded its type-work budget",
            )
        })?;
        let mut argument_provenance = Vec::new();
        argument_provenance
            .try_reserve_exact(argument_count)
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    row.span,
                    "effect-argument provenance could not reserve storage",
                )
            })?;
        self.type_work.charge(row.effects.len()).map_err(|()| {
            error(
                ResolveReason::TypeResourceExhausted,
                row.span,
                "effect-row storage exceeded its type-work budget",
            )
        })?;
        let mut resolved_instances = Vec::new();
        resolved_instances
            .try_reserve_exact(row.effects.len())
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    row.span,
                    "effect-row storage exceeded its type-work budget",
                )
            })?;
        for written in &row.effects {
            let effect = self.effect_reference(&written.effect)?;
            self.type_work
                .charge(written.arguments.len().checked_mul(2).ok_or_else(|| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        written.span,
                        "effect-argument storage exceeded its type-work budget",
                    )
                })?)
                .map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        written.span,
                        "effect-argument storage exceeded its type-work budget",
                    )
                })?;
            let mut arguments = Vec::new();
            let mut roots = Vec::new();
            arguments
                .try_reserve_exact(written.arguments.len())
                .map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        written.span,
                        "effect-argument storage exceeded its type-work budget",
                    )
                })?;
            roots
                .try_reserve_exact(written.arguments.len())
                .map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        written.span,
                        "effect-argument provenance could not reserve storage",
                    )
                })?;
            for argument in &written.arguments {
                let ResolvedType { ty, provenance, .. } = self.resolve_type(argument)?;
                roots.push(argument_provenance.len());
                argument_provenance.push(provenance);
                arguments.push(ty);
            }
            let instance = EffectInstance::new(effect, arguments.into_boxed_slice());
            resolved_instances.push((instance, written.span, roots.into_boxed_slice()));
        }
        let tail = row
            .tail
            .as_ref()
            .map(|tail| {
                self.type_scopes
                    .iter()
                    .rev()
                    .find_map(|scope| scope.get(&tail.text))
                    .copied()
                    .map(EffectRowVariable::rigid)
                    .ok_or_else(|| {
                        lookup_error(
                            ResolveContext::EffectRowParameter,
                            tail.span,
                            &tail.text,
                            "this effect-row tail parameter is not declared",
                        )
                    })
            })
            .transpose()?;
        let (row, roots) = build_source_effect_row_with_provenance(
            resolved_instances,
            tail,
            row.span,
            &mut self.type_work,
        )?;
        Ok((row, argument_provenance.into_boxed_slice(), roots))
    }

    fn resolve_effect_instance_parts(
        &mut self,
        effect: &SurfaceReference,
        arguments: &[SurfaceType],
        span: crate::source::Span,
    ) -> Result<ResolvedEffectInstance, ResolveError> {
        let identity = self.effect_reference(effect)?;
        self.type_work
            .charge(arguments.len().saturating_mul(2))
            .map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    span,
                    "effect-argument storage exceeded its type-work budget",
                )
            })?;
        let mut resolved = Vec::new();
        let mut argument_provenance = Vec::new();
        argument_provenance
            .try_reserve_exact(arguments.len())
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    span,
                    "effect-argument provenance could not reserve storage",
                )
            })?;
        resolved.try_reserve_exact(arguments.len()).map_err(|_| {
            error(
                ResolveReason::TypeResourceExhausted,
                span,
                "effect-argument storage exceeded its type-work budget",
            )
        })?;
        for argument in arguments {
            let ResolvedType { ty, provenance, .. } = self.resolve_type(argument)?;
            resolved.push(crate::types::IterativeTypeOwner::new(ty));
            argument_provenance.push(provenance);
        }
        self.type_work.charge(resolved.len()).map_err(|()| {
            error(
                ResolveReason::TypeResourceExhausted,
                span,
                "effect-argument retention exceeded its type-work budget",
            )
        })?;
        let mut retained = Vec::new();
        retained.try_reserve_exact(resolved.len()).map_err(|_| {
            error(
                ResolveReason::TypeResourceExhausted,
                span,
                "effect-argument retention could not reserve storage",
            )
        })?;
        for argument in resolved {
            retained.push(argument.into_inner());
        }
        Ok(ResolvedEffectInstance {
            instance: EffectInstance::new(identity, retained.into_boxed_slice()),
            argument_provenance: argument_provenance.into_boxed_slice(),
            origin: Origin::Source(effect.span()),
            span,
        })
    }

    fn resolved_operation(
        &self,
        effect: EffectId,
        operation: &SurfaceName,
    ) -> Result<OperationId, ResolveError> {
        self.local_operation_names
            .get(&effect)
            .and_then(|operations| operations.get(operation.text.as_str()))
            .copied()
            .or_else(|| {
                self.imported.effect(effect).and_then(|declaration| {
                    declaration
                        .operations
                        .iter()
                        .find(|candidate| candidate.spelling == operation.text)
                        .map(|operation| operation.id)
                })
            })
            .ok_or_else(|| {
                lookup_error(
                    ResolveContext::EffectOperation,
                    operation.span,
                    &operation.text,
                    "this operation is not declared by the selected effect",
                )
            })
    }

    fn resolve_requirements(
        &mut self,
        owner: RequirementOwner,
        requirements: &[SurfaceRequirement],
    ) -> Result<Box<[ResolvedRequirement]>, ResolveError> {
        let Some(first) = requirements.first() else {
            return Ok(Box::new([]));
        };
        let mut resolved = ResolvedRequirementBuffer(Vec::new());
        resolved.0.try_reserve(requirements.len()).map_err(|_| {
            error(
                ResolveReason::TypeResourceExhausted,
                first.span,
                "requirement storage exceeded its work budget",
            )
        })?;
        for (index, requirement) in requirements.iter().enumerate() {
            let index = u32::try_from(index).map_err(|_| {
                error(
                    ResolveReason::InternalState,
                    requirement.span,
                    "the declaration contains too many interface requirements",
                )
                .with_context(ResolveContext::IdentityExhaustion(
                    ResolveIdentitySpace::Requirement,
                ))
            })?;
            let application = self.resolve_interface_application(requirement)?;
            resolved.0.push(ResolvedRequirement {
                id: RequirementId::new(owner, index),
                application,
            });
        }
        Ok(resolved.into_boxed_slice())
    }

    fn resolve_interface_application(
        &mut self,
        application: &SurfaceInterfaceApplication,
    ) -> Result<ResolvedInterfaceApplication, ResolveError> {
        let interface = self.interface_reference(&application.interface)?;
        if application.arguments.is_empty() {
            return Err(error(
                ResolveReason::InternalState,
                application.span,
                "the projected interface argument vector is empty",
            ));
        }
        let mut arguments = ResolvedTypeOccurrenceBuffer(Vec::new());
        arguments
            .0
            .try_reserve_exact(application.arguments.len())
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    application.span,
                    "interface argument storage could not be reserved",
                )
            })?;
        for argument in &application.arguments {
            arguments.0.push(self.resolve_type(argument)?);
        }
        Ok(ResolvedInterfaceApplication {
            interface,
            arguments: arguments.into_vec().into_boxed_slice(),
            span: application.span,
        })
    }

    fn resolve_interface_determination(
        &mut self,
        determination: &SurfaceInterfaceDetermination,
        parameters: &[ResolvedTypeVariable],
    ) -> Result<ResolvedInterfaceDetermination, ResolveError> {
        self.type_work.charge(parameters.len()).map_err(|()| {
            error(
                ResolveReason::TypeResourceExhausted,
                determination.span,
                "interface determination parameter indexing exceeded its type-work budget",
            )
        })?;

        let mut identities = HashMap::new();
        identities.try_reserve(parameters.len()).map_err(|_| {
            error(
                ResolveReason::TypeResourceExhausted,
                determination.span,
                "interface determination identity storage could not be reserved",
            )
        })?;
        for parameter in parameters {
            identities.insert(parameter.spelling.as_str(), parameter.id);
        }

        let mut resolve_side = |side: &crate::surface::SurfaceDeterminationSide| {
            let mut resolved = ResolvedDeterminationParameterBuffer(Vec::new());
            resolved
                .0
                .try_reserve_exact(side.parameters.len())
                .map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        side.span,
                        "interface determination side storage could not be reserved",
                    )
                })?;
            for name in &side.parameters {
                self.type_work.charge(1).map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        name.span,
                        "interface determination lookup exceeded its type-work budget",
                    )
                })?;
                let id = identities
                    .get(name.text.as_str())
                    .copied()
                    .ok_or_else(|| unknown_determination_parameter_error(name))?;
                self.type_work.charge(1).map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        name.span,
                        "interface determination occurrence retention exceeded its type-work budget",
                    )
                })?;
                resolved.0.push(ResolvedDeterminationParameter {
                    id,
                    spelling: try_clone_resolution_string(
                        &name.text,
                        name.span,
                        "interface determination spelling could not be retained",
                    )?,
                    origin: Origin::Source(name.span),
                });
            }
            Ok::<_, ResolveError>(resolved)
        };

        let determinant = resolve_side(&determination.determinant)?;
        let dependent = resolve_side(&determination.dependent)?;
        Ok(ResolvedInterfaceDetermination {
            determinant: ResolvedDeterminationSide {
                parameters: determinant.into_boxed_slice(),
                span: determination.determinant.span,
            },
            dependent: ResolvedDeterminationSide {
                parameters: dependent.into_boxed_slice(),
                span: determination.dependent.span,
            },
            span: determination.span,
        })
    }

    fn constructor_reference(
        &mut self,
        reference: &SurfaceReference,
    ) -> Result<ConstructorId, ResolveError> {
        if let Some(namespace) = self.imported_namespace(reference)? {
            return namespace
                .constructors
                .get(&reference.member().text)
                .copied()
                .ok_or_else(|| {
                    withheld_export_error(
                        reference.member().span,
                        &reference.member().text,
                        namespace
                            .withheld
                            .get(&(
                                reference.member().text.clone(),
                                WithheldNamespace::Constructor,
                            ))
                            .copied(),
                    )
                });
        }
        if let Some(constructor) = charged_lexical_scope_lookup(
            &self.lexical_constructor_scopes,
            &reference.member().text,
            reference.member().span,
            &mut self.type_work,
            "lexical constructor lookup exceeded its type-work budget",
        )?
        .or_else(|| {
            self.constructor_names
                .get(&reference.member().text)
                .copied()
        }) {
            return Ok(constructor);
        }
        if let Some(kind) = self
            .targeted_withheld
            .get(&(
                reference.member().text.clone(),
                WithheldNamespace::Constructor,
            ))
            .copied()
        {
            return Err(withheld_export_error(
                reference.member().span,
                &reference.member().text,
                Some(kind),
            ));
        }
        let mut diagnostic = Diagnostic::new(
            ResolveReason::UnknownConstructor,
            SourceLabel::new(reference.member().span, "this constructor is not declared"),
        );
        diagnostic.found = Some(reference.member().text.clone());
        Err(ResolveError(
            Box::new(diagnostic),
            Some(ResolveContext::Constructor),
        ))
    }

    fn allocate_global_binder(
        &mut self,
        definition: &SurfaceDefinition,
    ) -> Result<Binder, ResolveError> {
        let (global_name, global_name_span) = match &definition.kind {
            SurfaceDefinitionKind::Equational(equational) => {
                if equational.equations.is_empty() {
                    return Err(error(
                        ResolveReason::InternalState,
                        definition.span,
                        "the equational definition has no clause",
                    ));
                }
                for equation in &equational.equations {
                    if equational.interface.name.text != equation.name.text {
                        let mut diagnostic = Diagnostic::new(
                            ResolveReason::EquationNameMismatch,
                            SourceLabel::new(
                                equation.name.span,
                                "this equation name does not match its interface",
                            ),
                        );
                        diagnostic.related.push(SourceLabel::new(
                            equational.interface.name.span,
                            "the external interface declares this name",
                        ));
                        diagnostic.expected = Some(equational.interface.name.text.clone());
                        diagnostic.found = Some(equation.name.text.clone());
                        diagnostic.help = Some(format!(
                            "rename the equation head to `{}`",
                            equational.interface.name.text
                        ));
                        return Err(diagnostic.into());
                    }
                }
                (
                    equational.interface.name.text.as_str(),
                    equational.interface.name.span,
                )
            }
            SurfaceDefinitionKind::InlineOperational(operational) => (
                operational.header.name.text.as_str(),
                operational.header.name.span,
            ),
        };
        if let Some(first) = self.globals.get(global_name) {
            let mut diagnostic = Diagnostic::new(
                ResolveReason::DuplicateGlobal,
                SourceLabel::new(global_name_span, "this global name is already defined"),
            );
            diagnostic.related.push(SourceLabel::new(
                first.name_span,
                "the first global name is here",
            ));
            diagnostic.related.push(SourceLabel::new(
                first.definition_span,
                "the first complete definition is here",
            ));
            diagnostic.found = Some(global_name.to_owned());
            return Err(diagnostic.into());
        }
        if self.expression_name_is_bound(global_name) {
            return Err(import_conflict(global_name_span, global_name));
        }
        let global = self.allocate_binder(global_name, global_name_span)?;
        let requirement_count = match &definition.kind {
            SurfaceDefinitionKind::Equational(global) => global.interface.requirements.len(),
            SurfaceDefinitionKind::InlineOperational(global) => global.header.requirements.len(),
        };
        self.global_requirement_counts
            .insert(global.id, requirement_count);
        let Some(file_scope) = self.scopes.first_mut() else {
            return Err(error(
                ResolveReason::InternalState,
                definition.span,
                "the resolver lost the file scope",
            )
            .with_context(ResolveContext::MissingFileScope));
        };
        file_scope.insert(
            global.spelling.clone(),
            ResolvedTermBinding::local(ResolvedTermName::Global(global.id)),
        );
        self.globals.insert(
            global_name.to_owned(),
            GlobalFact {
                name_span: global_name_span,
                definition_span: definition.span,
            },
        );
        Ok(global)
    }

    fn resolve_declarations(
        &mut self,
        surface: &SurfaceModule,
    ) -> Result<ResolvedDeclarations, ResolveError> {
        let nominal_identities = self.install_nominal_identities(&surface.type_declarations)?;
        let interface_identities = self.install_interface_identities(&surface.interfaces)?;
        let effect_identities = self.install_effect_identities(&surface.effects)?;

        let mut nominal_type_parameters = Vec::new();
        nominal_type_parameters
            .try_reserve_exact(surface.type_declarations.len())
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "nominal type-parameter preparation storage could not be reserved",
                )
            })?;
        let mut interface_type_parameters = Vec::new();
        interface_type_parameters
            .try_reserve_exact(surface.interfaces.len())
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "interface type-parameter preparation storage could not be reserved",
                )
            })?;
        let mut global_type_parameters = Vec::new();
        global_type_parameters
            .try_reserve_exact(surface.definitions.len())
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "global type-parameter preparation storage could not be reserved",
                )
            })?;
        let mut effect_type_parameters = Vec::new();
        effect_type_parameters
            .try_reserve_exact(surface.effects.len())
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "effect type-parameter preparation storage could not be reserved",
                )
            })?;
        let mut pending_implementations = Vec::new();
        pending_implementations
            .try_reserve_exact(surface.implementations.len())
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "implementation type-parameter preparation storage could not be reserved",
                )
            })?;

        for declaration in &surface.declaration_order {
            match *declaration {
                SurfaceDeclarationIndex::Type(index) => {
                    let source = surface.type_declarations.get(index).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the surface declaration order contains an invalid type index",
                        )
                        .with_context(ResolveContext::DeclarationOrder {
                            kind: "nominal",
                            problem: "invalid-index",
                        })
                    })?;
                    if index < nominal_type_parameters.len() {
                        return Err(error(
                            ResolveReason::InternalState,
                            source.span,
                            "the surface declaration order repeats or reorders a nominal declaration",
                        ).with_context(ResolveContext::DeclarationOrder { kind: "nominal", problem: "repeated-or-reordered" }));
                    }
                    if index > nominal_type_parameters.len() {
                        return Err(error(
                            ResolveReason::InternalState,
                            source.span,
                            "the surface declaration order skips or reorders a nominal declaration",
                        )
                        .with_context(ResolveContext::DeclarationOrder {
                            kind: "nominal",
                            problem: "skipped-or-reordered",
                        }));
                    }
                    let identity = nominal_identities.get(index).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            source.span,
                            "the resolver lost a nominal declaration identity",
                        )
                    })?;
                    nominal_type_parameters
                        .push((identity.id, self.allocate_nominal_type_parameters(source)?));
                }
                SurfaceDeclarationIndex::Interface(index) => {
                    let source = surface.interfaces.get(index).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the surface declaration order contains an invalid interface index",
                        )
                        .with_context(ResolveContext::DeclarationOrder {
                            kind: "interface",
                            problem: "invalid-index",
                        })
                    })?;
                    if index < interface_type_parameters.len() {
                        return Err(error(
                            ResolveReason::InternalState,
                            source.span,
                            "the surface declaration order repeats or reorders an interface declaration",
                        ).with_context(ResolveContext::DeclarationOrder { kind: "interface", problem: "repeated-or-reordered" }));
                    }
                    if index > interface_type_parameters.len() {
                        return Err(error(
                            ResolveReason::InternalState,
                            source.span,
                            "the surface declaration order skips or reorders an interface declaration",
                        ).with_context(ResolveContext::DeclarationOrder { kind: "interface", problem: "skipped-or-reordered" }));
                    }
                    interface_type_parameters.push(self.prepare_interface_type_parameters(source)?);
                }
                SurfaceDeclarationIndex::Effect(index) => {
                    let source = surface.effects.get(index).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the surface declaration order contains an invalid effect index",
                        )
                        .with_context(ResolveContext::DeclarationOrder {
                            kind: "effect",
                            problem: "invalid-index",
                        })
                    })?;
                    if index != effect_type_parameters.len() {
                        return Err(error(
                            ResolveReason::InternalState,
                            source.span,
                            "the surface declaration order repeats, skips, or reorders an effect declaration",
                        ).with_context(ResolveContext::DeclarationOrder { kind: "effect", problem: "repeated-skipped-or-reordered" }));
                    }
                    effect_type_parameters.push(self.allocate_effect_type_parameters(source)?);
                }
                SurfaceDeclarationIndex::Global(index) => {
                    let source = surface.definitions.get(index).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the surface declaration order contains an invalid global index",
                        )
                        .with_context(ResolveContext::DeclarationOrder {
                            kind: "global",
                            problem: "invalid-index",
                        })
                    })?;
                    if index < global_type_parameters.len() {
                        return Err(error(
                            ResolveReason::InternalState,
                            source.span,
                            "the surface declaration order repeats or reorders a global declaration",
                        ).with_context(ResolveContext::DeclarationOrder { kind: "global", problem: "repeated-or-reordered" }));
                    }
                    if index > global_type_parameters.len() {
                        return Err(error(
                            ResolveReason::InternalState,
                            source.span,
                            "the surface declaration order skips or reorders a global declaration",
                        )
                        .with_context(ResolveContext::DeclarationOrder {
                            kind: "global",
                            problem: "skipped-or-reordered",
                        }));
                    }
                    global_type_parameters.push(self.allocate_global_type_parameters(source)?);
                }
                SurfaceDeclarationIndex::Implementation(index) => {
                    let source = surface.implementations.get(index).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the surface declaration order contains an invalid impl index",
                        )
                        .with_context(ResolveContext::DeclarationOrder {
                            kind: "implementation",
                            problem: "invalid-index",
                        })
                    })?;
                    if index < pending_implementations.len() {
                        return Err(error(
                            ResolveReason::InternalState,
                            source.span,
                            "the surface declaration order repeats or reorders an implementation declaration",
                        ).with_context(ResolveContext::DeclarationOrder { kind: "implementation", problem: "repeated-or-reordered" }));
                    }
                    if index > pending_implementations.len() {
                        return Err(error(
                            ResolveReason::InternalState,
                            source.span,
                            "the surface declaration order skips or reorders an implementation declaration",
                        ).with_context(ResolveContext::DeclarationOrder { kind: "implementation", problem: "skipped-or-reordered" }));
                    }
                    pending_implementations.push(self.prepare_implementation(index, source)?);
                }
            }
        }

        if nominal_type_parameters.len() != surface.type_declarations.len() {
            return Err(error(
                ResolveReason::InternalState,
                surface
                    .type_declarations
                    .get(nominal_type_parameters.len())
                    .map_or(surface.span, |declaration| declaration.span),
                "the surface declaration order omits a nominal declaration",
            )
            .with_context(ResolveContext::DeclarationOrder {
                kind: "nominal",
                problem: "omitted",
            }));
        }
        if interface_type_parameters.len() != surface.interfaces.len() {
            return Err(error(
                ResolveReason::InternalState,
                surface
                    .interfaces
                    .get(interface_type_parameters.len())
                    .map_or(surface.span, |declaration| declaration.span),
                "the surface declaration order omits an interface declaration",
            )
            .with_context(ResolveContext::DeclarationOrder {
                kind: "interface",
                problem: "omitted",
            }));
        }
        if global_type_parameters.len() != surface.definitions.len() {
            return Err(error(
                ResolveReason::InternalState,
                surface
                    .definitions
                    .get(global_type_parameters.len())
                    .map_or(surface.span, |declaration| declaration.span),
                "the surface declaration order omits a global declaration",
            )
            .with_context(ResolveContext::DeclarationOrder {
                kind: "global",
                problem: "omitted",
            }));
        }
        if effect_type_parameters.len() != surface.effects.len() {
            return Err(error(
                ResolveReason::InternalState,
                surface.span,
                "the surface declaration order omits an effect declaration",
            )
            .with_context(ResolveContext::DeclarationOrder {
                kind: "effect",
                problem: "omitted",
            }));
        }
        if pending_implementations.len() != surface.implementations.len() {
            return Err(error(
                ResolveReason::InternalState,
                surface
                    .implementations
                    .get(pending_implementations.len())
                    .map_or(surface.span, |declaration| declaration.span),
                "the surface declaration order omits an implementation declaration",
            )
            .with_context(ResolveContext::DeclarationOrder {
                kind: "implementation",
                problem: "omitted",
            }));
        }

        let (registry, constructor_payload_provenance) = self.resolve_registry_with_prepared(
            &surface.type_declarations,
            nominal_identities,
            nominal_type_parameters,
        )?;
        let (interfaces, interface_type_parameters) = self.resolve_interface_declarations(
            &surface.interfaces,
            interface_identities,
            interface_type_parameters,
            surface.span,
        )?;
        self.resolved_interfaces = ResolvedInterfaceBuffer(interfaces);
        let (effects, effect_registry_parameters) = self.resolve_effect_declarations(
            &surface.effects,
            effect_identities,
            effect_type_parameters,
            surface.span,
        )?;
        let mut registry_effects = Vec::new();
        registry_effects
            .try_reserve_exact(effects.len())
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    surface.span,
                    "effect registry storage could not be reserved",
                )
            })?;
        for effect in &effects {
            registry_effects.push(
                clone_resolved_effect_with_budget(effect, &mut self.type_work).map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        effect.span,
                        "effect registry retention exceeded its type-work budget",
                    )
                })?,
            );
        }
        let surface_definitions = &surface.definitions;
        let mut implementation_type_parameters = Vec::new();
        for (implementation, pending) in
            surface.implementations.iter().zip(&pending_implementations)
        {
            for parameter in pending
                .head_parameters
                .iter()
                .chain(&pending.prerequisite_only_parameters)
            {
                implementation_type_parameters.push(self.clone_type_variable_for_retention(
                    parameter,
                    implementation.span,
                    "implementation parameter retention exceeded its type-work budget",
                )?);
            }
        }
        let global_registry_type_parameters =
            self.clone_global_type_parameters_for_registry(&global_type_parameters, surface.span)?;
        let registry = registry
            .with_additional_type_variables(
                interface_type_parameters
                    .into_iter()
                    .chain(effect_registry_parameters)
                    .chain(global_registry_type_parameters)
                    .chain(implementation_type_parameters),
            )
            .with_effects(registry_effects);
        let mut global_binders = vec![None; surface_definitions.len()];
        for declaration in &surface.declaration_order {
            match *declaration {
                SurfaceDeclarationIndex::Global(index) => {
                    let definition = surface_definitions.get(index).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the surface declaration order contains an invalid global index",
                        )
                        .with_context(ResolveContext::DeclarationOrder {
                            kind: "global",
                            problem: "invalid-index",
                        })
                    })?;
                    let binder = self.allocate_global_binder(definition)?;
                    let slot = global_binders.get_mut(index).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the resolver lost a global binder slot",
                        )
                    })?;
                    *slot = Some(binder);
                }
                SurfaceDeclarationIndex::Implementation(index) => {
                    let implementation = surface.implementations.get(index).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the surface declaration order contains an invalid impl index",
                        )
                        .with_context(ResolveContext::DeclarationOrder {
                            kind: "implementation",
                            problem: "invalid-index",
                        })
                    })?;
                    let pending = pending_implementations.get_mut(index).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the resolver lost an implementation plan",
                        )
                    })?;
                    for group in &mut pending.method_groups {
                        let first = implementation
                            .equations
                            .get(group.equations.start)
                            .ok_or_else(|| {
                                error(
                                    ResolveReason::InternalState,
                                    implementation.span,
                                    "an implementation method group is empty",
                                )
                            })?;
                        group.binder =
                            Some(self.allocate_binder(&first.name.text, first.name.span)?);
                    }
                }
                SurfaceDeclarationIndex::Type(_)
                | SurfaceDeclarationIndex::Interface(_)
                | SurfaceDeclarationIndex::Effect(_) => {}
            }
        }

        let global_binders = global_binders
            .into_iter()
            .enumerate()
            .map(|(index, binder)| {
                binder.ok_or_else(|| {
                    error(
                        ResolveReason::InternalState,
                        surface_definitions[index].span,
                        "the resolver did not allocate a global binder",
                    )
                })
            })
            .collect::<Result<Vec<_>, _>>()?;

        let mut definitions =
            ResolvedDefinitionBuffer(Vec::with_capacity(surface_definitions.len()));
        for ((definition, global), type_parameters) in surface_definitions
            .iter()
            .zip(global_binders)
            .zip(global_type_parameters)
        {
            let type_scope_checkpoint = self.type_scopes.len();
            self.type_scopes.push(
                type_parameters
                    .iter()
                    .map(|parameter| (parameter.spelling.clone(), parameter.id))
                    .collect(),
            );
            let kind = (|| -> Result<ResolvedDefinitionKind, ResolveError> {
                let kind = match &definition.kind {
                    SurfaceDefinitionKind::Equational(equational) => {
                        let annotation = ResolvedTypeOccurrenceOwner::new(
                            self.resolve_type(&equational.interface.annotation)?,
                        );
                        let requirements = ResolvedRequirementBuffer(
                            self.resolve_requirements(
                                RequirementOwner::Global(global.id),
                                &equational.interface.requirements,
                            )?
                            .into_vec(),
                        );
                        let mut equations =
                            ResolvedEquationBuffer(Vec::with_capacity(equational.equations.len()));
                        for equation in &equational.equations {
                            let scope_checkpoint = self.scopes.len();
                            let (patterns, binders) =
                                self.resolve_pattern_vector(&equation.patterns)?;
                            let patterns = ResolvedPatternBuffer(patterns);
                            self.push_binder_scope_many(&binders);
                            let resolved_body = self
                                .resolve_expr(&equation.body)
                                .map(ResolvedExpressionOwner::new);
                            self.scopes.truncate(scope_checkpoint);
                            let resolved_body = resolved_body?;
                            equations.0.push(ResolvedEquation {
                                name: crate::resolved::ResolvedEquationHead {
                                    binder: global.id,
                                    spelling: equation.name.text.clone(),
                                    origin: Origin::Source(equation.name.span),
                                },
                                patterns: patterns.into_vec(),
                                body: resolved_body.into_inner(),
                                span: equation.span,
                            });
                        }
                        if equations.is_empty() {
                            return Err(error(
                                ResolveReason::InternalState,
                                definition.span,
                                "the resolver produced no equation",
                            )
                            .with_context(ResolveContext::WorkState {
                                part: "equation",
                                problem: "missing",
                            }));
                        }
                        ResolvedDefinitionKind::Equational(ResolvedEquationalGlobal {
                            interface: ResolvedExternalInterface {
                                name: global.clone(),
                                annotation: annotation.into_inner(),
                                requirements: requirements.into_boxed_slice(),
                                type_parameters: type_parameters.into_boxed_slice(),
                                span: equational.interface.span,
                            },
                            equations: equations.into_vec(),
                        })
                    }
                    SurfaceDefinitionKind::InlineOperational(operational) => {
                        let requirements = ResolvedRequirementBuffer(
                            self.resolve_requirements(
                                RequirementOwner::Global(global.id),
                                &operational.header.requirements,
                            )?
                            .into_vec(),
                        );
                        let surface_patterns = operational
                            .header
                            .parameters
                            .iter()
                            .map(|parameter| parameter.pattern.clone())
                            .collect::<Vec<_>>();
                        let (patterns, binders) = self.resolve_pattern_vector(&surface_patterns)?;
                        let mut patterns = ResolvedPatternBuffer(patterns);
                        let scope_checkpoint = self.scopes.len();
                        self.push_binder_scope_many(&binders);
                        let resolved_body = self.resolve_block(&operational.body).map(|body| {
                            ResolvedExpressionOwner::new(ResolvedExpr {
                                kind: ResolvedExprKind::Block(body),
                                span: operational.body.span,
                            })
                        });
                        self.scopes.truncate(scope_checkpoint);
                        let body = resolved_body?;
                        let mut parameters = ResolvedTypedPatternBuffer(Vec::new());
                        parameters.0.try_reserve(patterns.0.len()).map_err(|_| {
                            error(
                                ResolveReason::TypeResourceExhausted,
                                operational.header.span,
                                "operational parameter storage exceeded its work budget",
                            )
                        })?;
                        patterns.0.reverse();
                        for parameter in &operational.header.parameters {
                            let pattern = patterns.pop().ok_or_else(|| {
                                error(
                                    ResolveReason::InternalState,
                                    parameter.span,
                                    "the resolver lost an operational parameter pattern",
                                )
                                .with_context(
                                    ResolveContext::WorkState {
                                        part: "operational-pattern",
                                        problem: "missing",
                                    },
                                )
                            })?;
                            let pattern = ResolvedPatternOwner::new(pattern);
                            let annotation = ResolvedTypeOccurrenceOwner::new(
                                self.resolve_type(&parameter.annotation)?,
                            );
                            parameters.0.push(ResolvedTypedPattern {
                                pattern: pattern.into_inner(),
                                annotation: annotation.into_inner(),
                                span: parameter.span,
                            });
                        }
                        if !patterns.0.is_empty() {
                            return Err(error(
                                ResolveReason::InternalState,
                                operational.header.span,
                                "the resolver retained an extra operational parameter pattern",
                            )
                            .with_context(ResolveContext::WorkState {
                                part: "operational-pattern",
                                problem: "extra",
                            }));
                        }
                        if parameters.is_empty() {
                            return Err(error(
                                ResolveReason::InternalState,
                                operational.header.span,
                                "the resolver produced no operational parameter",
                            )
                            .with_context(ResolveContext::WorkState {
                                part: "operational-parameter",
                                problem: "missing",
                            }));
                        }
                        let result_type = ResolvedTypeOccurrenceOwner::new(
                            self.resolve_type(&operational.header.result_type)?,
                        );
                        let (
                            result_effects,
                            result_effect_argument_provenance,
                            result_effect_argument_roots,
                        ) = operational
                            .header
                            .result_effects
                            .as_ref()
                            .map(|effects| self.resolve_effect_row(effects))
                            .transpose()?
                            .unwrap_or_else(|| {
                                (
                                    EffectRow::empty(),
                                    Vec::new().into_boxed_slice(),
                                    Vec::new().into_boxed_slice(),
                                )
                            });
                        if !matches!(body.kind, ResolvedExprKind::Block(_)) {
                            return Err(error(
                                ResolveReason::InternalState,
                                operational.body.span,
                                "the resolver produced the wrong operational body payload",
                            )
                            .with_context(ResolveContext::WorkState {
                                part: "operational-body",
                                problem: "wrong",
                            }));
                        }
                        let ResolvedExprKind::Block(body) = body.into_inner().kind else {
                            unreachable!("the operational body shape was checked")
                        };
                        ResolvedDefinitionKind::InlineOperational(ResolvedInlineOperationalGlobal {
                            header: ResolvedInlineOperationalHeader {
                                name: global.clone(),
                                parameters: parameters.into_vec(),
                                result_type: result_type.into_inner(),
                                result_effects,
                                result_effect_argument_provenance,
                                result_effect_argument_roots,
                                requirements: requirements.into_boxed_slice(),
                                type_parameters: type_parameters.into_boxed_slice(),
                                span: operational.header.span,
                            },
                            body,
                        })
                    }
                };
                Ok(kind)
            })();
            self.type_scopes.truncate(type_scope_checkpoint);
            let kind = kind?;
            definitions.0.push(ResolvedDefinition {
                kind,
                span: definition.span,
            });
        }

        let implementations = ResolvedImplementationBuffer(self.resolve_implementations(
            &surface.implementations,
            pending_implementations,
            surface.span,
        )?);

        let lexical_nominals = std::mem::replace(
            &mut self.lexical_nominals,
            ResolvedNominalOwnerBuffer(Vec::new()),
        );
        let lexical_constructors = std::mem::replace(
            &mut self.lexical_constructors,
            ResolvedConstructorOwnerBuffer(Vec::new()),
        );
        let lexical_parameters = std::mem::replace(
            &mut self.lexical_nominal_parameters,
            ResolvedNominalParameterOwnerBuffer(Vec::new()),
        );
        let lexical_method_parameters = std::mem::take(&mut self.lexical_method_parameters.0);
        let registry = Arc::new(
            registry
                .with_additional_type_variables(lexical_method_parameters)
                .with_lexical_nominals_with_budget(
                    lexical_nominals.into_vec(),
                    lexical_constructors.into_vec(),
                    lexical_parameters.into_vec(),
                    &mut self.type_work,
                )
                .map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        surface.span,
                        "lexical nominal registry publication exceeded its type-work budget",
                    )
                })?,
        );

        Ok(ResolvedDeclarations {
            registry,
            constructor_payload_provenance,
            interfaces: std::mem::replace(
                &mut self.resolved_interfaces,
                ResolvedInterfaceBuffer(Vec::new()),
            )
            .into_vec(),
            effects,
            implementations: implementations.into_vec(),
            definitions: definitions.into_vec(),
        })
    }

    fn resolve_implementations(
        &mut self,
        declarations: &[SurfaceImplementation],
        pending: Vec<PendingImplementation>,
        module_span: crate::source::Span,
    ) -> Result<Vec<ResolvedImplementation>, ResolveError> {
        if declarations.len() != pending.len() {
            return Err(error(
                ResolveReason::InternalState,
                module_span,
                "the resolver retained mismatched implementation plans",
            ));
        }

        let mut implementations =
            ResolvedImplementationBuffer(Vec::with_capacity(declarations.len()));
        for (implementation, pending) in declarations.iter().zip(pending) {
            let type_scope_checkpoint = self.type_scopes.len();
            self.type_scopes.push(
                pending
                    .head_parameters
                    .iter()
                    .chain(&pending.prerequisite_only_parameters)
                    .map(|parameter| (parameter.spelling.clone(), parameter.id))
                    .collect(),
            );

            let result = (|| -> Result<ResolvedImplementation, ResolveError> {
                let head = self.resolve_interface_application(&implementation.head)?;
                if head.interface.id.module().is_builtin_resource() {
                    return Err(error(
                        ResolveReason::SealedProvider,
                        implementation.span,
                        "only resource acquisition may introduce the builtin cell provider",
                    ));
                }
                let prerequisites = ResolvedRequirementBuffer(
                    self.resolve_requirements(
                        RequirementOwner::Impl(pending.id),
                        &implementation.prerequisites,
                    )?
                    .into_vec(),
                );
                let mut method_groups = ResolvedImplementationMethodGroupBuffer(Vec::new());
                method_groups
                    .0
                    .try_reserve(pending.method_groups.len())
                    .map_err(|_| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            implementation.span,
                            "implementation method-group storage exceeded its work budget",
                        )
                    })?;
                for group in pending.method_groups {
                    let equations = implementation
                        .equations
                        .get(group.equations.clone())
                        .ok_or_else(|| {
                            error(
                                ResolveReason::InternalState,
                                implementation.span,
                                "the resolver retained an invalid method-group range",
                            )
                        })?;
                    let first = equations.first().ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            implementation.span,
                            "the resolver retained an empty method group",
                        )
                    })?;
                    let last = equations.last().ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            implementation.span,
                            "the resolver retained an empty method group",
                        )
                    })?;
                    let span = first.span.cover(last.span).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            implementation.span,
                            "one implementation method group crosses source files",
                        )
                    })?;
                    let binder = group.binder.ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            first.span,
                            "the resolver did not allocate a hidden method binder",
                        )
                    })?;
                    let method = self.method_names.get(&first.name.text).and_then(|binding| {
                        match binding.term {
                            ResolvedTermName::Method(method) => Some(method),
                            ResolvedTermName::Global(_) => None,
                        }
                    });
                    let identity = method.map(|method| ImplMethodId::new(pending.id, method));
                    let mut resolved_equations =
                        ResolvedEquationBuffer(Vec::with_capacity(equations.len()));
                    for equation in equations {
                        let scope_checkpoint = self.scopes.len();
                        let (patterns, binders) =
                            self.resolve_pattern_vector(&equation.patterns)?;
                        let patterns = ResolvedPatternBuffer(patterns);
                        self.push_binder_scope_many(&binders);
                        let body = self
                            .resolve_expr(&equation.body)
                            .map(ResolvedExpressionOwner::new);
                        self.scopes.truncate(scope_checkpoint);
                        let body = body?;
                        resolved_equations.0.push(ResolvedEquation {
                            name: crate::resolved::ResolvedEquationHead {
                                binder: binder.id,
                                spelling: equation.name.text.clone(),
                                origin: Origin::Source(equation.name.span),
                            },
                            patterns: patterns.into_vec(),
                            body: body.into_inner(),
                            span: equation.span,
                        });
                    }
                    method_groups.0.push(ResolvedImplementationMethodGroup {
                        contextual_parameters: Box::new([]),
                        method,
                        identity,
                        binder,
                        equations: resolved_equations.into_boxed_slice(),
                        span,
                    });
                }

                Ok(ResolvedImplementation {
                    id: pending.id,
                    public: implementation.public,
                    head,
                    head_parameters: pending.head_parameters.into_boxed_slice(),
                    prerequisite_only_parameters: pending
                        .prerequisite_only_parameters
                        .into_boxed_slice(),
                    prerequisites: prerequisites.into_boxed_slice(),
                    method_groups: method_groups.into_boxed_slice(),
                    span: implementation.span,
                })
            })();

            self.type_scopes.truncate(type_scope_checkpoint);
            implementations.0.push(result?);
        }
        Ok(implementations.into_vec())
    }

    fn install_nominal_identities(
        &mut self,
        type_declarations: &[SurfaceTypeDeclaration],
    ) -> Result<Vec<NominalDeclarationIdentity>, ResolveError> {
        let mut first_types = HashMap::new();
        let mut nominal_ids = Vec::with_capacity(type_declarations.len());
        for (index, declaration) in type_declarations.iter().enumerate() {
            if let Some(first) =
                first_types.insert(declaration.name.text.as_str(), declaration.name.span)
            {
                let mut diagnostic = Diagnostic::new(
                    ResolveReason::DuplicateType,
                    SourceLabel::new(
                        declaration.name.span,
                        "this nominal type name is already defined",
                    ),
                );
                diagnostic
                    .related
                    .push(SourceLabel::new(first, "the first nominal type is here"));
                diagnostic.found = Some(declaration.name.text.clone());
                return Err(diagnostic.into());
            }
            if self.module_aliases.contains_key(&declaration.name.text)
                || self.type_names.contains_key(&declaration.name.text)
                || self.interface_names.contains_key(&declaration.name.text)
            {
                return Err(import_conflict(
                    declaration.name.span,
                    &declaration.name.text,
                ));
            }
            let index = u32::try_from(index).map_err(|_| {
                error(
                    ResolveReason::InternalState,
                    declaration.span,
                    "the file contains too many type declarations",
                )
                .with_context(ResolveContext::IdentityExhaustion(
                    ResolveIdentitySpace::Nominal,
                ))
            })?;
            let id = NominalTypeId::new(self.module, index);
            self.type_names.insert(declaration.name.text.clone(), id);
            nominal_ids.push(id);
        }

        let mut first_constructors = HashMap::new();
        let mut identities = Vec::with_capacity(type_declarations.len());
        for (declaration, owner) in type_declarations.iter().zip(&nominal_ids) {
            if declaration.declaration_kind == SurfaceNominalDeclarationKind::Newtype {
                let _ = validate_newtype_shape(declaration)?;
            }
            let mut owned = Vec::with_capacity(declaration.constructors.len());
            for (index, constructor) in declaration.constructors.iter().enumerate() {
                if let Some(first) =
                    first_constructors.insert(constructor.name.text.as_str(), constructor.name.span)
                {
                    let mut diagnostic = Diagnostic::new(
                        ResolveReason::DuplicateConstructor,
                        SourceLabel::new(
                            constructor.name.span,
                            "this constructor name is already defined",
                        ),
                    );
                    diagnostic
                        .related
                        .push(SourceLabel::new(first, "the first constructor is here"));
                    diagnostic.found = Some(constructor.name.text.clone());
                    return Err(diagnostic.into());
                }
                if self.module_aliases.contains_key(&constructor.name.text)
                    || self.constructor_names.contains_key(&constructor.name.text)
                    || self.method_names.contains_key(&constructor.name.text)
                    || self
                        .scopes
                        .first()
                        .is_some_and(|scope| scope.contains_key(&constructor.name.text))
                {
                    return Err(import_conflict(
                        constructor.name.span,
                        &constructor.name.text,
                    ));
                }
                let index = u32::try_from(index).map_err(|_| {
                    error(
                        ResolveReason::InternalState,
                        constructor.span,
                        "the declaration contains too many constructors",
                    )
                    .with_context(ResolveContext::IdentityExhaustion(
                        ResolveIdentitySpace::Constructor,
                    ))
                })?;
                let id = ConstructorId::new(*owner, index);
                self.constructor_names
                    .insert(constructor.name.text.clone(), id);
                owned.push(id);
            }
            identities.push(NominalDeclarationIdentity {
                id: *owner,
                constructors: owned,
            });
        }
        Ok(identities)
    }

    fn allocate_nominal_type_parameters(
        &mut self,
        declaration: &SurfaceTypeDeclaration,
    ) -> Result<Vec<ResolvedTypeVariable>, ResolveError> {
        validate_explicit_type_parameters(Some(&declaration.parameters))?;
        let mut parameters = Vec::with_capacity(declaration.parameters.len());
        for parameter in &declaration.parameters {
            parameters.push(self.allocate_type_variable(
                &parameter.name,
                parameter.kind.as_ref(),
                Kind::Type,
            )?);
        }
        Ok(parameters)
    }

    fn resolve_newtype_representation(
        &mut self,
        representation: &SurfaceType,
    ) -> Result<(IterativeTypeOwner, ResolvedTypeProvenance), ResolveError> {
        let ResolvedType {
            ty,
            provenance,
            origin,
            ..
        } = self.resolve_type(representation)?;
        discard_origin_iteratively(origin);
        Ok((IterativeTypeOwner::new(ty), provenance))
    }

    fn resolve_local_newtype(
        &mut self,
        declaration: &SurfaceTypeDeclaration,
    ) -> Result<NominalTypeId, ResolveError> {
        if declaration.declaration_kind != SurfaceNominalDeclarationKind::Newtype {
            return Err(error(
                ResolveReason::InternalState,
                declaration.span,
                "a block-local nominal is not a newtype",
            ));
        }
        let (constructor, representation) = validate_newtype_shape(declaration)?;

        let parameters = self.allocate_nominal_type_parameters(declaration)?;
        let type_scope_checkpoint = self.type_scopes.len();
        self.type_scopes.push(
            parameters
                .iter()
                .map(|parameter| (parameter.spelling.clone(), parameter.id))
                .collect(),
        );
        let resolved = self.resolve_newtype_representation(representation);
        self.type_scopes.truncate(type_scope_checkpoint);
        let (representation, provenance) = resolved?;

        self.type_work.charge(6).map_err(|()| {
            error(
                ResolveReason::TypeResourceExhausted,
                declaration.span,
                "local newtype fact retention exceeded its type-work budget",
            )
        })?;
        self.lexical_nominals.0.try_reserve(1).map_err(|_| {
            error(
                ResolveReason::TypeResourceExhausted,
                declaration.span,
                "local nominal fact storage could not be reserved",
            )
        })?;
        self.lexical_constructors.0.try_reserve(1).map_err(|_| {
            error(
                ResolveReason::TypeResourceExhausted,
                declaration.span,
                "local constructor fact storage could not be reserved",
            )
        })?;
        self.lexical_nominal_parameters
            .0
            .try_reserve(1)
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    declaration.span,
                    "local nominal parameter storage could not be reserved",
                )
            })?;
        self.nominal_parameter_counts.try_reserve(1).map_err(|_| {
            error(
                ResolveReason::TypeResourceExhausted,
                declaration.span,
                "local nominal arity storage could not be reserved",
            )
        })?;
        let nominal_scope = self.lexical_nominal_scopes.last_mut().ok_or_else(|| {
            error(
                ResolveReason::InternalState,
                declaration.span,
                "the resolver lost the local nominal scope",
            )
            .with_context(ResolveContext::MissingNominalScope)
        })?;
        nominal_scope.try_reserve(1).map_err(|_| {
            error(
                ResolveReason::TypeResourceExhausted,
                declaration.span,
                "local nominal name storage could not be reserved",
            )
        })?;
        let constructor_scope = self.lexical_constructor_scopes.last_mut().ok_or_else(|| {
            error(
                ResolveReason::InternalState,
                declaration.span,
                "the resolver lost the local constructor scope",
            )
            .with_context(ResolveContext::MissingConstructorScope)
        })?;
        constructor_scope.try_reserve(1).map_err(|_| {
            error(
                ResolveReason::TypeResourceExhausted,
                declaration.span,
                "local constructor name storage could not be reserved",
            )
        })?;

        let nominal_name = try_clone_resolution_string(
            &declaration.name.text,
            declaration.name.span,
            "local nominal name storage could not be reserved",
        )?;
        let constructor_name = try_clone_resolution_string(
            &constructor.name.text,
            constructor.name.span,
            "local constructor name storage could not be reserved",
        )?;
        let id = NominalTypeId::lexical(self.module, self.next_lexical_nominal);
        let constructor_id = ConstructorId::new(id, 0);
        let next = self.next_lexical_nominal.checked_add(1).ok_or_else(|| {
            identity_error(
                ResolveIdentitySpace::LocalNominal,
                declaration.span,
                "the program contains too many lexical nominal declarations",
            )
        })?;

        let (nominal, constructor_fact) = resolved_newtype_fact_pair(
            declaration,
            constructor,
            id,
            constructor_id,
            representation,
            provenance,
        )?;
        self.lexical_nominals.0.push(nominal);
        self.lexical_constructors.0.push(constructor_fact);
        let parameter_count = parameters.len();
        self.lexical_nominal_parameters.0.push((id, parameters));
        self.nominal_parameter_counts.insert(id, parameter_count);
        self.lexical_nominal_scopes
            .last_mut()
            .expect("the local nominal scope was reserved")
            .insert(nominal_name, id);
        self.lexical_constructor_scopes
            .last_mut()
            .expect("the local constructor scope was reserved")
            .insert(constructor_name, constructor_id);
        self.next_lexical_nominal = next;
        Ok(id)
    }

    #[cfg(test)]
    fn resolve_registry(
        &mut self,
        type_declarations: &[SurfaceTypeDeclaration],
    ) -> Result<(ResolvedRegistry, Vec<Vec<ConstructorPayloadProvenance>>), ResolveError> {
        let identities = self.install_nominal_identities(type_declarations)?;
        let mut parameters = Vec::new();
        if let Some(last) = type_declarations.last() {
            parameters
                .try_reserve_exact(type_declarations.len())
                .map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        last.span,
                        "nominal type-parameter preparation storage could not be reserved",
                    )
                })?;
        }
        for (declaration, identity) in type_declarations.iter().zip(&identities) {
            parameters.push((
                identity.id,
                self.allocate_nominal_type_parameters(declaration)?,
            ));
        }
        self.resolve_registry_with_prepared(type_declarations, identities, parameters)
    }

    fn resolve_registry_with_prepared(
        &mut self,
        type_declarations: &[SurfaceTypeDeclaration],
        identities: Vec<NominalDeclarationIdentity>,
        nominal_parameters: Vec<(NominalTypeId, Vec<ResolvedTypeVariable>)>,
    ) -> Result<(ResolvedRegistry, Vec<Vec<ConstructorPayloadProvenance>>), ResolveError> {
        debug_assert_eq!(type_declarations.len(), identities.len());
        debug_assert_eq!(type_declarations.len(), nominal_parameters.len());
        self.nominal_parameter_counts.extend(
            nominal_parameters
                .iter()
                .map(|(owner, parameters)| (*owner, parameters.len())),
        );

        let mut nominals = type_declarations
            .iter()
            .zip(&identities)
            .map(|(declaration, identity)| ResolvedNominalType {
                id: identity.id,
                declaration_kind: match declaration.declaration_kind {
                    SurfaceNominalDeclarationKind::Data => ResolvedNominalDeclarationKind::Data,
                    SurfaceNominalDeclarationKind::Newtype => {
                        ResolvedNominalDeclarationKind::Newtype
                    }
                },
                spelling: declaration.name.text.clone(),
                constructors: identity.constructors.clone().into_boxed_slice(),
                representation: None,
                representation_provenance: None,
                origin: Origin::Source(declaration.span),
            })
            .collect::<Vec<_>>();
        let discard_nominals = |nominals: &mut Vec<ResolvedNominalType>| {
            for nominal in nominals.drain(..) {
                if let Some(representation) = nominal.representation {
                    discard_type_iteratively(representation);
                }
                discard_origin_iteratively(nominal.origin);
            }
        };
        let mut constructors = ResolvedConstructorOwnerBuffer(Vec::new());
        let mut constructor_payload_provenance = Vec::new();
        if let Some(last) = type_declarations.last() {
            self.type_work
                .charge(type_declarations.len())
                .map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        last.span,
                        "nominal payload-provenance retention exceeded its type-work budget",
                    )
                })?;
            constructor_payload_provenance
                .try_reserve(type_declarations.len())
                .map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        last.span,
                        "nominal payload-provenance retention could not reserve storage",
                    )
                })?;
        }
        for (nominal_index, ((declaration, identity), (_, parameters))) in type_declarations
            .iter()
            .zip(&identities)
            .zip(&nominal_parameters)
            .enumerate()
        {
            let mut nominal_payload_provenance = Vec::new();
            self.type_work
                .charge(declaration.constructors.len())
                .map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        declaration.span,
                        "constructor payload-provenance retention exceeded its type-work budget",
                    )
                })?;
            nominal_payload_provenance
                .try_reserve(declaration.constructors.len())
                .map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        declaration.span,
                        "constructor payload-provenance retention could not reserve storage",
                    )
                })?;
            self.type_scopes.push(
                parameters
                    .iter()
                    .map(|parameter| (parameter.spelling.clone(), parameter.id))
                    .collect(),
            );
            let result = (|| -> Result<(), ResolveError> {
                for (constructor, id) in declaration.constructors.iter().zip(&identity.constructors)
                {
                    let mut field_provenance = Vec::new();
                    self.type_work
                        .charge(constructor.fields.len())
                        .map_err(|()| {
                            error(
                                ResolveReason::TypeResourceExhausted,
                                constructor.span,
                                "constructor field-provenance retention exceeded its type-work budget",
                            )
                        })?;
                    field_provenance
                        .try_reserve(constructor.fields.len())
                        .map_err(|_| {
                            error(
                                ResolveReason::TypeResourceExhausted,
                                constructor.span,
                                "constructor field provenance could not reserve storage",
                            )
                        })?;
                    let payload = match constructor.fields.as_slice() {
                        [] => None,
                        [field] => {
                            if declaration.declaration_kind
                                == SurfaceNominalDeclarationKind::Newtype
                            {
                                let (representation, provenance) =
                                    self.resolve_newtype_representation(field)?;
                                field_provenance.push(provenance);
                                Some(representation)
                            } else {
                                let ResolvedType {
                                    ty,
                                    provenance,
                                    origin,
                                    ..
                                } = self.resolve_type(field)?;
                                field_provenance.push(provenance);
                                discard_origin_iteratively(origin);
                                Some(IterativeTypeOwner::new(ty))
                            }
                        }
                        fields => {
                            self.type_work.charge(1).map_err(|()| {
                                error(
                                    ResolveReason::TypeResourceExhausted,
                                    constructor.span,
                                    "constructor payload synthesis exceeded its type-work budget",
                                )
                            })?;
                            let mut elements = Vec::new();
                            elements.try_reserve(fields.len()).map_err(|_| {
                                error(
                                    ResolveReason::TypeResourceExhausted,
                                    constructor.span,
                                    "constructor payload storage exceeded its type-work budget",
                                )
                            })?;
                            for field in fields {
                                let ResolvedType {
                                    ty,
                                    provenance,
                                    origin,
                                    ..
                                } = self.resolve_type(field)?;
                                field_provenance.push(provenance);
                                discard_origin_iteratively(origin);
                                elements.push(IterativeTypeOwner::new(ty));
                            }
                            Some(IterativeTypeOwner::new(Type::Tuple(
                                elements
                                    .into_iter()
                                    .map(IterativeTypeOwner::into_inner)
                                    .collect::<Vec<_>>()
                                    .into_boxed_slice(),
                            )))
                        }
                    };
                    let constructor_payload = if declaration.declaration_kind
                        == SurfaceNominalDeclarationKind::Newtype
                    {
                        let representation = payload.ok_or_else(|| {
                            error(
                                ResolveReason::InternalState,
                                constructor.span,
                                "a resolved newtype has no representation",
                            )
                        })?;
                        let representation_provenance =
                            field_provenance.first().cloned().ok_or_else(|| {
                                error(
                                    ResolveReason::InternalState,
                                    constructor.span,
                                    "a resolved newtype has no representation provenance",
                                )
                            })?;
                        let (nominal, constructor_fact) = resolved_newtype_fact_pair(
                            declaration,
                            constructor,
                            identity.id,
                            *id,
                            representation,
                            representation_provenance,
                        )?;
                        let displaced = std::mem::replace(&mut nominals[nominal_index], nominal);
                        discard_origin_iteratively(displaced.origin);
                        constructors.0.push(constructor_fact);
                        nominal_payload_provenance.push(ConstructorPayloadProvenance {
                            constructor: *id,
                            fields: field_provenance,
                        });
                        continue;
                    } else {
                        payload.map(IterativeTypeOwner::into_inner)
                    };
                    constructors.0.push(ResolvedConstructor {
                        id: *id,
                        owner: identity.id,
                        spelling: constructor.name.text.clone(),
                        payload: constructor_payload,
                        origin: Origin::Source(constructor.span),
                    });
                    nominal_payload_provenance.push(ConstructorPayloadProvenance {
                        constructor: *id,
                        fields: field_provenance,
                    });
                }
                Ok(())
            })();
            let _ = self.type_scopes.pop();
            if let Err(error) = result {
                discard_nominals(&mut nominals);
                return Err(error);
            }
            constructor_payload_provenance.push(nominal_payload_provenance);
        }
        let registry = ResolvedRegistry::new(nominals, constructors.into_vec())
            .with_type_parameters_with_budget(nominal_parameters, &mut self.type_work)
            .map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    type_declarations
                        .last()
                        .expect("nonempty nominal parameters have a declaration")
                        .span,
                    "nominal parameter retention exceeded its type-work budget",
                )
            })?;
        Ok((registry, constructor_payload_provenance))
    }

    fn push_binder_scope_many(&mut self, binders: &[Binder]) {
        self.scopes.push(
            binders
                .iter()
                .map(|binder| {
                    (
                        binder.spelling.clone(),
                        ResolvedTermBinding::local(ResolvedTermName::Global(binder.id)),
                    )
                })
                .collect(),
        );
    }

    fn resolve_type(&mut self, surface: &SurfaceType) -> Result<ResolvedType, ResolveError> {
        enum ApplicationHead {
            Nominal(NominalTypeId),
            Variable(TypeVariableId),
        }
        enum Task<'a> {
            Visit(&'a SurfaceType),
            Sequence(std::slice::Iter<'a, SurfaceType>),
            Tuple(usize, crate::source::Span),
            Function(
                crate::source::Span,
                Option<&'a crate::surface::SurfaceEffectRow>,
                usize,
            ),
            EffectInstances(std::slice::Iter<'a, crate::surface::SurfaceEffectInstance>),
            EffectArguments(std::slice::Iter<'a, SurfaceType>),
            Application(
                ApplicationHead,
                &'a [SurfaceType],
                crate::source::Span,
                crate::source::Span,
            ),
        }
        let mut tasks = vec![Task::Visit(surface)];
        let mut completed = ResolvedTypeBuffer(Vec::new());
        let mut provenance = Vec::new();
        while let Some(task) = tasks.pop() {
            #[cfg(test)]
            {
                self.max_type_pending_tasks = self.max_type_pending_tasks.max(tasks.len() + 1);
            }
            match task {
                Task::Visit(current) => {
                    self.type_work.charge(1).map_err(|()| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            current.span,
                            "source type resolution exceeded its work budget",
                        )
                    })?;
                    match &current.kind {
                        SurfaceTypeKind::Int => {
                            provenance.push(ResolvedTypeProvenanceNode::Fact(current.span));
                            completed.push((Type::Int, provenance.len() - 1));
                        }
                        SurfaceTypeKind::Bool => {
                            provenance.push(ResolvedTypeProvenanceNode::Fact(current.span));
                            completed.push((Type::Bool, provenance.len() - 1));
                        }
                        SurfaceTypeKind::Unit => {
                            provenance.push(ResolvedTypeProvenanceNode::Fact(current.span));
                            completed.push((Type::Unit, provenance.len() - 1));
                        }
                        SurfaceTypeKind::Named(name) => {
                            if matches!(name, SurfaceReference::Unqualified(_))
                                && let Some(variable) = self
                                    .type_scopes
                                    .iter()
                                    .rev()
                                    .find_map(|scope| scope.get(&name.member().text))
                            {
                                provenance.push(ResolvedTypeProvenanceNode::Fact(current.span));
                                completed.push((Type::Variable(*variable), provenance.len() - 1));
                                continue;
                            }
                            let nominal = self.nominal_reference(name)?;
                            let id = nominal.id;
                            provenance.push(ResolvedTypeProvenanceNode::Fact(current.span));
                            completed.push((Type::Nominal(id), provenance.len() - 1));
                        }
                        SurfaceTypeKind::Application {
                            constructor,
                            arguments,
                        } => {
                            let head = if matches!(constructor, SurfaceReference::Unqualified(_))
                                && let Some(variable) = self
                                    .type_scopes
                                    .iter()
                                    .rev()
                                    .find_map(|scope| scope.get(&constructor.member().text))
                            {
                                ApplicationHead::Variable(*variable)
                            } else {
                                ApplicationHead::Nominal(self.nominal_reference(constructor)?.id)
                            };
                            tasks.push(Task::Application(
                                head,
                                arguments,
                                current.span,
                                constructor.span(),
                            ));
                            tasks.push(Task::Sequence(arguments.iter()));
                        }
                        SurfaceTypeKind::Tuple(elements) => {
                            tasks.push(Task::Tuple(elements.len(), current.span));
                            tasks.push(Task::Sequence(elements.iter()));
                        }
                        SurfaceTypeKind::Function(function) => {
                            let effect_argument_count = function
                                .effects
                                .iter()
                                .flat_map(|row| row.effects.iter())
                                .try_fold(0usize, |count, instance| {
                                    count.checked_add(instance.arguments.len())
                                })
                                .ok_or_else(|| {
                                    error(
                                        ResolveReason::TypeResourceExhausted,
                                        current.span,
                                        "effect-argument provenance exceeded its type-work budget",
                                    )
                                })?;
                            tasks.push(Task::Function(
                                current.span,
                                function.effects.as_ref(),
                                effect_argument_count,
                            ));
                            if let Some(effects) = &function.effects {
                                tasks.push(Task::EffectInstances(effects.effects.iter()));
                            }
                            tasks.push(Task::Visit(&function.codomain));
                            tasks.push(Task::Visit(&function.domain));
                        }
                    }
                }
                Task::Sequence(mut remaining) => {
                    if let Some(next) = remaining.next() {
                        tasks.push(Task::Sequence(remaining));
                        tasks.push(Task::Visit(next));
                    }
                }
                Task::EffectInstances(mut remaining) => {
                    if let Some(next) = remaining.next() {
                        tasks.push(Task::EffectInstances(remaining));
                        tasks.push(Task::EffectArguments(next.arguments.iter()));
                    }
                }
                Task::EffectArguments(mut remaining) => {
                    if let Some(next) = remaining.next() {
                        tasks.push(Task::EffectArguments(remaining));
                        tasks.push(Task::Visit(next));
                    }
                }
                Task::Tuple(count, span) => {
                    let split = completed.len().checked_sub(count).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the resolver lost a tuple type element",
                        )
                        .with_context(ResolveContext::WorkState {
                            part: "tuple-type-element",
                            problem: "missing",
                        })
                    })?;
                    let elements = completed.split_off(split);
                    let roots = elements
                        .iter()
                        .map(|(_, root)| *root)
                        .collect::<Vec<_>>()
                        .into_boxed_slice();
                    provenance.push(ResolvedTypeProvenanceNode::Tuple {
                        span,
                        elements: roots,
                    });
                    completed.push((
                        Type::Tuple(
                            elements
                                .into_vec()
                                .into_iter()
                                .map(|(ty, _)| ty)
                                .collect::<Vec<_>>()
                                .into_boxed_slice(),
                        ),
                        provenance.len() - 1,
                    ));
                }
                Task::Function(span, effects, effect_argument_count) => {
                    let mut effect_arguments = completed.split_off(
                        completed
                            .len()
                            .checked_sub(effect_argument_count)
                            .ok_or_else(|| {
                                error(
                                    ResolveReason::InternalState,
                                    surface.span,
                                    "the resolver lost an effect-row type argument",
                                )
                                .with_context(
                                    ResolveContext::WorkState {
                                        part: "effect-row-argument",
                                        problem: "missing",
                                    },
                                )
                            })?,
                    );
                    let (codomain, codomain_root) = completed.pop_owned().ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the resolver lost a function codomain",
                        )
                        .with_context(ResolveContext::WorkState {
                            part: "function-codomain",
                            problem: "missing",
                        })
                    })?;
                    let (domain, domain_root) = completed.pop_owned().ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the resolver lost a function domain",
                        )
                        .with_context(ResolveContext::WorkState {
                            part: "function-domain",
                            problem: "missing",
                        })
                    })?;
                    let (ty, effect_argument_roots) =
                        if let Some(effects) = effects {
                            self.type_work.charge(effects.effects.len()).map_err(|()| {
                                error(
                                    ResolveReason::TypeResourceExhausted,
                                    effects.span,
                                    "effect-row storage exceeded its type-work budget",
                                )
                            })?;
                            let mut written = Vec::new();
                            written
                                .try_reserve_exact(effects.effects.len())
                                .map_err(|_| {
                                    error(
                                        ResolveReason::TypeResourceExhausted,
                                        effects.span,
                                        "effect-row storage exceeded its type-work budget",
                                    )
                                })?;
                            for source_instance in effects.effects.iter().rev() {
                                let count = source_instance.arguments.len();
                                self.type_work.charge(count.checked_mul(2).ok_or_else(|| {
                                error(
                                    ResolveReason::TypeResourceExhausted,
                                    source_instance.span,
                                    "effect-argument provenance exceeded its type-work budget",
                                )
                            })?).map_err(|()| {
                                error(
                                    ResolveReason::TypeResourceExhausted,
                                    source_instance.span,
                                    "effect-argument storage exceeded its type-work budget",
                                )
                            })?;
                                let mut arguments = Vec::new();
                                let mut roots = Vec::new();
                                arguments.try_reserve_exact(count).map_err(|_| {
                                    error(
                                        ResolveReason::TypeResourceExhausted,
                                        source_instance.span,
                                        "effect-argument storage exceeded its type-work budget",
                                    )
                                })?;
                                roots.try_reserve_exact(count).map_err(|_| {
                                    error(
                                        ResolveReason::TypeResourceExhausted,
                                        source_instance.span,
                                        "effect-argument provenance could not reserve storage",
                                    )
                                })?;
                                for _ in source_instance.arguments.iter().rev() {
                                    let (argument, root) =
                                        effect_arguments.pop_owned().ok_or_else(|| {
                                            error(
                                                ResolveReason::InternalState,
                                                source_instance.span,
                                                "the resolver lost an effect-row type argument",
                                            )
                                            .with_context(ResolveContext::WorkState {
                                                part: "effect-row-argument",
                                                problem: "missing",
                                            })
                                        })?;
                                    arguments.push(argument);
                                    roots.push(root);
                                }
                                arguments.reverse();
                                roots.reverse();
                                written.push((
                                    EffectInstance::new(
                                        self.effect_reference(&source_instance.effect)?,
                                        arguments
                                            .into_iter()
                                            .map(IterativeTypeOwner::into_inner)
                                            .collect::<Vec<_>>()
                                            .into_boxed_slice(),
                                    ),
                                    source_instance.span,
                                    roots.into_boxed_slice(),
                                ));
                            }
                            written.reverse();
                            if !effect_arguments.is_empty() {
                                return Err(error(
                                    ResolveReason::InternalState,
                                    effects.span,
                                    "the resolver retained an extra effect-row type argument",
                                )
                                .with_context(
                                    ResolveContext::WorkState {
                                        part: "effect-row-argument",
                                        problem: "extra",
                                    },
                                ));
                            }
                            let tail = effects
                                .tail
                                .as_ref()
                                .map(|tail| {
                                    self.type_scopes
                                        .iter()
                                        .rev()
                                        .find_map(|scope| scope.get(&tail.text))
                                        .copied()
                                        .map(EffectRowVariable::rigid)
                                        .ok_or_else(|| {
                                            lookup_error(
                                                ResolveContext::EffectRowParameter,
                                                tail.span,
                                                &tail.text,
                                                "this effect-row tail parameter is not declared",
                                            )
                                        })
                                })
                                .transpose()?;
                            let (row, roots) = build_source_effect_row_with_provenance(
                                written,
                                tail,
                                effects.span,
                                &mut self.type_work,
                            )?;
                            (
                                Type::function_computation(
                                    domain.into_inner(),
                                    ComputationType::new(codomain.into_inner(), row),
                                ),
                                roots,
                            )
                        } else {
                            if effect_argument_count != 0 || !effect_arguments.is_empty() {
                                return Err(error(
                                    ResolveReason::InternalState,
                                    span,
                                    "a pure function retained effect-argument provenance",
                                ));
                            }
                            (
                                Type::Function(
                                    Box::new(domain.into_inner()),
                                    Box::new(codomain.into_inner()),
                                ),
                                Vec::<usize>::new().into_boxed_slice(),
                            )
                        };
                    provenance.push(ResolvedTypeProvenanceNode::Function {
                        span,
                        domain: domain_root,
                        codomain: codomain_root,
                        effect_arguments: effect_argument_roots,
                    });
                    completed.push((ty, provenance.len() - 1));
                }
                Task::Application(head, source_arguments, span, constructor_span) => {
                    let count = source_arguments.len();
                    self.type_work.charge(count).map_err(|()| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            span,
                            "source type resolution exceeded its work budget",
                        )
                    })?;
                    let split = completed.len().checked_sub(count).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            surface.span,
                            "the resolver lost a type argument",
                        )
                        .with_context(ResolveContext::WorkState {
                            part: "type-argument",
                            problem: "missing",
                        })
                    })?;
                    let arguments = completed.split_off(split);
                    provenance.push(ResolvedTypeProvenanceNode::Fact(constructor_span));
                    let mut function = match head {
                        ApplicationHead::Nominal(owner) => Type::Nominal(owner),
                        ApplicationHead::Variable(variable) => Type::Variable(variable),
                    };
                    let mut function_root = provenance.len() - 1;
                    for ((argument, argument_root), source_argument) in
                        arguments.into_vec().into_iter().zip(source_arguments)
                    {
                        provenance.push(ResolvedTypeProvenanceNode::Application {
                            span,
                            function: function_root,
                            argument: argument_root,
                            argument_span: source_argument.span,
                        });
                        function = Type::Application(Box::new(function), Box::new(argument));
                        function_root = provenance.len() - 1;
                    }
                    completed.push((function, function_root));
                }
            }
        }
        if completed.len() != 1 {
            return Err(error(
                ResolveReason::InternalState,
                surface.span,
                "the resolver retained incomplete type state",
            )
            .with_context(ResolveContext::WorkState {
                part: "type",
                problem: "incomplete",
            }));
        }
        let (ty, root) = completed.pop_owned().ok_or_else(|| {
            error(
                ResolveReason::InternalState,
                surface.span,
                "the resolver produced no type",
            )
            .with_context(ResolveContext::WorkState {
                part: "type",
                problem: "missing",
            })
        })?;
        Ok(ResolvedType {
            ty: ty.into_inner(),
            provenance: ResolvedTypeProvenance::new(provenance, root),
            origin: Origin::Source(surface.span),
            span: surface.span,
        })
    }

    fn resolve_pattern_vector(
        &mut self,
        patterns: &[SurfacePattern],
    ) -> Result<(Vec<ResolvedPattern>, Vec<Binder>), ResolveError> {
        let mut seen = HashMap::new();
        let mut binders = Vec::new();
        let patterns = patterns
            .iter()
            .map(|pattern| self.resolve_pattern(pattern, &mut seen, &mut binders))
            .collect::<Result<Vec<_>, _>>()?;
        Ok((patterns, binders))
    }

    fn resolve_pattern(
        &mut self,
        pattern: &SurfacePattern,
        seen: &mut HashMap<String, crate::source::Span>,
        binders: &mut Vec<Binder>,
    ) -> Result<ResolvedPattern, ResolveError> {
        let kind = match &pattern.kind {
            SurfacePatternKind::Binder(surface) => {
                if let Some(first) = seen.insert(surface.name.text.clone(), surface.name.span) {
                    let mut diagnostic = Diagnostic::new(
                        ResolveReason::DuplicatePatternBinder,
                        SourceLabel::new(
                            surface.name.span,
                            "this pattern binder is already defined",
                        ),
                    );
                    diagnostic
                        .related
                        .push(SourceLabel::new(first, "the first pattern binder is here"));
                    diagnostic.found = Some(surface.name.text.clone());
                    return Err(diagnostic.into());
                }
                let binder = self.allocate_binder(&surface.name.text, surface.name.span)?;
                binders.push(binder.clone());
                ResolvedPatternKind::Binder(binder)
            }
            SurfacePatternKind::Wildcard => ResolvedPatternKind::Wildcard,
            SurfacePatternKind::Boolean(value) => ResolvedPatternKind::Boolean(*value),
            SurfacePatternKind::Unit => ResolvedPatternKind::Unit,
            SurfacePatternKind::Tuple(elements) => ResolvedPatternKind::Tuple(
                elements
                    .iter()
                    .map(|element| self.resolve_pattern(element, seen, binders))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            SurfacePatternKind::Constructor { name, payload } => {
                let constructor = self.constructor_reference(name)?;
                ResolvedPatternKind::Constructor {
                    constructor,
                    occurrence: ResolvedConstructorOccurrence {
                        constructor,
                        spelling: name.member().text.clone(),
                        origin: Origin::Source(name.span()),
                    },
                    payload: payload
                        .as_deref()
                        .map(|payload| self.resolve_pattern(payload, seen, binders).map(Box::new))
                        .transpose()?,
                }
            }
        };
        Ok(ResolvedPattern {
            kind,
            span: pattern.span,
        })
    }

    fn resolve_block(&mut self, block: &SurfaceBlock) -> Result<ResolvedBlock, ResolveError> {
        let resolved = self.resolve_work(ResolveTask::VisitBlock(block))?;
        let ResolvedExprKind::Block(block) = resolved.kind else {
            return Err(error(
                ResolveReason::InternalState,
                block.span,
                "the resolver produced the wrong block payload",
            )
            .with_context(ResolveContext::WorkState {
                part: "block",
                problem: "wrong",
            }));
        };
        Ok(block)
    }

    fn finish_hook(
        &mut self,
        effect: ResolvedEffectInstance,
        span: Span,
        body: ResolvedExpressionOwner,
    ) -> Result<ResolvedExpr, ResolveError> {
        let target_span = effect.span;
        self.type_work.charge(6).map_err(|()| {
            error(
                ResolveReason::TypeResourceExhausted,
                span,
                "hook identity clause retention exceeded its type-work budget",
            )
        })?;
        let mut clauses = Vec::new();
        clauses.try_reserve_exact(1).map_err(|_| {
            error(
                ResolveReason::TypeResourceExhausted,
                span,
                "hook identity clause storage could not be reserved",
            )
        })?;
        let input = self.allocate_binder("", target_span)?;
        let resume = ResumeId::new(self.next_resume);
        self.next_resume = self.next_resume.checked_add(1).ok_or_else(|| {
            identity_error(
                ResolveIdentitySpace::Continuation,
                span,
                "hook resume identity space is exhausted",
            )
        })?;
        let operation = OperationId::new(effect.instance.effect(), 0);
        let contract = crate::resolved::HookRootContract {
            target: crate::types::clone_effect_instance_with_budget(
                &effect.instance,
                &mut self.type_work,
            )
            .map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    span,
                    "hook target retention exceeded its type-work budget",
                )
            })?,
            span,
            target_span,
            operation,
            input: input.id,
            resume,
        };
        clauses.push(ResolvedHandlerClause {
            operation,
            spelling: "publish".into(),
            resume,
            pattern: ResolvedPattern {
                kind: ResolvedPatternKind::Binder(input),
                span: target_span,
            },
            body: ResolvedExpr {
                kind: ResolvedExprKind::Resume(ResolvedResumeExpr {
                    owner: Some(resume),
                    value: Box::new(ResolvedExpr {
                        kind: ResolvedExprKind::Occurrence(ResolvedOccurrence {
                            term: ResolvedTermName::Global(contract.input),
                            spelling: String::new(),
                            origin: Origin::Source(target_span),
                            import_span: None,
                            evidence: Box::new([]),
                        }),
                        span: target_span,
                    }),
                }),
                span: target_span,
            },
            span: target_span,
        });
        Ok(ResolvedExpr {
            kind: ResolvedExprKind::Handle(ResolvedHandleExpr {
                hook_registration: None,
                hook_root: Some(contract),
                body: Box::new(body.into_inner()),
                effect,
                clauses,
            }),
            span,
        })
    }

    fn finish_cleanup(
        &mut self,
        span: Span,
        initializer: ResolvedExpressionOwner,
        body: ResolvedExpressionOwner,
    ) -> Result<ResolvedExpr, ResolveError> {
        let exhausted = || {
            error(
                ResolveReason::TypeResourceExhausted,
                span,
                "cleanup lowering exceeded its budget",
            )
        };
        self.type_work.charge(9).map_err(|()| exhausted())?;
        let mut declarations = Vec::new();
        declarations.try_reserve_exact(1).map_err(|_| exhausted())?;
        let action_span = initializer.span;
        let callback = self.allocate_binder("", action_span)?;
        let owner = callback.id;
        declarations.push(ResolvedLocalDeclaration::Binding(Box::new(
            ResolvedBinding {
                pattern: ResolvedPattern {
                    kind: ResolvedPatternKind::Binder(callback),
                    span: action_span,
                },
                annotation: None,
                initializer: initializer.into_inner(),
                span: action_span,
            },
        )));
        let action = ResolvedExpr {
            kind: ResolvedExprKind::Apply(ResolvedApplicationExpr {
                function: Box::new(ResolvedExpr {
                    kind: ResolvedExprKind::Occurrence(ResolvedOccurrence {
                        term: ResolvedTermName::Global(owner),
                        spelling: String::new(),
                        origin: Origin::Source(action_span),
                        import_span: None,
                        evidence: Box::new([]),
                    }),
                    span: action_span,
                }),
                argument: Box::new(ResolvedExpr {
                    kind: ResolvedExprKind::Unit,
                    span: action_span,
                }),
            }),
            span: action_span,
        };
        Ok(ResolvedExpr {
            kind: ResolvedExprKind::Block(ResolvedBlock {
                declarations,
                result: Box::new(ResolvedExpr {
                    kind: ResolvedExprKind::Cleanup(Box::new(
                        crate::resolved::ResolvedCleanupExpr {
                            callback: owner,
                            action_span,
                            body: Box::new(body.into_inner()),
                            action: Box::new(action),
                        },
                    )),
                    span,
                }),
                span,
            }),
            span,
        })
    }

    fn finish_registration(
        &mut self,
        effect: ResolvedEffectInstance,
        span: Span,
        initializer: ResolvedExpressionOwner,
        body: ResolvedExpressionOwner,
    ) -> Result<ResolvedExpr, ResolveError> {
        let target_span = effect.span;
        let exhausted = || {
            error(
                ResolveReason::TypeResourceExhausted,
                span,
                "registration lowering exceeded its type-work budget",
            )
        };
        self.type_work.charge(24).map_err(|()| exhausted())?;
        let mut declarations = Vec::new();
        declarations.try_reserve_exact(1).map_err(|_| exhausted())?;
        let mut steps = Vec::new();
        steps.try_reserve_exact(2).map_err(|_| exhausted())?;
        let mut clauses = Vec::new();
        clauses.try_reserve_exact(1).map_err(|_| exhausted())?;
        let callback = self.allocate_binder("", target_span)?;
        let input = self.allocate_binder("", target_span)?;
        let previous = self.allocate_binder("", target_span)?;
        let next = self.allocate_binder("", target_span)?;
        let resume = ResumeId::new(self.next_resume);
        self.next_resume = self.next_resume.checked_add(1).ok_or_else(|| {
            identity_error(
                ResolveIdentitySpace::Continuation,
                span,
                "registration resume identity space is exhausted",
            )
        })?;
        let operation = OperationId::new(effect.instance.effect(), 0);
        let target =
            crate::types::clone_effect_instance_with_budget(&effect.instance, &mut self.type_work)
                .map_err(|()| exhausted())?;
        let forwarded =
            crate::types::clone_effect_instance_with_budget(&effect.instance, &mut self.type_work)
                .map_err(|()| exhausted())?;
        let contract = crate::resolved::HookRegistrationContract {
            target,
            span,
            target_span,
            operation,
            callback: callback.id,
            input: input.id,
            previous: previous.id,
            next: next.id,
            resume,
        };
        let occurrence = |binder| ResolvedExpr {
            kind: ResolvedExprKind::Occurrence(ResolvedOccurrence {
                term: ResolvedTermName::Global(binder),
                spelling: String::new(),
                origin: Origin::Source(target_span),
                import_span: None,
                evidence: Box::new([]),
            }),
            span: target_span,
        };
        let binding = |binder, initializer| {
            ResolvedLocalDeclaration::Binding(Box::new(ResolvedBinding {
                pattern: ResolvedPattern {
                    kind: ResolvedPatternKind::Binder(binder),
                    span: target_span,
                },
                annotation: None,
                initializer,
                span: target_span,
            }))
        };
        steps.push(binding(
            previous,
            ResolvedExpr {
                kind: ResolvedExprKind::Perform(ResolvedPerformExpr {
                    effect: ResolvedEffectInstance {
                        instance: forwarded,
                        argument_provenance: Box::new([]),
                        origin: Origin::Source(target_span),
                        span: target_span,
                    },
                    operation,
                    spelling: "publish".into(),
                    operand: Box::new(occurrence(contract.input)),
                    origin: Origin::Source(target_span),
                }),
                span: target_span,
            },
        ));
        steps.push(binding(
            next,
            ResolvedExpr {
                kind: ResolvedExprKind::Apply(ResolvedApplicationExpr {
                    function: Box::new(occurrence(contract.callback)),
                    argument: Box::new(occurrence(contract.previous)),
                }),
                span: target_span,
            },
        ));
        clauses.push(ResolvedHandlerClause {
            operation,
            spelling: "publish".into(),
            resume,
            pattern: ResolvedPattern {
                kind: ResolvedPatternKind::Binder(input),
                span: target_span,
            },
            body: ResolvedExpr {
                kind: ResolvedExprKind::Block(ResolvedBlock {
                    declarations: steps,
                    result: Box::new(ResolvedExpr {
                        kind: ResolvedExprKind::Resume(ResolvedResumeExpr {
                            owner: Some(resume),
                            value: Box::new(occurrence(contract.next)),
                        }),
                        span: target_span,
                    }),
                    span: target_span,
                }),
                span: target_span,
            },
            span: target_span,
        });
        declarations.push(binding(callback, initializer.into_inner()));
        Ok(ResolvedExpr {
            kind: ResolvedExprKind::Block(ResolvedBlock {
                declarations,
                result: Box::new(ResolvedExpr {
                    kind: ResolvedExprKind::Handle(ResolvedHandleExpr {
                        hook_registration: Some(Box::new(contract)),
                        hook_root: None,
                        body: Box::new(body.into_inner()),
                        effect,
                        clauses,
                    }),
                    span,
                }),
                span,
            }),
            span,
        })
    }

    fn allocate_binder(
        &mut self,
        spelling: &str,
        span: crate::source::Span,
    ) -> Result<Binder, ResolveError> {
        let id = BinderId::resolved(self.module, self.next_binder);
        self.next_binder = self.next_binder.checked_add(1).ok_or_else(|| {
            identity_error(
                ResolveIdentitySpace::TermBinder,
                span,
                "the program contains too many binders",
            )
        })?;
        Ok(Binder {
            id,
            spelling: spelling.to_owned(),
            origin: Origin::Source(span),
        })
    }

    fn clone_type_variable_for_retention(
        &mut self,
        parameter: &ResolvedTypeVariable,
        span: crate::source::Span,
        message: &'static str,
    ) -> Result<ResolvedTypeVariable, ResolveError> {
        clone_resolved_type_variable_with_budget(parameter, &mut self.type_work)
            .map_err(|()| error(ResolveReason::TypeResourceExhausted, span, message))
    }

    fn allocate_type_variable(
        &mut self,
        name: &SurfaceName,
        surface_kind: Option<&SurfaceKind>,
        implicit_kind: Kind,
    ) -> Result<ResolvedTypeVariable, ResolveError> {
        let kind = match surface_kind {
            Some(kind) => surface_kind_to_kind(kind, &mut self.type_work),
            None => self.type_work.charge(1).map(|()| implicit_kind),
        }
        .map_err(|()| {
            error(
                ResolveReason::TypeResourceExhausted,
                name.span,
                "type-parameter kind retention exceeded its type-work budget",
            )
        })?;
        self.type_work.charge(1).map_err(|()| {
            error(
                ResolveReason::TypeResourceExhausted,
                name.span,
                "type-parameter record retention exceeded its type-work budget",
            )
        })?;
        let spelling = try_clone_resolution_string(
            &name.text,
            name.span,
            "type-parameter spelling storage could not be reserved",
        )?;
        let id = TypeVariableId::resolved(self.module, self.next_type_variable);
        self.next_type_variable = self.next_type_variable.checked_add(1).ok_or_else(|| {
            identity_error(
                ResolveIdentitySpace::TypeBinder,
                name.span,
                "the program contains too many type binders",
            )
        })?;
        Ok(ResolvedTypeVariable {
            id,
            spelling,
            kind,
            origin: Origin::Source(name.span),
        })
    }

    fn allocate_declaration_type_parameters(
        &mut self,
        explicit: Option<&[SurfaceTypeParameter]>,
        free_names: &[FreeTypeName],
        infer_effect_row_tails: bool,
    ) -> Result<Vec<ResolvedTypeVariable>, ResolveError> {
        let Some(explicit) = explicit else {
            return free_names
                .iter()
                .map(|free| {
                    let kind = if infer_effect_row_tails && free.role == FreeTypeNameRole::EffectRow
                    {
                        Kind::EffectRow
                    } else {
                        Kind::Type
                    };
                    self.allocate_type_variable(&free.name, None, kind)
                })
                .collect();
        };

        let free = free_names
            .iter()
            .map(|free| free.name.text.as_str())
            .collect::<HashSet<_>>();
        let mut parameters = Vec::with_capacity(explicit.len());
        for parameter in explicit {
            if !free.contains(parameter.name.text.as_str()) {
                let mut diagnostic = Diagnostic::new(
                    ResolveReason::UnusedTypeParameter,
                    SourceLabel::new(
                        parameter.name.span,
                        "this explicit type parameter is not used in the declaration header",
                    ),
                );
                diagnostic.found = Some(parameter.name.text.clone());
                return Err(diagnostic.into());
            }
            parameters.push(self.allocate_type_variable(
                &parameter.name,
                parameter.kind.as_ref(),
                Kind::Type,
            )?);
        }
        Ok(parameters)
    }

    fn allocate_global_type_parameters(
        &mut self,
        definition: &crate::surface::SurfaceDefinition,
    ) -> Result<Vec<ResolvedTypeVariable>, ResolveError> {
        let explicit = match &definition.kind {
            SurfaceDefinitionKind::Equational(equational) => {
                equational.interface.type_parameters.as_deref()
            }
            SurfaceDefinitionKind::InlineOperational(operational) => {
                operational.header.type_parameters.as_deref()
            }
        };
        let infer_implicit_effect_rows = explicit.is_none();
        let declared = validate_explicit_type_parameters(explicit)?;
        let mut names = Vec::new();
        let mut seen = HashMap::new();
        match &definition.kind {
            SurfaceDefinitionKind::Equational(equational) => {
                collect_free_type_names(
                    &equational.interface.annotation,
                    &self.type_names,
                    &self.interface_names,
                    &declared,
                    &mut seen,
                    &mut names,
                    infer_implicit_effect_rows,
                    &mut self.type_work,
                )?;
                for requirement in &equational.interface.requirements {
                    for argument in &requirement.arguments {
                        collect_free_type_names(
                            argument,
                            &self.type_names,
                            &self.interface_names,
                            &declared,
                            &mut seen,
                            &mut names,
                            infer_implicit_effect_rows,
                            &mut self.type_work,
                        )?;
                    }
                }
            }
            SurfaceDefinitionKind::InlineOperational(operational) => {
                for parameter in &operational.header.parameters {
                    collect_free_type_names(
                        &parameter.annotation,
                        &self.type_names,
                        &self.interface_names,
                        &declared,
                        &mut seen,
                        &mut names,
                        infer_implicit_effect_rows,
                        &mut self.type_work,
                    )?;
                }
                collect_free_type_names(
                    &operational.header.result_type,
                    &self.type_names,
                    &self.interface_names,
                    &declared,
                    &mut seen,
                    &mut names,
                    infer_implicit_effect_rows,
                    &mut self.type_work,
                )?;
                for requirement in &operational.header.requirements {
                    for argument in &requirement.arguments {
                        collect_free_type_names(
                            argument,
                            &self.type_names,
                            &self.interface_names,
                            &declared,
                            &mut seen,
                            &mut names,
                            infer_implicit_effect_rows,
                            &mut self.type_work,
                        )?;
                    }
                }
            }
        }
        self.allocate_declaration_type_parameters(explicit, &names, infer_implicit_effect_rows)
    }

    fn resolve_lexical_method_group(
        &mut self,
        source: &crate::surface::SurfaceLexicalEvidence,
        start: usize,
    ) -> Result<(ResolvedImplementationMethodGroup, usize), ResolveError> {
        let first = &source.equations[start];
        let mut end = start + 1;
        while end < source.equations.len() && source.equations[end].name.text == first.name.text {
            end += 1;
        }
        let binder = self.allocate_binder(&first.name.text, first.name.span)?;
        let method =
            self.method_names
                .get(&first.name.text)
                .and_then(|binding| match binding.term {
                    ResolvedTermName::Method(method) => Some(method),
                    ResolvedTermName::Global(_) => None,
                });
        let mut contextual_parameters = ImportedTypeVariableBuffer(Vec::new());
        if let Some(method) = method {
            let parameters = if method.interface().module() == self.module {
                self.type_work
                    .charge(self.resolved_interfaces.0.len())
                    .map_err(|()| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            first.span,
                            "lexical interface lookup exceeded its budget",
                        )
                    })?;
                let interface = self
                    .resolved_interfaces
                    .0
                    .iter()
                    .find(|interface| interface.id == method.interface())
                    .ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            first.span,
                            "method parameters are unavailable",
                        )
                    })?;
                self.type_work
                    .charge(interface.methods.len())
                    .map_err(|()| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            first.span,
                            "lexical method lookup exceeded its budget",
                        )
                    })?;
                interface
                    .methods
                    .iter()
                    .find(|candidate| candidate.id == method)
                    .map(|method| method.type_parameters.as_ref())
            } else {
                let interface = self.imported.interface(method.interface()).ok_or_else(|| {
                    error(
                        ResolveReason::InternalState,
                        first.span,
                        "method parameters are unavailable",
                    )
                })?;
                self.type_work
                    .charge(interface.methods.len())
                    .map_err(|()| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            first.span,
                            "lexical method lookup exceeded its budget",
                        )
                    })?;
                interface
                    .method(method)
                    .map(|method| method.authoritative_type_parameters())
            }
            .ok_or_else(|| {
                error(
                    ResolveReason::InternalState,
                    first.span,
                    "method parameters are unavailable",
                )
            })?;
            self.type_work.charge(parameters.len()).map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    first.span,
                    "lexical method parameter retention exceeded its budget",
                )
            })?;
            contextual_parameters
                .try_reserve(parameters.len())
                .map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        first.span,
                        "lexical method parameter storage could not be reserved",
                    )
                })?;
            for parameter in parameters {
                let mut fresh =
                    clone_resolved_type_variable_with_budget(parameter, &mut self.type_work)
                        .map_err(|()| {
                            error(
                                ResolveReason::TypeResourceExhausted,
                                first.span,
                                "lexical method parameter retention exceeded its budget",
                            )
                        })?;
                fresh.id = TypeVariableId::resolved(self.module, self.next_type_variable);
                fresh.origin = Origin::Source(first.span);
                self.next_type_variable =
                    self.next_type_variable.checked_add(1).ok_or_else(|| {
                        identity_error(
                            ResolveIdentitySpace::TypeBinder,
                            first.span,
                            "lexical method parameter identities exhausted",
                        )
                    })?;
                contextual_parameters.push(fresh);
            }
            self.type_work
                .charge(contextual_parameters.0.len())
                .map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        first.span,
                        "lexical method registry retention exceeded its budget",
                    )
                })?;
            self.lexical_method_parameters
                .try_reserve(contextual_parameters.0.len())
                .map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        first.span,
                        "lexical method registry storage could not be reserved",
                    )
                })?;
            for parameter in &contextual_parameters.0 {
                self.lexical_method_parameters.push(
                    clone_resolved_type_variable_with_budget(parameter, &mut self.type_work)
                        .map_err(|()| {
                            error(
                                ResolveReason::TypeResourceExhausted,
                                first.span,
                                "lexical method registry retention exceeded its budget",
                            )
                        })?,
                );
            }
        }
        let span = first
            .span
            .cover(source.equations[end - 1].span)
            .ok_or_else(|| {
                error(
                    ResolveReason::InternalState,
                    source.span,
                    "method equations cross source files",
                )
            })?;
        Ok((
            ResolvedImplementationMethodGroup {
                contextual_parameters: contextual_parameters.into_boxed_slice(),
                method,
                identity: None,
                binder,
                equations: Box::new([]),
                span,
            },
            end,
        ))
    }

    fn finish_resource_expression(
        &mut self,
        kind: crate::surface::SurfaceResourceKind,
        identity: ResolvedTypeVariable,
        handle: Binder,
        initializer: ResolvedExpressionOwner,
        body: ResolvedExpressionOwner,
        span: Span,
    ) -> Result<ResolvedExpr, ResolveError> {
        use crate::resolved::{
            ResolvedEffectInstance, ResolvedPerformExpr, ResolvedResourceExpr, ResourceAcquisition,
            ResourceApi,
        };
        let builtin = self.resource_builtin(kind).ok_or_else(|| {
            error(
                ResolveReason::InternalState,
                span,
                "resource builtin origin is missing",
            )
        })?;
        let api = ResourceApi::for_module(builtin).ok_or_else(|| {
            error(
                ResolveReason::InternalState,
                span,
                "resource builtin origin is invalid",
            )
        })?;
        // Each fixed method retains its forwarding equation, pattern, operand
        // and effect argument alongside one complete provider application.
        self.type_work
            .charge(12 * api.method_names().len())
            .map_err(|()| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    span,
                    "resource provider construction exceeded its budget",
                )
            })?;
        self.constraint_work
            .charge(1 + api.method_names().len())
            .map_err(|()| {
                error(
                    ResolveReason::ConstraintResourceExhausted,
                    span,
                    "resource provider construction exceeded its budget",
                )
            })?;
        let provider =
            crate::interface::LexicalEvidenceId::new(self.module, self.next_lexical_evidence);
        self.next_lexical_evidence =
            self.next_lexical_evidence.checked_add(1).ok_or_else(|| {
                identity_error(
                    ResolveIdentitySpace::LexicalEvidence,
                    span,
                    "resource provider identities exhausted",
                )
            })?;
        let mut groups = ResolvedImplementationMethodGroupBuffer(Vec::new());
        groups
            .0
            .try_reserve(api.method_names().len())
            .map_err(|_| {
                error(
                    ResolveReason::TypeResourceExhausted,
                    span,
                    "resource methods could not be reserved",
                )
            })?;
        let mut method_binders = [handle.id; 3];
        for (ordinal, &spelling) in api.method_names().iter().enumerate() {
            let binder = self.allocate_binder(spelling, span)?;
            method_binders[ordinal] = binder.id;
            let parameter = self.allocate_binder("value", span)?;
            let operand = ResolvedExpr {
                kind: ResolvedExprKind::Occurrence(ResolvedOccurrence {
                    term: ResolvedTermName::Global(parameter.id),
                    spelling: parameter.spelling.clone(),
                    origin: Origin::Source(span),
                    import_span: None,
                    evidence: Box::new([]),
                }),
                span,
            };
            let request = ResolvedExpr {
                kind: ResolvedExprKind::Perform(ResolvedPerformExpr {
                    effect: ResolvedEffectInstance {
                        argument_provenance: Box::new([]),
                        instance: crate::types::EffectInstance::new(
                            api.ops(),
                            Box::new([Type::Variable(identity.id)]),
                        ),
                        origin: Origin::Source(span),
                        span,
                    },
                    operation: crate::types::OperationId::new(api.ops(), ordinal as u32),
                    spelling: spelling.to_owned(),
                    operand: Box::new(operand),
                    origin: Origin::Source(span),
                }),
                span,
            };
            groups.0.push(ResolvedImplementationMethodGroup {
                contextual_parameters: Box::new([]),
                method: Some(crate::interface::MethodId::new(
                    api.provider(),
                    ordinal as u32,
                )),
                identity: None,
                equations: Box::new([ResolvedEquation {
                    name: crate::resolved::ResolvedEquationHead {
                        binder: binder.id,
                        spelling: spelling.to_owned(),
                        origin: Origin::Source(span),
                    },
                    patterns: vec![ResolvedPattern {
                        kind: ResolvedPatternKind::Binder(parameter),
                        span,
                    }],
                    body: request,
                    span,
                }]),
                binder,
                span,
            });
        }
        let acquisition = ResourceAcquisition {
            builtin,
            identity: identity.id,
            handle: handle.id,
            provider,
            methods: if api.is_native_buffer() {
                crate::resolved::ResourceMethods::NativeBuffer(method_binders)
            } else {
                crate::resolved::ResourceMethods::Cell([method_binders[0], method_binders[1]])
            },
            span,
        };
        let generated = crate::resolved::ResolvedLexicalEvidence {
            acquisition: Some(acquisition),
            checked: crate::interface::LexicalEvidenceSlot::default(),
            id: provider,
            application: crate::resolved::ResolvedInterfaceApplication {
                interface: crate::resolved::ResolvedInterfaceOccurrence {
                    id: api.provider(),
                    spelling: "Provider".to_owned(),
                    origin: Origin::Source(span),
                },
                arguments: Box::new([ResolvedType {
                    ty: Type::Variable(identity.id),
                    provenance: crate::resolved::ResolvedTypeProvenance::new(
                        vec![crate::resolved::ResolvedTypeProvenanceNode::Fact(span)],
                        0,
                    ),
                    origin: Origin::Source(span),
                    span,
                }]),
                span,
            },
            method_groups: groups.into_boxed_slice(),
            span,
        };
        let body = ResolvedExpr {
            kind: ResolvedExprKind::Block(ResolvedBlock {
                declarations: vec![ResolvedLocalDeclaration::Evidence(Box::new(generated))],
                result: Box::new(body.into_inner()),
                span,
            }),
            span,
        };
        Ok(ResolvedExpr {
            kind: ResolvedExprKind::Resource(Box::new(ResolvedResourceExpr {
                acquisition,
                identity,
                handle,
                initializer: Box::new(initializer.into_inner()),
                body: Box::new(body),
            })),
            span,
        })
    }

    fn resolve_expr(&mut self, expression: &SurfaceExpr) -> Result<ResolvedExpr, ResolveError> {
        self.resolve_work(ResolveTask::VisitExpr(expression))
    }

    fn resolve_work<'a>(&mut self, initial: ResolveTask<'a>) -> Result<ResolvedExpr, ResolveError> {
        let scope_checkpoint = self.scopes.len();
        let type_scope_checkpoint = self.type_scopes.len();
        let nominal_scope_checkpoint = self.lexical_nominal_scopes.len();
        let constructor_scope_checkpoint = self.lexical_constructor_scopes.len();
        let result = self.resolve_work_inner(initial);
        if result.is_err() {
            self.scopes.truncate(scope_checkpoint);
            self.type_scopes.truncate(type_scope_checkpoint);
            self.lexical_nominal_scopes
                .truncate(nominal_scope_checkpoint);
            self.lexical_constructor_scopes
                .truncate(constructor_scope_checkpoint);
        }
        result
    }

    fn resolve_work_inner<'a>(
        &mut self,
        initial: ResolveTask<'a>,
    ) -> Result<ResolvedExpr, ResolveError> {
        let initial_span = initial.span();
        let mut tasks = ResolveTaskBuffer(vec![initial]);
        let mut expressions = ResolvedExpressionBuffer(Vec::new());
        let mut declarations = ResolvedDeclarationBuffer(Vec::new());

        while let Some(task) = tasks.pop() {
            match task {
                ResolveTask::VisitExpr(expression) => {
                    if let SurfaceExprKind::Match(match_expression) = &expression.kind {
                        self.visit_match_expression(
                            match_expression,
                            expression.span,
                            &mut expressions,
                        )?;
                    } else {
                        self.visit_expression(expression, &mut tasks, &mut expressions)?;
                    }
                }
                ResolveTask::FinishPerform {
                    effect,
                    operation,
                    spelling,
                    operation_span,
                    span,
                } => {
                    Self::finish_perform(
                        effect,
                        operation,
                        spelling,
                        operation_span,
                        span,
                        &mut expressions,
                    )?;
                }
                ResolveTask::FinishHook { effect, span } => {
                    let body = expressions.pop_owned().ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            span,
                            "hook body resolution produced no expression",
                        )
                    })?;
                    expressions.push(self.finish_hook(effect, span, body)?);
                }
                ResolveTask::FinishRegistration { effect, span } => {
                    let body = expressions.pop_owned().ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            span,
                            "missing registration body",
                        )
                    })?;
                    let initializer = expressions.pop_owned().ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            span,
                            "missing registration initializer",
                        )
                    })?;
                    expressions.push(self.finish_registration(effect, span, initializer, body)?);
                }
                ResolveTask::FinishCleanup { span } => {
                    let body = expressions.pop_owned().ok_or_else(|| {
                        error(ResolveReason::InternalState, span, "missing cleanup body")
                    })?;
                    let initializer = expressions.pop_owned().ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            span,
                            "missing cleanup initializer",
                        )
                    })?;
                    expressions.push(self.finish_cleanup(span, initializer, body)?);
                }
                ResolveTask::VisitBlock(block) => {
                    let scope_checkpoint = self.scopes.len();
                    let nominal_scope_checkpoint = self.lexical_nominal_scopes.len();
                    let constructor_scope_checkpoint = self.lexical_constructor_scopes.len();
                    self.scopes.push(HashMap::new());
                    self.lexical_nominal_scopes.push(HashMap::new());
                    self.lexical_constructor_scopes.push(HashMap::new());
                    let declaration_start = declarations.len();
                    tasks.push(ResolveTask::FinishBlock {
                        declaration_start,
                        scope_checkpoint,
                        nominal_scope_checkpoint,
                        constructor_scope_checkpoint,
                        span: block.span,
                    });
                    tasks.push(ResolveTask::VisitExpr(&block.result));
                    for declaration in block.declarations.iter().rev() {
                        match declaration {
                            SurfaceLocalDeclaration::Evidence(source) => {
                                tasks.push(ResolveTask::VisitLexicalEvidence(source));
                            }
                            SurfaceLocalDeclaration::Binding(binding) => {
                                tasks.push(ResolveTask::FinishBinding(binding));
                                tasks.push(ResolveTask::VisitExpr(&binding.initializer));
                            }
                            SurfaceLocalDeclaration::Recursive(group) => {
                                tasks.push(ResolveTask::VisitRecursiveGroup(group));
                            }
                            SurfaceLocalDeclaration::Newtype(declaration) => {
                                tasks.push(ResolveTask::FinishLocalNewtype(declaration));
                            }
                        }
                    }
                }
                ResolveTask::ResourceInitializer { source, span } => {
                    let initializer = expressions.pop_owned().ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            span,
                            "resource initializer is missing",
                        )
                    })?;
                    let identity =
                        self.allocate_type_variable(&source.identity, None, Kind::Type)?;
                    let handle = self.allocate_binder(&source.handle.text, source.handle.span)?;
                    self.type_work.charge(4).map_err(|()| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            span,
                            "resource scope retention exceeded its budget",
                        )
                    })?;
                    self.lexical_method_parameters
                        .0
                        .try_reserve(1)
                        .map_err(|_| {
                            error(
                                ResolveReason::TypeResourceExhausted,
                                span,
                                "resource identity retention could not be reserved",
                            )
                        })?;
                    let retained = self.clone_type_variable_for_retention(
                        &identity,
                        span,
                        "resource identity retention exceeded its budget",
                    )?;
                    self.lexical_method_parameters.push(retained);
                    let scope_checkpoint = self.scopes.len();
                    let type_scope_checkpoint = self.type_scopes.len();
                    let mut terms = HashMap::new();
                    terms.try_reserve(1).map_err(|_| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            span,
                            "resource handle scope could not be reserved",
                        )
                    })?;
                    terms.insert(
                        handle.spelling.clone(),
                        ResolvedTermBinding::local(ResolvedTermName::Global(handle.id)),
                    );
                    let mut types = HashMap::new();
                    types.try_reserve(1).map_err(|_| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            span,
                            "resource type scope could not be reserved",
                        )
                    })?;
                    types.insert(identity.spelling.clone(), identity.id);
                    self.scopes.try_reserve(1).map_err(|_| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            span,
                            "resource scope could not be reserved",
                        )
                    })?;
                    self.type_scopes.try_reserve(1).map_err(|_| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            span,
                            "resource type scope could not be reserved",
                        )
                    })?;
                    self.scopes.push(terms);
                    self.type_scopes.push(types);
                    tasks.0.try_reserve(2).map_err(|_| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            span,
                            "resource body scheduling could not be reserved",
                        )
                    })?;
                    self.type_work.charge(1).map_err(|()| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            span,
                            "resource initializer ownership exceeded its type-work budget",
                        )
                    })?;
                    tasks.push(ResolveTask::FinishResource {
                        kind: source.kind,
                        identity,
                        handle,
                        initializer: Box::new(initializer),
                        scope_checkpoint,
                        type_scope_checkpoint,
                        span,
                    });
                    tasks.push(ResolveTask::VisitBlock(&source.body));
                }
                ResolveTask::FinishResource {
                    kind,
                    identity,
                    handle,
                    initializer,
                    scope_checkpoint,
                    type_scope_checkpoint,
                    span,
                } => {
                    let body = expressions.pop_owned().ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            span,
                            "resource body is missing",
                        )
                    })?;
                    self.scopes.truncate(scope_checkpoint);
                    self.type_scopes.truncate(type_scope_checkpoint);
                    expressions.push(self.finish_resource_expression(
                        kind,
                        identity,
                        handle,
                        *initializer,
                        body,
                        span,
                    )?);
                }
                ResolveTask::VisitRecursiveGroup(group) => {
                    let mut first_members = HashMap::with_capacity(group.members.len());
                    let mut binders = ResolvedBinderBuffer(Vec::with_capacity(group.members.len()));
                    for member in &group.members {
                        if let Some(first_span) =
                            first_members.get(member.binder.name.text.as_str()).copied()
                        {
                            let mut diagnostic = Diagnostic::new(
                                ResolveReason::DuplicateRecursiveMember,
                                SourceLabel::new(
                                    member.binder.name.span,
                                    "this recursive member name is already defined",
                                ),
                            );
                            diagnostic.related.push(SourceLabel::new(
                                first_span,
                                "the first recursive member is here",
                            ));
                            diagnostic.found = Some(member.binder.name.text.clone());
                            return Err(diagnostic.into());
                        }
                        first_members
                            .insert(member.binder.name.text.as_str(), member.binder.name.span);
                        binders.push(
                            self.allocate_binder(
                                &member.binder.name.text,
                                member.binder.name.span,
                            )?,
                        );
                    }
                    let Some(scope) = self.scopes.last_mut() else {
                        return Err(error(
                            ResolveReason::InternalState,
                            group.span,
                            "the resolver lost the current lexical scope",
                        )
                        .with_context(ResolveContext::MissingLexicalScope));
                    };
                    for binder in binders.iter() {
                        scope.insert(
                            binder.spelling.clone(),
                            ResolvedTermBinding::local(ResolvedTermName::Global(binder.id)),
                        );
                    }
                    tasks.push(ResolveTask::FinishRecursiveGroup { group, binders });
                    for member in group.members.iter().rev() {
                        tasks.push(ResolveTask::VisitExpr(&member.initializer));
                    }
                }
                ResolveTask::FinishApplication { span } => {
                    let (function, argument) = take_expression_pair(&mut expressions, span)?;
                    expressions.push(ResolvedExpr {
                        kind: ResolvedExprKind::Apply(ResolvedApplicationExpr {
                            function: Box::new(function),
                            argument: Box::new(argument),
                        }),
                        span,
                    });
                }
                ResolveTask::FinishBinary {
                    kind,
                    operator_span,
                    span,
                } => {
                    let (left, right) = take_expression_pair(&mut expressions, span)?;
                    let binary = ResolvedBinaryExpr {
                        left: Box::new(left),
                        right: Box::new(right),
                        operator_span,
                    };
                    expressions.push(ResolvedExpr {
                        kind: kind.finish(binary),
                        span,
                    });
                }
                ResolveTask::FinishBinding(binding) => {
                    let (patterns, binders) =
                        self.resolve_pattern_vector(std::slice::from_ref(&binding.pattern))?;
                    let mut patterns = ResolvedPatternBuffer(patterns);
                    let pattern = patterns.pop().ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            binding.pattern.span,
                            "the resolver produced no binding pattern",
                        )
                        .with_context(ResolveContext::WorkState {
                            part: "binding-pattern",
                            problem: "missing",
                        })
                    })?;
                    let pattern = ResolvedPatternOwner::new(pattern);
                    let annotation = binding
                        .annotation
                        .as_ref()
                        .map(|annotation| self.resolve_type(annotation))
                        .transpose()?
                        .map(ResolvedTypeOccurrenceOwner::new);
                    let initializer = expressions.pop_owned().ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            binding.span,
                            "the resolver lost a binding initializer",
                        )
                        .with_context(ResolveContext::WorkState {
                            part: "binding-initializer",
                            problem: "missing",
                        })
                    })?;
                    let Some(scope) = self.scopes.last_mut() else {
                        return Err(error(
                            ResolveReason::InternalState,
                            binding.span,
                            "the resolver lost the current lexical scope",
                        )
                        .with_context(ResolveContext::MissingLexicalScope));
                    };
                    for binder in binders {
                        scope.insert(
                            binder.spelling.clone(),
                            ResolvedTermBinding::local(ResolvedTermName::Global(binder.id)),
                        );
                    }
                    declarations.push(ResolvedLocalDeclaration::Binding(Box::new(
                        ResolvedBinding {
                            pattern: pattern.into_inner(),
                            annotation: annotation.map(ResolvedTypeOccurrenceOwner::into_inner),
                            initializer: initializer.into_inner(),
                            span: binding.span,
                        },
                    )));
                }
                ResolveTask::FinishLocalNewtype(declaration) => {
                    let owner = self.resolve_local_newtype(declaration)?;
                    declarations.push(ResolvedLocalDeclaration::Newtype(owner));
                }
                ResolveTask::VisitLexicalEvidence(source) => {
                    let id = crate::interface::LexicalEvidenceId::new(
                        self.module,
                        self.next_lexical_evidence,
                    );
                    self.next_lexical_evidence =
                        self.next_lexical_evidence.checked_add(1).ok_or_else(|| {
                            error(
                                ResolveReason::InternalState,
                                source.span,
                                "lexical evidence identity space is exhausted",
                            )
                        })?;
                    self.constraint_work.charge(1).map_err(|()| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            source.span,
                            "lexical evidence storage exceeded its budget",
                        )
                    })?;
                    let application = self.resolve_interface_application(&source.application)?;
                    if application.interface.id.module().is_builtin_resource() {
                        return Err(error(
                            ResolveReason::SealedProvider,
                            source.span,
                            "only resource acquisition may introduce the builtin cell provider",
                        ));
                    }
                    let mut state = Box::new(PendingLexicalResolution {
                        source,
                        id,
                        application: Some(application),
                        groups: ResolvedImplementationMethodGroupBuffer(Vec::new()),
                        equations: ResolvedEquationBuffer(Vec::new()),
                        next: 0,
                        group_end: 0,
                    });
                    self.constraint_work
                        .charge(source.equations.len())
                        .map_err(|()| {
                            error(
                                ResolveReason::TypeResourceExhausted,
                                source.span,
                                "lexical evidence storage exceeded its budget",
                            )
                        })?;
                    state
                        .groups
                        .0
                        .try_reserve(source.equations.len())
                        .map_err(|_| {
                            error(
                                ResolveReason::TypeResourceExhausted,
                                source.span,
                                "lexical evidence storage could not be reserved",
                            )
                        })?;
                    tasks.push(ResolveTask::ContinueLexicalEvidence(state));
                }
                ResolveTask::ContinueLexicalEvidence(mut state) => {
                    if state.next == state.group_end {
                        if let Some(group) = state.groups.0.last_mut() {
                            group.equations = std::mem::replace(
                                &mut state.equations,
                                ResolvedEquationBuffer(Vec::new()),
                            )
                            .into_boxed_slice();
                        }
                        if state.next == state.source.equations.len() {
                            let evidence = crate::resolved::ResolvedLexicalEvidence {
                                acquisition: None,
                                checked: crate::interface::LexicalEvidenceSlot::default(),
                                id: state.id,
                                application: state.application.take().ok_or_else(|| {
                                    error(
                                        ResolveReason::InternalState,
                                        state.source.span,
                                        "lexical evidence application is missing",
                                    )
                                })?,
                                method_groups: std::mem::replace(
                                    &mut state.groups,
                                    ResolvedImplementationMethodGroupBuffer(Vec::new()),
                                )
                                .into_boxed_slice(),
                                span: state.source.span,
                            };
                            declarations
                                .push(ResolvedLocalDeclaration::Evidence(Box::new(evidence)));
                            continue;
                        }
                        let (group, end) =
                            self.resolve_lexical_method_group(state.source, state.next)?;
                        state.groups.0.push(group);
                        state.group_end = end;
                        state
                            .equations
                            .0
                            .try_reserve(end - state.next)
                            .map_err(|_| {
                                error(
                                    ResolveReason::TypeResourceExhausted,
                                    state.source.span,
                                    "lexical method equation storage could not be reserved",
                                )
                            })?;
                    }
                    let equation = &state.source.equations[state.next];
                    let scope_checkpoint = self.scopes.len();
                    let (patterns, binders) = self.resolve_pattern_vector(&equation.patterns)?;
                    let patterns = ResolvedPatternBuffer(patterns);
                    self.push_binder_scope_many(&binders);
                    tasks.push(ResolveTask::FinishLexicalEquation {
                        state,
                        patterns,
                        scope_checkpoint,
                    });
                    tasks.push(ResolveTask::VisitExpr(&equation.body));
                }
                ResolveTask::FinishLexicalEquation {
                    mut state,
                    patterns,
                    scope_checkpoint,
                } => {
                    self.scopes.truncate(scope_checkpoint);
                    let equation = &state.source.equations[state.next];
                    let body = expressions.pop_owned().ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            equation.span,
                            "lexical method body is missing",
                        )
                    })?;
                    let binder = state
                        .groups
                        .0
                        .last()
                        .ok_or_else(|| {
                            error(
                                ResolveReason::InternalState,
                                equation.span,
                                "lexical method group is missing",
                            )
                        })?
                        .binder
                        .id;
                    state.equations.0.push(ResolvedEquation {
                        name: crate::resolved::ResolvedEquationHead {
                            binder,
                            spelling: equation.name.text.clone(),
                            origin: Origin::Source(equation.name.span),
                        },
                        patterns: patterns.into_vec(),
                        body: body.into_inner(),
                        span: equation.span,
                    });
                    state.next += 1;
                    tasks.push(ResolveTask::ContinueLexicalEvidence(state));
                }
                ResolveTask::FinishRecursiveGroup { group, binders } => {
                    if binders.len() != group.members.len()
                        || expressions.len() < group.members.len()
                    {
                        return Err(error(
                            ResolveReason::InternalState,
                            group.span,
                            "the resolver lost a recursive group member",
                        )
                        .with_context(ResolveContext::WorkState {
                            part: "recursive-member",
                            problem: "missing",
                        }));
                    }
                    let mut annotations = ResolvedTypeOccurrenceBuffer(Vec::new());
                    annotations
                        .0
                        .try_reserve(group.members.len())
                        .map_err(|_| {
                            error(
                                ResolveReason::TypeResourceExhausted,
                                group.span,
                                "recursive annotation storage exceeded its work budget",
                            )
                        })?;
                    for member in &group.members {
                        annotations.0.push(self.resolve_type(&member.annotation)?);
                    }
                    let expression_start = expressions.len() - group.members.len();
                    let initializers = expressions.split_off(expression_start).into_vec();
                    let members = group
                        .members
                        .iter()
                        .zip(binders.into_vec())
                        .zip(annotations.into_vec())
                        .zip(initializers)
                        .map(|(((member, binder), annotation), initializer)| {
                            ResolvedRecursiveMember {
                                introducer_span: member.introducer_span,
                                binder,
                                annotation,
                                initializer,
                                span: member.span,
                            }
                        })
                        .collect::<Vec<_>>();
                    declarations.push(ResolvedLocalDeclaration::Recursive(
                        ResolvedRecursiveGroup {
                            members,
                            span: group.span,
                        },
                    ));
                }
                ResolveTask::FinishBlock {
                    declaration_start,
                    scope_checkpoint,
                    nominal_scope_checkpoint,
                    constructor_scope_checkpoint,
                    span,
                } => {
                    let result = expressions.pop_owned().ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            span,
                            "the resolver lost a block result",
                        )
                        .with_context(ResolveContext::WorkState {
                            part: "block-result",
                            problem: "missing",
                        })
                    })?;
                    if declaration_start > declarations.len() {
                        return Err(error(
                            ResolveReason::InternalState,
                            span,
                            "the resolver lost a block binding",
                        )
                        .with_context(ResolveContext::WorkState {
                            part: "block-binding",
                            problem: "missing",
                        }));
                    }
                    let block_declarations = declarations.split_off(declaration_start).into_vec();
                    self.scopes.truncate(scope_checkpoint);
                    self.lexical_nominal_scopes
                        .truncate(nominal_scope_checkpoint);
                    self.lexical_constructor_scopes
                        .truncate(constructor_scope_checkpoint);
                    expressions.push(ResolvedExpr {
                        kind: ResolvedExprKind::Block(ResolvedBlock {
                            declarations: block_declarations,
                            result: Box::new(result.into_inner()),
                            span,
                        }),
                        span,
                    });
                }
                ResolveTask::FinishFunction {
                    parameter: pattern,
                    scope_checkpoint,
                    span,
                } => {
                    let body_expression = expressions.pop_owned().ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            span,
                            "the resolver lost a function body",
                        )
                        .with_context(ResolveContext::WorkState {
                            part: "function-body",
                            problem: "missing",
                        })
                    })?;
                    if !matches!(body_expression.kind, ResolvedExprKind::Block(_)) {
                        return Err(error(
                            ResolveReason::InternalState,
                            span,
                            "the resolver produced the wrong function body payload",
                        )
                        .with_context(ResolveContext::WorkState {
                            part: "function-body",
                            problem: "wrong",
                        }));
                    }
                    let ResolvedExprKind::Block(body) = body_expression.into_inner().kind else {
                        unreachable!("the function body shape was checked")
                    };
                    self.scopes.truncate(scope_checkpoint);
                    expressions.push(ResolvedExpr {
                        kind: ResolvedExprKind::Function(ResolvedFunctionExpr {
                            pattern: pattern.into_inner(),
                            body,
                        }),
                        span,
                    });
                }
                ResolveTask::FinishTuple { count, span } => {
                    let split = expressions.len().checked_sub(count).ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            span,
                            "the resolver lost a tuple element",
                        )
                        .with_context(ResolveContext::WorkState {
                            part: "tuple-element",
                            problem: "missing",
                        })
                    })?;
                    let elements = expressions.split_off(split).into_vec();
                    expressions.push(ResolvedExpr {
                        kind: ResolvedExprKind::Tuple(elements),
                        span,
                    });
                }
            }
        }

        let result = expressions.pop_owned().ok_or_else(|| {
            error(
                ResolveReason::InternalState,
                initial_span,
                "the resolver produced no expression",
            )
            .with_context(ResolveContext::WorkState {
                part: "expression",
                problem: "missing",
            })
        })?;
        if !expressions.is_empty() || !declarations.is_empty() {
            return Err(error(
                ResolveReason::InternalState,
                initial_span,
                "the resolver retained incomplete expression state",
            )
            .with_context(ResolveContext::WorkState {
                part: "expression",
                problem: "incomplete",
            }));
        }
        Ok(result.into_inner())
    }

    // Keep request construction's owned temporaries out of the resolver driver
    // frame, which existing nested match resolution can reenter.
    fn finish_perform(
        effect: ResolvedEffectInstance,
        operation: crate::types::OperationId,
        spelling: &str,
        operation_span: Span,
        span: Span,
        expressions: &mut ResolvedExpressionBuffer,
    ) -> Result<(), ResolveError> {
        let operand = expressions.pop_owned().ok_or_else(|| {
            error(
                ResolveReason::InternalState,
                span,
                "request operand resolution produced no expression",
            )
        })?;
        expressions.push(ResolvedExpr {
            kind: ResolvedExprKind::Perform(ResolvedPerformExpr {
                effect,
                operation,
                spelling: spelling.to_owned(),
                operand: Box::new(operand.into_inner()),
                origin: Origin::Source(operation_span),
            }),
            span,
        });
        Ok(())
    }

    // Keep recursive match resolution outside the ordinary expression dispatch frame.
    fn visit_match_expression(
        &mut self,
        match_expression: &crate::surface::SurfaceMatchExpr,
        span: Span,
        expressions: &mut ResolvedExpressionBuffer,
    ) -> Result<(), ResolveError> {
        let scrutinee =
            ResolvedExpressionOwner::new(self.resolve_expr(&match_expression.scrutinee)?);
        let mut arms = ResolvedMatchArmBuffer(Vec::with_capacity(match_expression.arms.len()));
        for arm in &match_expression.arms {
            let scope_checkpoint = self.scopes.len();
            let (patterns, binders) =
                self.resolve_pattern_vector(std::slice::from_ref(&arm.pattern))?;
            let mut patterns = ResolvedPatternBuffer(patterns);
            let pattern = patterns.pop().ok_or_else(|| {
                error(
                    ResolveReason::InternalState,
                    arm.span,
                    "the resolver produced no match pattern",
                )
                .with_context(ResolveContext::WorkState {
                    part: "match-pattern",
                    problem: "missing",
                })
            })?;
            let pattern = ResolvedPatternOwner::new(pattern);
            self.push_binder_scope_many(&binders);
            let body = self
                .resolve_expr(&arm.body)
                .map(ResolvedExpressionOwner::new);
            self.scopes.truncate(scope_checkpoint);
            let body = body?;
            arms.0.push(ResolvedMatchArm {
                pattern: pattern.into_inner(),
                body: body.into_inner(),
                span: arm.span,
            });
        }
        expressions.push(ResolvedExpr {
            kind: ResolvedExprKind::Match(ResolvedMatchExpr {
                scrutinee: Box::new(scrutinee.into_inner()),
                arms: arms.into_vec(),
            }),
            span,
        });
        Ok(())
    }

    fn visit_expression<'a>(
        &mut self,
        expression: &'a SurfaceExpr,
        tasks: &mut ResolveTaskBuffer<'a>,
        expressions: &mut ResolvedExpressionBuffer,
    ) -> Result<(), ResolveError> {
        match &expression.kind {
            SurfaceExprKind::Cleanup(cleanup) => {
                self.type_work.charge(3).map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        expression.span,
                        "cleanup task storage exceeded its budget",
                    )
                })?;
                tasks.0.try_reserve(3).map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        expression.span,
                        "cleanup task storage could not be reserved",
                    )
                })?;
                tasks.push(ResolveTask::FinishCleanup {
                    span: expression.span,
                });
                tasks.push(ResolveTask::VisitBlock(&cleanup.body));
                tasks.push(ResolveTask::VisitExpr(&cleanup.action));
            }
            SurfaceExprKind::Registration(registration) => {
                let effect = self.resolve_effect_instance_parts(
                    &registration.effect.effect,
                    &registration.effect.arguments,
                    registration.effect.span,
                )?;
                self.type_work.charge(3).map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        expression.span,
                        "registration task storage exceeded its budget",
                    )
                })?;
                tasks.0.try_reserve(3).map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        expression.span,
                        "registration task storage could not be reserved",
                    )
                })?;
                tasks.push(ResolveTask::FinishRegistration {
                    effect,
                    span: expression.span,
                });
                tasks.push(ResolveTask::VisitBlock(&registration.body));
                tasks.push(ResolveTask::VisitExpr(&registration.transformer));
            }
            SurfaceExprKind::Hook(hook) => {
                let effect = self.resolve_effect_instance_parts(
                    &hook.effect.effect,
                    &hook.effect.arguments,
                    hook.effect.span,
                )?;
                self.type_work.charge(2).map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        expression.span,
                        "hook resolution task storage exceeded its budget",
                    )
                })?;
                tasks.0.try_reserve(2).map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        expression.span,
                        "hook resolution task storage could not be reserved",
                    )
                })?;
                tasks.push(ResolveTask::FinishHook {
                    effect,
                    span: expression.span,
                });
                tasks.push(ResolveTask::VisitBlock(&hook.body));
            }
            SurfaceExprKind::Resource(source) if self.resource_builtin(source.kind).is_none() => {
                let (builtin, message) = match source.kind {
                    crate::surface::SurfaceResourceKind::Cell => (
                        "@builtin.cell",
                        "resource acquisition requires a direct import of @builtin.cell",
                    ),
                    crate::surface::SurfaceResourceKind::NativeBuffer => (
                        "@builtin.native_buffer",
                        "resource acquisition requires a direct import of @builtin.native_buffer",
                    ),
                };
                let mut failure = error(
                    ResolveReason::ResourceBuiltinRequired,
                    expression.span,
                    message,
                );
                failure.0.expected = Some(builtin.to_owned());
                return Err(failure);
            }
            SurfaceExprKind::Resource(source) => {
                self.type_work.charge(2).map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        expression.span,
                        "resource resolution work exceeded its budget",
                    )
                })?;
                tasks.0.try_reserve(2).map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        expression.span,
                        "resource resolution work could not be reserved",
                    )
                })?;
                tasks.push(ResolveTask::ResourceInitializer {
                    source,
                    span: expression.span,
                });
                tasks.push(ResolveTask::VisitExpr(&source.initializer));
            }
            SurfaceExprKind::Integer(value) => expressions.push(ResolvedExpr {
                kind: ResolvedExprKind::Integer(value.clone()),
                span: expression.span,
            }),
            SurfaceExprKind::Boolean(value) => expressions.push(ResolvedExpr {
                kind: ResolvedExprKind::Boolean(*value),
                span: expression.span,
            }),
            SurfaceExprKind::Unit => expressions.push(ResolvedExpr {
                kind: ResolvedExprKind::Unit,
                span: expression.span,
            }),
            SurfaceExprKind::Name(name) => {
                let member = name.member();
                let is_qualified = matches!(name, SurfaceReference::Qualified(_));
                let (qualified_binding, qualified_constructor, qualified_withheld) =
                    if let Some(namespace) = self.imported_namespace(name)? {
                        (
                            namespace.terms.get(&member.text).copied(),
                            namespace.constructors.get(&member.text).copied(),
                            namespace
                                .withheld
                                .get(&(member.text.clone(), WithheldNamespace::Term))
                                .or_else(|| {
                                    namespace
                                        .withheld
                                        .get(&(member.text.clone(), WithheldNamespace::Constructor))
                                })
                                .copied(),
                        )
                    } else {
                        (None, None, None)
                    };
                let binding = if is_qualified {
                    qualified_binding
                } else {
                    self.scopes
                        .iter()
                        .rev()
                        .find_map(|scope| scope.get(&member.text))
                        .copied()
                        .or_else(|| self.method_names.get(&member.text).copied())
                };
                let unqualified_constructor = if binding.is_none() && !is_qualified {
                    charged_lexical_scope_lookup(
                        &self.lexical_constructor_scopes,
                        &member.text,
                        member.span,
                        &mut self.type_work,
                        "inline lexical constructor lookup exceeded its type-work budget",
                    )?
                    .or_else(|| self.constructor_names.get(&member.text).copied())
                } else {
                    None
                };
                if let Some(binding) = binding {
                    let term = binding.term;
                    let evidence_count = match term {
                        ResolvedTermName::Global(binder) => self
                            .global_requirement_counts
                            .get(&binder)
                            .copied()
                            .unwrap_or(0),
                        ResolvedTermName::Method(_) => 1,
                    };
                    self.constraint_work.charge(evidence_count).map_err(|()| {
                        error(
                            ResolveReason::ConstraintResourceExhausted,
                            expression.span,
                            "occurrence evidence slots exceeded the graph work budget",
                        )
                    })?;
                    let mut evidence = Vec::new();
                    evidence.try_reserve(evidence_count).map_err(|_| {
                        error(
                            ResolveReason::ConstraintResourceExhausted,
                            expression.span,
                            "occurrence evidence-slot storage exceeded the graph work budget",
                        )
                    })?;
                    evidence.extend((0..evidence_count).map(|_| EvidenceSlot::empty()));
                    expressions.push(ResolvedExpr {
                        kind: ResolvedExprKind::Occurrence(ResolvedOccurrence {
                            term,
                            spelling: member.text.clone(),
                            origin: Origin::Source(name.span()),
                            import_span: binding.import_span,
                            evidence: evidence.into_boxed_slice(),
                        }),
                        span: expression.span,
                    });
                } else if let Some(constructor) = qualified_constructor.or(unqualified_constructor)
                {
                    expressions.push(ResolvedExpr {
                        kind: ResolvedExprKind::Constructor(ResolvedConstructorOccurrence {
                            constructor,
                            spelling: member.text.clone(),
                            origin: Origin::Source(name.span()),
                        }),
                        span: expression.span,
                    });
                } else if is_qualified {
                    return Err(withheld_export_error(
                        member.span,
                        &member.text,
                        qualified_withheld,
                    ));
                } else {
                    if let Some(kind) = self
                        .targeted_withheld
                        .get(&(member.text.clone(), WithheldNamespace::Term))
                        .or_else(|| {
                            self.targeted_withheld
                                .get(&(member.text.clone(), WithheldNamespace::Constructor))
                        })
                        .copied()
                    {
                        return Err(withheld_export_error(member.span, &member.text, Some(kind)));
                    }
                    return Err(
                        if member.text.chars().next().is_some_and(char::is_uppercase) {
                            let mut diagnostic = Diagnostic::new(
                                ResolveReason::UnknownConstructor,
                                SourceLabel::new(member.span, "this constructor is not declared"),
                            );
                            diagnostic.found = Some(member.text.clone());
                            ResolveError(Box::new(diagnostic), Some(ResolveContext::Constructor))
                        } else {
                            lookup_error(
                                ResolveContext::Term,
                                member.span,
                                &member.text,
                                "this name is not in scope",
                            )
                        },
                    );
                }
            }
            SurfaceExprKind::Apply(application) => {
                tasks.push(ResolveTask::FinishApplication {
                    span: expression.span,
                });
                tasks.push(ResolveTask::VisitExpr(&application.argument));
                tasks.push(ResolveTask::VisitExpr(&application.function));
            }
            SurfaceExprKind::Add(binary) => {
                schedule_binary(BinaryKind::Add, expression.span, binary, tasks);
            }
            SurfaceExprKind::Multiply(binary) => {
                schedule_binary(BinaryKind::Multiply, expression.span, binary, tasks);
            }
            SurfaceExprKind::Equal(binary) => {
                schedule_binary(BinaryKind::Equal, expression.span, binary, tasks);
            }
            SurfaceExprKind::Block(block) => tasks.push(ResolveTask::VisitBlock(block)),
            SurfaceExprKind::Function(function) => {
                let (patterns, binders) =
                    self.resolve_pattern_vector(std::slice::from_ref(&function.parameter))?;
                let mut patterns = ResolvedPatternBuffer(patterns);
                let parameter = patterns.pop().ok_or_else(|| {
                    error(
                        ResolveReason::InternalState,
                        function.parameter.span,
                        "the resolver produced no function pattern",
                    )
                    .with_context(ResolveContext::WorkState {
                        part: "function-pattern",
                        problem: "missing",
                    })
                })?;
                let scope_checkpoint = self.scopes.len();
                self.push_binder_scope_many(&binders);
                tasks.push(ResolveTask::FinishFunction {
                    parameter: ResolvedPatternOwner::new(parameter),
                    scope_checkpoint,
                    span: expression.span,
                });
                tasks.push(ResolveTask::VisitBlock(&function.body));
            }
            SurfaceExprKind::Tuple(elements) => {
                tasks.push(ResolveTask::FinishTuple {
                    count: elements.len(),
                    span: expression.span,
                });
                tasks.extend(elements.iter().rev().map(ResolveTask::VisitExpr));
            }
            SurfaceExprKind::Match(match_expression) => {
                self.visit_match_expression(match_expression, expression.span, expressions)?;
            }
            SurfaceExprKind::Perform(request) => {
                let effect = self.resolve_effect_instance_parts(
                    &request.effect,
                    &request.arguments,
                    request.effect.span(),
                )?;
                let operation =
                    self.resolved_operation(effect.instance.effect(), &request.operation)?;
                self.type_work.charge(2).map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        expression.span,
                        "request operand work exceeded its type-work budget",
                    )
                })?;
                tasks.0.try_reserve(2).map_err(|_| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        expression.span,
                        "request operand work exceeded its type-work budget",
                    )
                })?;
                tasks.push(ResolveTask::FinishPerform {
                    effect,
                    operation,
                    spelling: &request.operation.text,
                    operation_span: request.operation.span,
                    span: expression.span,
                });
                tasks.push(ResolveTask::VisitExpr(&request.operand));
            }
            SurfaceExprKind::Handle(handler) => {
                let effect = self.resolve_effect_instance_parts(
                    &handler.effect.effect,
                    &handler.effect.arguments,
                    handler.effect.span,
                )?;
                let body = ResolvedExpressionOwner::new(self.resolve_expr(&handler.body)?);
                self.type_work.charge(handler.clauses.len()).map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        expression.span,
                        "handler clause storage exceeded its type-work budget",
                    )
                })?;
                let mut clauses = Vec::new();
                clauses
                    .try_reserve_exact(handler.clauses.len())
                    .map_err(|_| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            expression.span,
                            "handler clause storage exceeded its type-work budget",
                        )
                    })?;
                self.type_work.charge(handler.clauses.len()).map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        expression.span,
                        "handler clause traversal exceeded its type-work budget",
                    )
                })?;
                for clause in &handler.clauses {
                    let operation =
                        self.resolved_operation(effect.instance.effect(), &clause.operation)?;
                    let resume = ResumeId::new(self.next_resume);
                    self.next_resume = self.next_resume.checked_add(1).ok_or_else(|| {
                        identity_error(
                            ResolveIdentitySpace::Continuation,
                            clause.span,
                            "handler resume identity space is exhausted",
                        )
                    })?;
                    let (patterns, binders) =
                        self.resolve_pattern_vector(std::slice::from_ref(&clause.pattern))?;
                    let mut patterns = ResolvedPatternBuffer(patterns);
                    let pattern = ResolvedPatternOwner::new(patterns.pop().ok_or_else(|| {
                        error(
                            ResolveReason::InternalState,
                            clause.pattern.span,
                            "the resolver produced no handler pattern",
                        )
                        .with_context(ResolveContext::WorkState {
                            part: "handler-pattern",
                            problem: "missing",
                        })
                    })?);
                    let scope_checkpoint = self.scopes.len();
                    let resume_checkpoint = self.active_resumes.len();
                    self.push_binder_scope_many(&binders);
                    self.type_work.charge(1).map_err(|()| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            clause.span,
                            "handler resume scope exceeded its type-work budget",
                        )
                    })?;
                    self.active_resumes.try_reserve(1).map_err(|_| {
                        error(
                            ResolveReason::TypeResourceExhausted,
                            clause.span,
                            "handler resume scope exceeded its type-work budget",
                        )
                    })?;
                    self.active_resumes.push(resume);
                    let resolved_body = self
                        .resolve_expr(&clause.body)
                        .map(ResolvedExpressionOwner::new);
                    self.active_resumes.truncate(resume_checkpoint);
                    self.scopes.truncate(scope_checkpoint);
                    clauses.push(ResolvedHandlerClause {
                        operation,
                        spelling: clause.operation.text.clone(),
                        resume,
                        pattern: pattern.into_inner(),
                        body: resolved_body?.into_inner(),
                        span: clause.span,
                    });
                }
                expressions.push(ResolvedExpr {
                    kind: ResolvedExprKind::Handle(ResolvedHandleExpr {
                        hook_registration: None,
                        hook_root: None,
                        body: Box::new(body.into_inner()),
                        effect,
                        clauses,
                    }),
                    span: expression.span,
                });
            }
            SurfaceExprKind::Resume(value) => {
                let owner = self
                    .active_resumes
                    .last()
                    .copied()
                    .ok_or_else(|| continuation_outside_clause(expression.span, "resume"))?;
                let value = self.resolve_expr(value)?;
                expressions.push(ResolvedExpr {
                    kind: ResolvedExprKind::Resume(ResolvedResumeExpr {
                        owner: Some(owner),
                        value: Box::new(value),
                    }),
                    span: expression.span,
                });
            }
            SurfaceExprKind::Discard => {
                let owner = self
                    .active_resumes
                    .last()
                    .copied()
                    .ok_or_else(|| continuation_outside_clause(expression.span, "discard"))?;
                expressions.push(ResolvedExpr {
                    kind: ResolvedExprKind::Discard(crate::resolved::ResolvedDiscardExpr {
                        owner: Some(owner),
                    }),
                    span: expression.span,
                });
            }
        }
        Ok(())
    }
}

struct ResolvedBinderBuffer(Vec<Binder>);

impl Deref for ResolvedBinderBuffer {
    type Target = [Binder];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl ResolvedBinderBuffer {
    fn push(&mut self, binder: Binder) {
        self.0.push(binder);
    }

    fn into_vec(mut self) -> Vec<Binder> {
        std::mem::take(&mut self.0)
    }
}

impl Drop for ResolvedBinderBuffer {
    fn drop(&mut self) {
        for binder in self.0.drain(..) {
            discard_origin_iteratively(binder.origin);
        }
    }
}

struct PendingLexicalResolution<'a> {
    source: &'a crate::surface::SurfaceLexicalEvidence,
    id: crate::interface::LexicalEvidenceId,
    application: Option<ResolvedInterfaceApplication>,
    groups: ResolvedImplementationMethodGroupBuffer,
    equations: ResolvedEquationBuffer,
    next: usize,
    group_end: usize,
}

impl Drop for PendingLexicalResolution<'_> {
    fn drop(&mut self) {
        if let Some(application) = self.application.take() {
            discard_origin_iteratively(application.interface.origin);
            for argument in application.arguments.into_vec() {
                argument.discard_iteratively();
            }
        }
    }
}

enum ResolveTask<'a> {
    FinishPerform {
        effect: ResolvedEffectInstance,
        operation: crate::types::OperationId,
        spelling: &'a str,
        operation_span: Span,
        span: Span,
    },
    FinishCleanup {
        span: Span,
    },
    VisitExpr(&'a SurfaceExpr),
    FinishRegistration {
        effect: ResolvedEffectInstance,
        span: Span,
    },
    FinishHook {
        effect: ResolvedEffectInstance,
        span: Span,
    },
    ResourceInitializer {
        source: &'a crate::surface::SurfaceResourceExpr,
        span: Span,
    },
    FinishResource {
        kind: crate::surface::SurfaceResourceKind,
        identity: ResolvedTypeVariable,
        handle: Binder,
        initializer: Box<ResolvedExpressionOwner>,
        scope_checkpoint: usize,
        type_scope_checkpoint: usize,
        span: Span,
    },
    VisitBlock(&'a SurfaceBlock),
    VisitRecursiveGroup(&'a SurfaceRecursiveGroup),
    FinishApplication {
        span: crate::source::Span,
    },
    FinishBinary {
        kind: BinaryKind,
        operator_span: crate::source::Span,
        span: crate::source::Span,
    },
    FinishBinding(&'a SurfaceBinding),
    FinishLocalNewtype(&'a SurfaceTypeDeclaration),
    VisitLexicalEvidence(&'a crate::surface::SurfaceLexicalEvidence),
    ContinueLexicalEvidence(Box<PendingLexicalResolution<'a>>),
    FinishLexicalEquation {
        state: Box<PendingLexicalResolution<'a>>,
        patterns: ResolvedPatternBuffer,
        scope_checkpoint: usize,
    },
    FinishRecursiveGroup {
        group: &'a SurfaceRecursiveGroup,
        binders: ResolvedBinderBuffer,
    },
    FinishBlock {
        declaration_start: usize,
        scope_checkpoint: usize,
        nominal_scope_checkpoint: usize,
        constructor_scope_checkpoint: usize,
        span: crate::source::Span,
    },
    FinishFunction {
        parameter: ResolvedPatternOwner,
        scope_checkpoint: usize,
        span: crate::source::Span,
    },
    FinishTuple {
        count: usize,
        span: crate::source::Span,
    },
}

struct ResolveTaskBuffer<'a>(Vec<ResolveTask<'a>>);

impl<'a> Deref for ResolveTaskBuffer<'a> {
    type Target = Vec<ResolveTask<'a>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'a> ResolveTaskBuffer<'a> {
    fn push(&mut self, task: ResolveTask<'a>) {
        self.0.push(task);
    }

    fn pop(&mut self) -> Option<ResolveTask<'a>> {
        self.0.pop()
    }

    fn extend(&mut self, tasks: impl IntoIterator<Item = ResolveTask<'a>>) {
        self.0.extend(tasks);
    }
}

impl Drop for ResolveTaskBuffer<'_> {
    fn drop(&mut self) {
        self.0.clear();
    }
}

impl ResolveTask<'_> {
    fn span(&self) -> crate::source::Span {
        match self {
            Self::VisitExpr(expression) => expression.span,
            Self::VisitBlock(block) => block.span,
            Self::VisitRecursiveGroup(group) => group.span,
            Self::FinishApplication { span }
            | Self::FinishPerform { span, .. }
            | Self::FinishCleanup { span }
            | Self::FinishHook { span, .. }
            | Self::FinishRegistration { span, .. }
            | Self::ResourceInitializer { span, .. }
            | Self::FinishResource { span, .. }
            | Self::FinishBinary { span, .. }
            | Self::FinishBlock { span, .. }
            | Self::FinishFunction { span, .. }
            | Self::FinishTuple { span, .. } => *span,
            Self::FinishBinding(binding) => binding.span,
            Self::FinishLocalNewtype(declaration) => declaration.span,
            Self::VisitLexicalEvidence(source) => source.span,
            Self::ContinueLexicalEvidence(state) | Self::FinishLexicalEquation { state, .. } => {
                state.source.span
            }
            Self::FinishRecursiveGroup { group, .. } => group.span,
        }
    }
}

#[derive(Clone, Copy)]
enum BinaryKind {
    Add,
    Multiply,
    Equal,
}

impl BinaryKind {
    fn finish(self, binary: ResolvedBinaryExpr) -> ResolvedExprKind {
        match self {
            Self::Add => ResolvedExprKind::Add(binary),
            Self::Multiply => ResolvedExprKind::Multiply(binary),
            Self::Equal => ResolvedExprKind::Equal(binary),
        }
    }
}

fn schedule_binary<'a>(
    kind: BinaryKind,
    span: crate::source::Span,
    binary: &'a BinaryExpr,
    tasks: &mut ResolveTaskBuffer<'a>,
) {
    tasks.push(ResolveTask::FinishBinary {
        kind,
        operator_span: binary.operator_span,
        span,
    });
    tasks.push(ResolveTask::VisitExpr(&binary.right));
    tasks.push(ResolveTask::VisitExpr(&binary.left));
}

fn take_expression_pair(
    expressions: &mut ResolvedExpressionBuffer,
    span: crate::source::Span,
) -> Result<(ResolvedExpr, ResolvedExpr), ResolveError> {
    let right = expressions.pop_owned().ok_or_else(|| {
        error(
            ResolveReason::InternalState,
            span,
            "the resolver lost a right operand",
        )
        .with_context(ResolveContext::WorkState {
            part: "right-operand",
            problem: "missing",
        })
    })?;
    let left = expressions.pop_owned().ok_or_else(|| {
        error(
            ResolveReason::InternalState,
            span,
            "the resolver lost a left operand",
        )
        .with_context(ResolveContext::WorkState {
            part: "left-operand",
            problem: "missing",
        })
    })?;
    Ok((left.into_inner(), right.into_inner()))
}

fn identity_error(space: ResolveIdentitySpace, span: Span, message: &str) -> ResolveError {
    let mut failure = error(ResolveReason::BinderIdExhausted, span, message);
    failure.1 = Some(ResolveContext::IdentityExhaustion(space));
    failure
}

fn kind_context_error(
    context: crate::kind::KindFailureContext,
    span: crate::source::Span,
    message: &str,
) -> ResolveError {
    let mut failure = error(ResolveReason::InternalState, span, message);
    failure.1 = Some(ResolveContext::Kind(context));
    failure
}

fn error(reason: ResolveReason, span: crate::source::Span, message: &str) -> ResolveError {
    Diagnostic::new(reason, SourceLabel::new(span, message)).into()
}

fn lookup_error(
    scope: ResolveContext,
    span: crate::source::Span,
    name: &str,
    message: &str,
) -> ResolveError {
    let reason = match scope {
        ResolveContext::Term | ResolveContext::EffectOperation => ResolveReason::UnknownName,
        ResolveContext::Type
        | ResolveContext::EffectRowParameter
        | ResolveContext::InterfaceParameter => ResolveReason::UnknownType,
        ResolveContext::Constructor => ResolveReason::UnknownConstructor,
        ResolveContext::Interface => ResolveReason::UnknownInterface,
        ResolveContext::Effect | ResolveContext::ExportedEffect => ResolveReason::UnknownEffect,
        ResolveContext::MixedTypeRowRoles => ResolveReason::TypeKind,
        ResolveContext::IdentityExhaustion(_) => ResolveReason::BinderIdExhausted,
        ResolveContext::Kind(_)
        | ResolveContext::DependencySummaryMismatch
        | ResolveContext::DependencySummaryInvalid
        | ResolveContext::DeclarationOrder { .. }
        | ResolveContext::WorkState { .. }
        | ResolveContext::MissingFileScope
        | ResolveContext::MissingLexicalScope
        | ResolveContext::MissingNominalScope
        | ResolveContext::MissingConstructorScope => ResolveReason::InternalState,
        ResolveContext::PrivateExport
        | ResolveContext::MissingExport
        | ResolveContext::MissingModuleAlias => ResolveReason::UnavailableExport,
    };
    let mut diagnostic = Diagnostic::new(reason, SourceLabel::new(span, message));
    diagnostic.found = Some(name.to_owned());
    ResolveError(Box::new(diagnostic), Some(scope))
}

fn imported_nominal_merge_error(
    failure: ImportedNominalMergeFailure,
    span: crate::source::Span,
) -> ResolveError {
    match failure {
        ImportedNominalMergeFailure::Kind(context) => kind_context_error(
            context,
            span,
            "imported routes disagree about nominal metadata",
        ),
        ImportedNominalMergeFailure::Conflict => error(
            ResolveReason::InternalState,
            span,
            "imported routes disagree about nominal metadata",
        ),
        ImportedNominalMergeFailure::TypeResource => error(
            ResolveReason::TypeResourceExhausted,
            span,
            "imported nominal authentication exceeded its type-work budget",
        ),
        ImportedNominalMergeFailure::ConstraintResource => error(
            ResolveReason::ConstraintResourceExhausted,
            span,
            "imported nominal authentication exceeded its constraint-work budget",
        ),
    }
}

fn imported_fact_comparison_error(
    failure: ResolvedBuildFailure,
    span: crate::source::Span,
) -> ResolveError {
    match failure {
        ResolvedBuildFailure::Kind(context) => kind_context_error(
            context,
            span,
            "alternate imported-fact comparison encountered invalid retained state",
        ),
        ResolvedBuildFailure::TypeResource => error(
            ResolveReason::TypeResourceExhausted,
            span,
            "alternate imported-fact comparison exceeded its type-work budget",
        ),
        ResolvedBuildFailure::ConstraintResource => error(
            ResolveReason::ConstraintResourceExhausted,
            span,
            "alternate imported-fact comparison exceeded its constraint-work budget",
        ),
        ResolvedBuildFailure::InvalidState => error(
            ResolveReason::InternalState,
            span,
            "alternate imported-fact comparison encountered invalid retained state",
        ),
    }
}

#[cfg(test)]
fn same_kinded_parameters_with_constraint_budget(
    parameters: &[(TypeVariableId, Kind)],
    binders: &[ResolvedTypeVariable],
    budget: &mut InterfaceConstraintBudget,
) -> Result<bool, ()> {
    if parameters.len() != binders.len() {
        return Ok(false);
    }
    for ((parameter, kind), binder) in parameters.iter().zip(binders) {
        budget.charge(1)?;
        if *parameter != binder.id {
            return Ok(false);
        }
        if !same_kind_with_charge(kind, &binder.kind, || budget.charge(1))? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn same_kinded_parameters_with_two_binder_slices(
    parameters: &[(TypeVariableId, Kind)],
    first: &[ResolvedTypeVariable],
    second: &[ResolvedTypeVariable],
    budget: &mut InterfaceConstraintBudget,
) -> Result<bool, ()> {
    let expected = first.len().checked_add(second.len()).ok_or(())?;
    if parameters.len() != expected {
        return Ok(false);
    }
    for ((parameter, kind), binder) in parameters.iter().zip(first.iter().chain(second)) {
        budget.charge(1)?;
        if *parameter != binder.id {
            return Ok(false);
        }
        if !same_kind_with_charge(kind, &binder.kind, || budget.charge(1))? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn import_conflict(span: crate::source::Span, spelling: &str) -> ResolveError {
    let mut diagnostic = Diagnostic::new(
        ResolveReason::ImportConflict,
        SourceLabel::new(span, "this file-wide name is already bound"),
    );
    diagnostic.found = Some(spelling.to_owned());
    diagnostic.into()
}

fn withheld_export_error(
    span: crate::source::Span,
    spelling: &str,
    withheld: Option<WithheldImport>,
) -> ResolveError {
    let (reason, message, context) = match withheld.map(|withheld| withheld.kind) {
        Some(WithheldExportKind::Private) => (
            ResolveReason::UnavailableExport,
            "this declaration is private to its defining module",
            Some(ResolveContext::PrivateExport),
        ),
        Some(WithheldExportKind::OpaqueConstructor) => (
            ResolveReason::OpaqueConstructor,
            "this constructor belongs to an opaque type",
            None,
        ),
        None => (
            ResolveReason::UnavailableExport,
            "the dependency exports no declaration with this spelling",
            Some(ResolveContext::MissingExport),
        ),
    };
    let mut diagnostic = Diagnostic::new(reason, SourceLabel::new(span, message));
    if let Some(declaration) = withheld.and_then(|withheld| withheld.declaration) {
        diagnostic.related.push(SourceLabel::new(
            declaration,
            "the inaccessible declaration is here",
        ));
    }
    diagnostic.found = Some(spelling.to_owned());
    ResolveError(Box::new(diagnostic), context)
}

fn unknown_interface_error(span: crate::source::Span, spelling: &str) -> ResolveError {
    let mut diagnostic = Diagnostic::new(
        ResolveReason::UnknownInterface,
        SourceLabel::new(span, "this interface is not declared"),
    );
    diagnostic.found = Some(spelling.to_owned());
    ResolveError(Box::new(diagnostic), Some(ResolveContext::Interface))
}

fn unknown_determination_parameter_error(name: &SurfaceName) -> ResolveError {
    let mut diagnostic = Diagnostic::new(
        ResolveReason::UnknownType,
        SourceLabel::new(
            name.span,
            "this name is not a parameter of the owning interface",
        ),
    );
    diagnostic.expected = Some("interface parameter".to_owned());
    diagnostic.found = Some(name.text.clone());
    ResolveError(
        Box::new(diagnostic),
        Some(ResolveContext::InterfaceParameter),
    )
}

fn interface_kind_error(span: crate::source::Span, spelling: &str) -> ResolveError {
    let mut diagnostic = Diagnostic::new(
        ResolveReason::InterfaceKind,
        SourceLabel::new(span, "this name does not denote an interface"),
    );
    diagnostic.expected = Some("interface".to_owned());
    diagnostic.found = Some(spelling.to_owned());
    diagnostic.into()
}

fn continuation_outside_clause(span: crate::source::Span, operation: &str) -> ResolveError {
    let mut failure = error(
        ResolveReason::ResumeOutsideClause,
        span,
        "resume and discard are available only inside an operation clause",
    );
    failure.0.found = Some(operation.to_owned());
    failure
}

fn effect_kind_error(span: crate::source::Span, spelling: &str) -> ResolveError {
    let mut diagnostic = Diagnostic::new(
        ResolveReason::EffectKind,
        SourceLabel::new(span, "this uppercase name does not denote an effect"),
    );
    diagnostic.expected = Some("effect".to_owned());
    diagnostic.found = Some(spelling.to_owned());
    diagnostic.into()
}

fn type_kind_error(span: crate::source::Span, spelling: &str) -> ResolveError {
    let mut diagnostic = Diagnostic::new(
        ResolveReason::TypeKind,
        SourceLabel::new(span, "an interface cannot be used as a value type"),
    );
    diagnostic.expected = Some("type".to_owned());
    diagnostic.found = Some(spelling.to_owned());
    diagnostic.into()
}

fn charged_lexical_scope_lookup<Identity: Copy>(
    scopes: &[HashMap<String, Identity>],
    spelling: &str,
    span: crate::source::Span,
    budget: &mut TypeWorkBudget,
    message: &'static str,
) -> Result<Option<Identity>, ResolveError> {
    for scope in scopes.iter().rev() {
        budget
            .charge(1)
            .map_err(|()| error(ResolveReason::TypeResourceExhausted, span, message))?;
        if let Some(identity) = scope.get(spelling).copied() {
            return Ok(Some(identity));
        }
    }
    Ok(None)
}

fn try_clone_resolution_string(
    value: &str,
    span: crate::source::Span,
    message: &'static str,
) -> Result<String, ResolveError> {
    let mut retained = String::new();
    retained
        .try_reserve_exact(value.len())
        .map_err(|_| error(ResolveReason::TypeResourceExhausted, span, message))?;
    retained.push_str(value);
    Ok(retained)
}

fn validate_interface_type_parameters(
    parameters: &[SurfaceTypeParameter],
    owner_span: crate::source::Span,
    budget: &mut TypeWorkBudget,
) -> Result<(), ResolveError> {
    budget.charge(parameters.len()).map_err(|()| {
        error(
            ResolveReason::TypeResourceExhausted,
            owner_span,
            "interface type-parameter validation exceeded its type-work budget",
        )
    })?;
    let mut first = HashMap::new();
    first.try_reserve(parameters.len()).map_err(|_| {
        error(
            ResolveReason::TypeResourceExhausted,
            owner_span,
            "interface type-parameter validation could not reserve duplicate storage",
        )
    })?;
    for parameter in parameters {
        if let Some(first_span) = first.insert(parameter.name.text.as_str(), parameter.name.span) {
            let mut diagnostic = Diagnostic::new(
                ResolveReason::DuplicateTypeParameter,
                SourceLabel::new(
                    parameter.name.span,
                    "this type parameter is already declared",
                ),
            );
            diagnostic.related.push(SourceLabel::new(
                first_span,
                "the first type parameter is here",
            ));
            diagnostic.found = Some(parameter.name.text.clone());
            return Err(diagnostic.into());
        }
    }
    Ok(())
}

fn validate_explicit_type_parameters(
    parameters: Option<&[SurfaceTypeParameter]>,
) -> Result<HashSet<&str>, ResolveError> {
    let Some(parameters) = parameters else {
        return Ok(HashSet::new());
    };
    let mut declared = HashSet::with_capacity(parameters.len());
    let mut first = HashMap::with_capacity(parameters.len());
    for parameter in parameters {
        if let Some(first_span) = first.insert(parameter.name.text.as_str(), parameter.name.span) {
            let mut diagnostic = Diagnostic::new(
                ResolveReason::DuplicateTypeParameter,
                SourceLabel::new(
                    parameter.name.span,
                    "this type parameter is already declared",
                ),
            );
            diagnostic.related.push(SourceLabel::new(
                first_span,
                "the first type parameter is here",
            ));
            diagnostic.found = Some(parameter.name.text.clone());
            return Err(diagnostic.into());
        }
        declared.insert(parameter.name.text.as_str());
    }
    Ok(declared)
}

fn validate_method_type_parameters<'a>(
    owners: &'a [SurfaceTypeParameter],
    parameters: Option<&'a [SurfaceTypeParameter]>,
    owner_span: crate::source::Span,
    budget: &mut TypeWorkBudget,
) -> Result<HashSet<&'a str>, ResolveError> {
    let Some(parameters) = parameters else {
        budget.charge(owners.len()).map_err(|()| {
            error(
                ResolveReason::TypeResourceExhausted,
                owner_span,
                "method type-parameter owner validation exceeded its type-work budget",
            )
        })?;
        let mut declared = HashSet::new();
        declared.try_reserve(owners.len()).map_err(|_| {
            error(
                ResolveReason::TypeResourceExhausted,
                owner_span,
                "method type-parameter validation could not reserve owner storage",
            )
        })?;
        for owner in owners {
            declared.insert(owner.name.text.as_str());
        }
        return Ok(declared);
    };
    let entry_count = parameters.len().checked_add(owners.len()).ok_or_else(|| {
        error(
            ResolveReason::TypeResourceExhausted,
            owner_span,
            "method type-parameter validation size is not representable",
        )
    })?;
    let validation_work = entry_count.checked_mul(2).ok_or_else(|| {
        error(
            ResolveReason::TypeResourceExhausted,
            owner_span,
            "method type-parameter validation size is not representable",
        )
    })?;
    budget.charge(validation_work).map_err(|()| {
        error(
            ResolveReason::TypeResourceExhausted,
            owner_span,
            "method type-parameter validation exceeded its type-work budget",
        )
    })?;
    let mut declared = HashSet::new();
    declared.try_reserve(entry_count).map_err(|_| {
        error(
            ResolveReason::TypeResourceExhausted,
            owner_span,
            "method type-parameter validation could not reserve declaration storage",
        )
    })?;
    let mut first = HashMap::new();
    first.try_reserve(entry_count).map_err(|_| {
        error(
            ResolveReason::TypeResourceExhausted,
            owner_span,
            "method type-parameter validation could not reserve duplicate storage",
        )
    })?;
    for owner in owners {
        declared.insert(owner.name.text.as_str());
        first.insert(owner.name.text.as_str(), owner.name.span);
    }
    for parameter in parameters {
        if let Some(first_span) = first.insert(parameter.name.text.as_str(), parameter.name.span) {
            let mut diagnostic = Diagnostic::new(
                ResolveReason::DuplicateTypeParameter,
                SourceLabel::new(
                    parameter.name.span,
                    "this type parameter is already declared",
                ),
            );
            diagnostic.related.push(SourceLabel::new(
                first_span,
                "the first type parameter is here",
            ));
            diagnostic.found = Some(parameter.name.text.clone());
            return Err(diagnostic.into());
        }
        declared.insert(parameter.name.text.as_str());
    }
    Ok(declared)
}

#[cfg(test)]
thread_local! {
    static SURFACE_KIND_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static SURFACE_KIND_ARROWS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static SURFACE_KIND_REBUILT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
fn reset_surface_kind_conversion_counts() {
    SURFACE_KIND_VISITS.set(0);
    SURFACE_KIND_ARROWS.set(0);
    SURFACE_KIND_REBUILT.set(0);
}

#[cfg(test)]
fn surface_kind_conversion_counts() -> (usize, usize, usize) {
    (
        SURFACE_KIND_VISITS.get(),
        SURFACE_KIND_ARROWS.get(),
        SURFACE_KIND_REBUILT.get(),
    )
}

fn surface_kind_to_kind(root: &SurfaceKind, budget: &mut TypeWorkBudget) -> Result<Kind, ()> {
    enum Task<'a> {
        Visit(&'a SurfaceKind),
        Arrow,
    }

    // Every source node has one lifecycle slot. A leaf moves from `Visit` to
    // one rebuilt `Kind::Type`; a function node moves from `Visit` through one
    // `Arrow` continuation to one rebuilt `Kind::Arrow`. Only `Visit` is new
    // semantic work and is charged exactly once. Therefore D source arrows and
    // D+1 leaves have the complete boundary N=2D+1; continuation and rebuilt
    // states do not add a second traversal charge.
    let mut work = vec![Task::Visit(root)];
    let mut rebuilt = Vec::new();
    while let Some(task) = work.pop() {
        match task {
            Task::Visit(kind) => {
                #[cfg(test)]
                SURFACE_KIND_VISITS.set(SURFACE_KIND_VISITS.get().saturating_add(1));
                budget.charge(1)?;
                match &kind.kind {
                    SurfaceKindKind::Type => {
                        rebuilt.push(Kind::Type);
                        #[cfg(test)]
                        SURFACE_KIND_REBUILT.set(SURFACE_KIND_REBUILT.get().saturating_add(1));
                    }
                    SurfaceKindKind::EffectRow => {
                        rebuilt.push(Kind::EffectRow);
                        #[cfg(test)]
                        SURFACE_KIND_REBUILT.set(SURFACE_KIND_REBUILT.get().saturating_add(1));
                    }
                    SurfaceKindKind::Function { domain, codomain } => {
                        work.push(Task::Arrow);
                        work.push(Task::Visit(codomain));
                        work.push(Task::Visit(domain));
                    }
                }
            }
            Task::Arrow => {
                #[cfg(test)]
                SURFACE_KIND_ARROWS.set(SURFACE_KIND_ARROWS.get().saturating_add(1));
                let codomain = rebuilt.pop().ok_or(())?;
                let domain = rebuilt.pop().ok_or(())?;
                rebuilt.push(Kind::Arrow(Box::new(domain), Box::new(codomain)));
                #[cfg(test)]
                SURFACE_KIND_REBUILT.set(SURFACE_KIND_REBUILT.get().saturating_add(1));
            }
        }
    }
    rebuilt.pop().ok_or(())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FreeTypeNameRole {
    Type,
    EffectRow,
}

struct FreeTypeName {
    name: SurfaceName,
    role: FreeTypeNameRole,
}

fn retain_free_type_name<'a>(
    name: &'a SurfaceName,
    role: FreeTypeNameRole,
    seen: &mut HashMap<&'a str, Option<FreeTypeNameRole>>,
    output: &mut Vec<FreeTypeName>,
    reject_mixed_roles: bool,
) -> Result<(), ResolveError> {
    match seen.entry(name.text.as_str()) {
        std::collections::hash_map::Entry::Vacant(entry) => {
            entry.insert(Some(role));
            output.push(FreeTypeName {
                name: name.clone(),
                role,
            });
            Ok(())
        }
        std::collections::hash_map::Entry::Occupied(entry) => match entry.get() {
            Some(existing) if reject_mixed_roles && *existing != role => Err(lookup_error(
                ResolveContext::MixedTypeRowRoles,
                name.span,
                &name.text,
                "this parameter name is used both as an ordinary type and as an effect-row tail",
            )),
            None | Some(_) => Ok(()),
        },
    }
}

#[allow(
    clippy::too_many_arguments,
    reason = "free-name discovery keeps the reviewed omitted-global correction in one pass"
)]
fn collect_free_type_names<'a>(
    root: &'a SurfaceType,
    nominals: &HashMap<String, NominalTypeId>,
    interfaces: &HashMap<String, InterfaceId>,
    declared: &HashSet<&str>,
    seen: &mut HashMap<&'a str, Option<FreeTypeNameRole>>,
    output: &mut Vec<FreeTypeName>,
    reject_mixed_roles: bool,
    budget: &mut TypeWorkBudget,
) -> Result<(), ResolveError> {
    enum Task<'a> {
        Visit(&'a SurfaceType),
        Slice(std::slice::Iter<'a, SurfaceType>),
        RowTail(&'a SurfaceName),
    }

    let mut work = vec![Task::Visit(root)];
    while let Some(task) = work.pop() {
        let ty = match task {
            Task::Visit(ty) => ty,
            Task::Slice(mut remaining) => {
                if let Some(next) = remaining.next() {
                    work.push(Task::Slice(remaining));
                    work.push(Task::Visit(next));
                }
                continue;
            }
            Task::RowTail(tail) => {
                budget.charge(1).map_err(|()| {
                    error(
                        ResolveReason::TypeResourceExhausted,
                        tail.span,
                        "free type discovery exceeded its work budget",
                    )
                })?;
                retain_free_type_name(
                    tail,
                    FreeTypeNameRole::EffectRow,
                    seen,
                    output,
                    reject_mixed_roles,
                )?;
                continue;
            }
        };
        budget.charge(1).map_err(|()| {
            error(
                ResolveReason::TypeResourceExhausted,
                ty.span,
                "free type discovery exceeded its work budget",
            )
        })?;
        match &ty.kind {
            SurfaceTypeKind::Named(name) => {
                let SurfaceReference::Unqualified(name) = name else {
                    continue;
                };
                if declared.contains(name.text.as_str())
                    || (!nominals.contains_key(&name.text) && !interfaces.contains_key(&name.text))
                {
                    retain_free_type_name(
                        name,
                        FreeTypeNameRole::Type,
                        seen,
                        output,
                        reject_mixed_roles,
                    )?;
                }
            }
            SurfaceTypeKind::Application {
                constructor,
                arguments,
            } => {
                if let SurfaceReference::Unqualified(constructor) = constructor
                    && (declared.contains(constructor.text.as_str())
                        || (!nominals.contains_key(&constructor.text)
                            && !interfaces.contains_key(&constructor.text)))
                {
                    retain_free_type_name(
                        constructor,
                        FreeTypeNameRole::Type,
                        seen,
                        output,
                        reject_mixed_roles,
                    )?;
                }
                work.push(Task::Slice(arguments.iter()));
            }
            SurfaceTypeKind::Tuple(elements) => work.push(Task::Slice(elements.iter())),
            SurfaceTypeKind::Function(function) => {
                if let Some(effects) = &function.effects {
                    if let Some(tail) = &effects.tail {
                        work.push(Task::RowTail(tail));
                    }
                    for effect in effects.effects.iter().rev() {
                        work.push(Task::Slice(effect.arguments.iter()));
                    }
                }
                work.push(Task::Visit(&function.codomain));
                work.push(Task::Visit(&function.domain));
            }
            SurfaceTypeKind::Int | SurfaceTypeKind::Bool | SurfaceTypeKind::Unit => {}
        }
    }
    Ok(())
}

#[cfg(test)]
mod module_tests;

#[cfg(test)]
mod tests {
    #[test]
    fn imported_kind_context_reaches_presentation() {
        use crate::{
            message::{Catalogue, Locale},
            presentation::{compile_resolve_diagnostic, write_human, write_json},
        };
        let declaration = crate::source::SourceFile::new("declaration.ash", "binder").unwrap();
        let importer = crate::source::SourceFile::new("importer.ash", "import").unwrap();
        let origin = declaration
            .span(crate::source::ByteRange::new(0, 6).unwrap())
            .unwrap();
        let import = importer
            .span(crate::source::ByteRange::new(0, 6).unwrap())
            .unwrap();
        let kind = Kind::Type;
        let mut environments = crate::kind::KindEnvironments::new();
        let identity = TypeVariableId::new(0);
        environments
            .insert_declared(identity, &kind, origin, &mut TypeWorkBudget::with_limit(1))
            .unwrap();
        let failure = environments
            .insert_declared(identity, &kind, origin, &mut TypeWorkBudget::with_limit(1))
            .unwrap_err();
        let context = failure.internal_context().unwrap();
        for span in [origin, import] {
            for failure in [
                imported_fact_comparison_error(ResolvedBuildFailure::Kind(context), span),
                imported_nominal_merge_error(ImportedNominalMergeFailure::Kind(context), span),
                kind_context_error(context, span, "ignored legacy description"),
            ] {
                assert_eq!(failure.reason, ResolveReason::InternalState);
                assert_eq!(failure.kind_context(), Some(context));
                let view =
                    compile_resolve_diagnostic(&failure, &[&declaration, &importer]).unwrap();
                for locale in [Locale::English, Locale::Bulgarian] {
                    let mut output = Vec::new();
                    write_human(&mut output, &view, &Catalogue::new(locale).unwrap()).unwrap();
                    if locale == Locale::English {
                        assert!(
                            String::from_utf8(output)
                                .unwrap()
                                .contains("duplicate type-variable identity")
                        );
                    }
                }
                let mut output = Vec::new();
                write_json(&mut output, &view).unwrap();
                let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
                assert_eq!(json["responsibility"], "compiler");
                assert_eq!(json["facts"][0]["name"], "kind_cause");
                assert_eq!(json["facts"][0]["value"], "duplicate-binder");
                let labels = json["labels"].as_array().unwrap();
                assert_eq!(labels.len(), if span == origin { 1 } else { 2 });
                if span != origin {
                    assert_eq!(labels[1]["relationship"], "kind_failure_origin");
                }
                assert!(compile_resolve_diagnostic(&failure, &[&importer]).is_err());
            }
        }
    }
    use std::{
        fs,
        path::{Path, PathBuf},
        sync::atomic::{AtomicU64, Ordering},
    };

    use super::*;
    use crate::elaborate::check_module;
    use crate::module::{ModuleRoots, load_module_graph};
    use crate::source::{ByteRange, SourceFile};
    use crate::surface::{
        SurfaceDefinitionKind, SurfaceExprKind, SurfaceLocalDeclaration, SurfaceName,
        SurfaceTypeKind,
    };
    use crate::types::{TYPE_WORK_LIMIT, kind_node_charge_visits, reset_kind_node_charge_visits};
    use crate::{
        lexer::lex,
        parser::{parse, project_module},
    };

    static IMPORT_BUDGET_FIXTURE_IDS: AtomicU64 = AtomicU64::new(0);

    #[test]
    fn registration_resolution_retains_initializer_and_completion_contract() {
        {
            let expression = "register Adjust increment {\n3\n}";
            let source = format!(
                "effect Adjust {{\npublish : Int -> Int\n}}\nincrement : Int -> Int\nincrement value = value + 1\nmain : Unit -> Int\nmain () = {expression}\n"
            );
            let fixture = ImportBudgetFixture::create(&source, "");
            let graph = load_module_graph(&fixture.0.join("entry.ash"), &ModuleRoots::empty())
                .expect("hook syntax should load");
            let entry = graph.module(graph.entry()).unwrap();
            let resolved = resolve_module(entry, &[]).unwrap();
            let ResolvedDefinitionKind::Equational(main) = &resolved.definitions()[1].kind else {
                panic!("equational main")
            };
            let ResolvedExprKind::Block(block) = &main.equations[0].body.kind else {
                panic!("initializer binding")
            };
            let [ResolvedLocalDeclaration::Binding(initializer)] = &*block.declarations else {
                panic!("one initializer")
            };
            let ResolvedExprKind::Handle(handler) = &block.result.kind else {
                panic!("registration handler")
            };
            let contract = handler
                .hook_registration
                .as_ref()
                .expect("retained registration contract");
            let ResolvedPatternKind::Binder(callback) = &initializer.pattern.kind else {
                panic!("callback binder")
            };
            assert_eq!(callback.id, contract.callback);
            assert!(matches!(
                initializer.initializer.kind,
                ResolvedExprKind::Occurrence(_)
            ));
        }
    }

    #[test]
    fn hook_identity_retention_is_exact_and_disposes_failed_deep_inputs() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("hook-retention", "hook Adjust { 42 }").unwrap();
                let span = source.span(ByteRange::new(0, 18).unwrap()).unwrap();
                let run = |limit| {
                    let mut resolver = Resolver::with_type_work(
                        ModuleId::new(0),
                        TypeWorkBudget::with_limit(limit),
                    );
                    let mut argument = Type::Unit;
                    for _ in 0..32_000 {
                        argument = Type::Function(Box::new(Type::Unit), Box::new(argument));
                    }
                    let effect = ResolvedEffectInstance {
                        instance: EffectInstance::new(
                            EffectId::new(ModuleId::new(0), 0),
                            Box::new([argument]),
                        ),
                        argument_provenance: Box::new([]),
                        origin: Origin::Source(span),
                        span,
                    };
                    let mut expression = ResolvedExpr {
                        kind: ResolvedExprKind::Unit,
                        span,
                    };
                    for _ in 0..32_000 {
                        expression = ResolvedExpr {
                            kind: ResolvedExprKind::Tuple(vec![expression]),
                            span,
                        };
                    }
                    let result = resolver.finish_hook(
                        effect,
                        span,
                        ResolvedExpressionOwner::new(expression),
                    );
                    let work = resolver.type_work.used();
                    match result {
                        Ok(expression) => {
                            drop(ResolvedExpressionOwner::new(expression));
                            Ok(work)
                        }
                        Err(error) => Err(error.reason),
                    }
                };
                let exact = run(usize::MAX).unwrap();
                for limit in [0, 6, exact - 1] {
                    assert_eq!(run(limit), Err(ResolveReason::TypeResourceExhausted));
                }
                for _ in 0..2 {
                    assert_eq!(run(exact), Ok(exact));
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn registration_retention_is_exact_and_disposes_failed_deep_inputs() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let source =
                    SourceFile::new("registration-retention", "register Adjust callback { 42 }")
                        .unwrap();
                let span = source.span(ByteRange::new(0, 31).unwrap()).unwrap();
                let run = |limit| {
                    let mut resolver = Resolver::with_type_work(
                        ModuleId::new(0),
                        TypeWorkBudget::with_limit(limit),
                    );
                    let mut argument = Type::Unit;
                    for _ in 0..32_000 {
                        argument = Type::Function(Box::new(Type::Unit), Box::new(argument));
                    }
                    let effect = ResolvedEffectInstance {
                        instance: EffectInstance::new(
                            EffectId::new(ModuleId::new(0), 0),
                            Box::new([argument, Type::Bool]),
                        ),
                        argument_provenance: Box::new([]),
                        origin: Origin::Source(span),
                        span,
                    };
                    let mut expression = ResolvedExpr {
                        kind: ResolvedExprKind::Unit,
                        span,
                    };
                    for _ in 0..32_000 {
                        expression = ResolvedExpr {
                            kind: ResolvedExprKind::Tuple(vec![expression]),
                            span,
                        };
                    }
                    let initializer = ResolvedExpr {
                        kind: ResolvedExprKind::Unit,
                        span,
                    };
                    let result = resolver.finish_registration(
                        effect,
                        span,
                        ResolvedExpressionOwner::new(initializer),
                        ResolvedExpressionOwner::new(expression),
                    );
                    let work = resolver.type_work.used();
                    match result {
                        Ok(expression) => {
                            drop(ResolvedExpressionOwner::new(expression));
                            Ok(work)
                        }
                        Err(error) => Err(error.reason),
                    }
                };
                let exact = run(usize::MAX).unwrap();
                for limit in [0, 24, 64_030, exact - 1] {
                    assert_eq!(run(limit), Err(ResolveReason::TypeResourceExhausted));
                }
                for _ in 0..2 {
                    assert_eq!(run(exact), Ok(exact));
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn capture_type_metadata_excludes_only_lexical_fact_demand_and_retries_exactly() {
        let source = SourceFile::new("capture-metadata", "x").unwrap();
        let span = source.span(ByteRange::new(0, 1).unwrap()).unwrap();
        let module = ModuleId::new(9_093);
        let lexical = NominalTypeId::lexical(module, 0);
        let missing = NominalTypeId::new(module, 0);
        let summary =
            ExportSummary::test_fixture(module, Vec::new(), Vec::new(), Vec::new(), Vec::new());
        let root = Type::Tuple(Box::new([Type::Nominal(lexical), Type::Int]));
        let run = |budget| {
            let mut resolver = Resolver::with_type_work(ModuleId::new(9_094), budget);
            let result = resolver.retain_capture_type_metadata(&root, &summary, span);
            assert!(resolver.imported.nominal(lexical).is_none());
            (result, resolver.type_work.used())
        };
        let (result, exact) = run(TypeWorkBudget::unbounded());
        result.unwrap();
        assert!(exact >= 3);
        for limit in [0, exact - 1] {
            assert_eq!(
                run(TypeWorkBudget::with_limit(limit)).0.unwrap_err().reason,
                ResolveReason::TypeResourceExhausted
            );
        }
        for _ in 0..2 {
            let (result, used) = run(TypeWorkBudget::with_limit(exact));
            result.unwrap();
            assert_eq!(used, exact);
        }
        let mut resolver = Resolver::new(ModuleId::new(9_094));
        assert_eq!(
            resolver
                .retain_type_nominals(&root, &summary, span)
                .unwrap_err()
                .reason,
            ResolveReason::InternalState,
            "ordinary exported types must still require nominal facts"
        );
        assert_eq!(
            resolver
                .retain_capture_type_metadata(&Type::Nominal(missing), &summary, span)
                .unwrap_err()
                .reason,
            ResolveReason::InternalState,
            "a missing ordinary capture nominal is still invalid"
        );
        let effect_type = Type::function_computation(
            Type::Unit,
            crate::types::ComputationType::new(
                Type::Int,
                crate::types::EffectRow::singleton(crate::types::EffectInstance::new(
                    crate::types::EffectId::new(module, 0),
                    Box::new([]),
                )),
            ),
        );
        assert_eq!(
            resolver
                .retain_capture_type_metadata(&effect_type, &summary, span)
                .unwrap_err()
                .reason,
            ResolveReason::InternalState,
            "signature-only effects still require authenticated metadata"
        );
    }

    #[test]
    fn opaque_newtype_value_scheme_retains_canonical_closure_without_constructor_access() {
        let source = SourceFile::new("opaque-newtype-scheme.ash", "Token")
            .expect("the source fixture should fit");
        let span = source
            .span(ByteRange::new(0, 5).expect("the Token span should be ordered"))
            .expect("the Token span should fit");
        let module = ModuleId::new(9_089);
        let owner = NominalTypeId::new(module, 0);
        let summary = || {
            let mut summary = ExportSummary::test_fixture_with_access(
                module,
                Vec::new(),
                vec![(
                    "Token",
                    owner,
                    ExportedTypeAccess::Opaque,
                    Origin::Source(span),
                )],
                Vec::new(),
                Vec::new(),
                vec![("Token", Origin::Source(span))],
                Vec::new(),
            );
            assert!(
                summary.configure_first_public_nominal_as_opaque_newtype_for_test(
                    Type::Int,
                    ResolvedTypeProvenance::new(vec![ResolvedTypeProvenanceNode::Fact(span)], 0),
                )
            );
            summary
                .authenticate(
                    &mut TypeWorkBudget::default(),
                    &mut InterfaceConstraintBudget::default(),
                )
                .expect("the opaque source summary should authenticate");
            summary
        };
        let scheme = Type::Function(Box::new(Type::Unit), Box::new(Type::Nominal(owner)));

        let mut measured = Resolver::new(ModuleId::new(9_090));
        measured
            .retain_type_nominals(&scheme, &summary(), span)
            .expect("a selected value scheme should retain the opaque newtype closure");
        let exact_work = measured.type_work.used();
        let retained = measured
            .imported
            .nominal(owner)
            .expect("the hidden closure should retain Token");
        assert_eq!(retained.access, ImportedTypeAccess::Hidden);
        assert!(retained.constructors.is_empty());
        assert_eq!(retained.representation, Some(Type::Int));
        assert!(
            measured
                .imported
                .constructor(ConstructorId::new(owner, 0))
                .is_none()
        );

        let mut short = Resolver::with_type_work(
            ModuleId::new(9_091),
            TypeWorkBudget::with_limit(exact_work - 1),
        );
        let error = short
            .retain_type_nominals(&scheme, &summary(), span)
            .expect_err("one missing closure-retention cell should fail atomically");
        assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
        assert!(short.imported.nominal(owner).is_none());

        for _ in 0..2 {
            let mut exact = Resolver::with_type_work(
                ModuleId::new(9_092),
                TypeWorkBudget::with_limit(exact_work),
            );
            exact
                .retain_type_nominals(&scheme, &summary(), span)
                .expect("a fresh exact retry should retain the same hidden canonical closure");
            assert_eq!(exact.type_work.used(), exact_work);
            assert!(exact.imported.nominal(owner).is_some_and(|fact| {
                fact.access == ImportedTypeAccess::Hidden
                    && fact.representation == Some(Type::Int)
                    && fact.representation_provenance.is_some()
                    && fact.constructors.is_empty()
            }));
        }
    }

    #[test]
    fn nullary_constructor_family_transaction_and_route_cache_are_exact_atomic_and_reusable() {
        const FIRST_CONSTRAINT_WORK: usize = 9;
        const FIRST_TYPE_WORK: usize = 11;
        const DUPLICATE_CONSTRAINT_WORK: usize = 16;

        let source = SourceFile::new("nullary-constructor-family.ash", "First Second")
            .expect("the constructor-family source should fit");
        let span = source
            .span(ByteRange::new(0, 5).expect("the constructor range should be ordered"))
            .expect("the constructor span should fit");
        let module = ModuleId::new(9_090);
        let owner = NominalTypeId::new(module, 0);
        let first = ConstructorId::new(owner, 0);
        let second = ConstructorId::new(owner, 1);
        let summary = ExportSummary::test_fixture(
            module,
            Vec::new(),
            vec![(
                "Pair",
                owner,
                ExportedTypeAccess::Transparent,
                Origin::Source(span),
            )],
            vec![
                ("First", first, None, Origin::Source(span)),
                ("Second", second, None, Origin::Source(span)),
            ],
            Vec::new(),
        );
        summary
            .authenticate(
                &mut TypeWorkBudget::default(),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the immutable two-constructor summary should authenticate");
        let exported = summary
            .constructor("First")
            .expect("the first constructor should be public");

        let assert_snapshot = |resolver: &Resolver| {
            let nominal = resolver
                .imported
                .nominal(owner)
                .expect("the complete owner should be retained");
            assert_eq!(nominal.access, ImportedTypeAccess::Transparent);
            assert_eq!(nominal.constructors.as_ref(), [first, second]);
            assert!(resolver.imported.constructor(first).is_some());
            assert!(resolver.imported.constructor(second).is_some());
        };

        let mut constraint_short = Resolver::with_budgets(
            ModuleId::new(9_091),
            TypeWorkBudget::with_limit(FIRST_TYPE_WORK),
            InterfaceConstraintBudget::with_limit(FIRST_CONSTRAINT_WORK - 1),
        );
        let error = constraint_short
            .retain_imported_constructor(exported, &summary, span)
            .expect_err("one missing family-discovery cell must reject before retention");
        assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
        assert_eq!(
            constraint_short.constraint_work.used(),
            FIRST_CONSTRAINT_WORK - 1
        );
        assert_eq!(constraint_short.type_work.used(), 0);
        assert!(constraint_short.imported.nominals().next().is_none());
        assert!(constraint_short.imported.constructor(first).is_none());
        assert!(constraint_short.imported.constructor(second).is_none());

        let mut type_short = Resolver::with_budgets(
            ModuleId::new(9_092),
            TypeWorkBudget::with_limit(FIRST_TYPE_WORK - 1),
            InterfaceConstraintBudget::with_limit(FIRST_CONSTRAINT_WORK),
        );
        let error = type_short
            .retain_imported_constructor(exported, &summary, span)
            .expect_err("one missing aggregate Type cell must reject before retention");
        assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(type_short.constraint_work.used(), FIRST_CONSTRAINT_WORK);
        assert_eq!(type_short.type_work.used(), 0);
        assert!(type_short.imported.nominals().next().is_none());
        assert!(type_short.imported.constructor(first).is_none());
        assert!(type_short.imported.constructor(second).is_none());

        let mut duplicate_short = Resolver::with_budgets(
            ModuleId::new(9_093),
            TypeWorkBudget::with_limit(FIRST_TYPE_WORK),
            InterfaceConstraintBudget::with_limit(
                FIRST_CONSTRAINT_WORK + DUPLICATE_CONSTRAINT_WORK - 1,
            ),
        );
        duplicate_short
            .retain_imported_constructor(exported, &summary, span)
            .expect("the exact first route should publish the complete family");
        assert_snapshot(&duplicate_short);
        let error = duplicate_short
            .retain_imported_constructor(exported, &summary, span)
            .expect_err("one missing duplicate-route cell must preserve the first route");
        assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
        assert_eq!(
            duplicate_short.constraint_work.used(),
            FIRST_CONSTRAINT_WORK + DUPLICATE_CONSTRAINT_WORK - 1,
        );
        assert_eq!(duplicate_short.type_work.used(), FIRST_TYPE_WORK);
        assert_snapshot(&duplicate_short);

        let mut exact = Resolver::with_budgets(
            ModuleId::new(9_094),
            TypeWorkBudget::with_limit(FIRST_TYPE_WORK),
            InterfaceConstraintBudget::with_limit(
                FIRST_CONSTRAINT_WORK + DUPLICATE_CONSTRAINT_WORK,
            ),
        );
        exact
            .retain_imported_constructor(exported, &summary, span)
            .expect("the exact first route should publish the complete family");
        exact
            .retain_imported_constructor(exported, &summary, span)
            .expect("the exact duplicate route should authenticate without retention");
        assert_eq!(exact.type_work.used(), FIRST_TYPE_WORK);
        assert_eq!(
            exact.constraint_work.used(),
            FIRST_CONSTRAINT_WORK + DUPLICATE_CONSTRAINT_WORK,
        );
        assert_snapshot(&exact);

        const FIRST_ROUTE_CONSTRAINT_WORK: usize = FIRST_CONSTRAINT_WORK + 2;
        const REPEATED_ROUTE_CONSTRAINT_WORK: usize = 1;

        let owner_fact = summary
            .nominal_fact(owner)
            .expect("the family owner metadata should exist");
        let mut route_short = Resolver::with_budgets(
            ModuleId::new(9_095),
            TypeWorkBudget::with_limit(FIRST_TYPE_WORK),
            InterfaceConstraintBudget::with_limit(FIRST_ROUTE_CONSTRAINT_WORK - 1),
        );
        let mut short_route_owners = HashSet::new();
        let error = route_short
            .retain_imported_constructor_family_once_per_route(
                owner_fact,
                &summary,
                span,
                &mut short_route_owners,
            )
            .expect_err("one missing family cell must leave the route cache and facts empty");
        assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
        assert_eq!(
            route_short.constraint_work.used(),
            FIRST_ROUTE_CONSTRAINT_WORK - 1,
        );
        assert_eq!(route_short.type_work.used(), 0);
        assert!(short_route_owners.is_empty());
        assert!(route_short.imported.nominals().next().is_none());
        assert!(route_short.imported.constructor(first).is_none());
        assert!(route_short.imported.constructor(second).is_none());

        let mut route_exact = Resolver::with_budgets(
            ModuleId::new(9_096),
            TypeWorkBudget::with_limit(FIRST_TYPE_WORK),
            InterfaceConstraintBudget::with_limit(
                FIRST_ROUTE_CONSTRAINT_WORK + REPEATED_ROUTE_CONSTRAINT_WORK,
            ),
        );
        let mut exact_route_owners = HashSet::new();
        route_exact
            .retain_imported_constructor_family_once_per_route(
                owner_fact,
                &summary,
                span,
                &mut exact_route_owners,
            )
            .expect("the exact first route should retain the complete family");
        assert_snapshot(&route_exact);
        route_exact
            .retain_imported_constructor_family_once_per_route(
                owner_fact,
                &summary,
                span,
                &mut exact_route_owners,
            )
            .expect("the exact repeated selector should consume only its route probe");
        assert_eq!(route_exact.type_work.used(), FIRST_TYPE_WORK);
        assert_eq!(
            route_exact.constraint_work.used(),
            FIRST_ROUTE_CONSTRAINT_WORK + REPEATED_ROUTE_CONSTRAINT_WORK,
        );
        assert_eq!(exact_route_owners, HashSet::from([owner]));
        assert_snapshot(&route_exact);

        let error = route_exact
            .retain_imported_constructor_family_once_per_route(
                owner_fact,
                &summary,
                span,
                &mut exact_route_owners,
            )
            .expect_err("one missing repeat probe must preserve the complete route snapshot");
        assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
        assert_eq!(exact_route_owners, HashSet::from([owner]));
        assert_snapshot(&route_exact);
    }

    #[test]
    fn shared_foreign_nominal_constructor_family_transaction_is_exact_atomic_and_reusable() {
        const FIRST_CONSTRAINT_WORK: usize = 19;
        const FIRST_TYPE_WORK: usize = 20;
        const DUPLICATE_CONSTRAINT_WORK: usize = 32;
        const DEFERRED_FOREIGN_CONFLICT_WORK: usize = 31;
        const LATE_SIBLING_CONFLICT_WORK: usize = 21;

        std::thread::Builder::new()
            .name("shared-foreign-constructor-family".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new(
                    "shared-foreign-constructor-family.ash",
                    "First Second Foreign forged",
                )
                .expect("the shared-foreign source should fit");
                let span = source
                    .span(ByteRange::new(0, 5).expect("the clean range should be ordered"))
                    .expect("the clean span should fit");
                let forged_span = source
                    .span(ByteRange::new(21, 27).expect("the forged range should be ordered"))
                    .expect("the forged span should fit");
                let module = ModuleId::new(9_110);
                let owner = NominalTypeId::new(module, 0);
                let foreign = NominalTypeId::new(module, 1);
                let first = ConstructorId::new(owner, 0);
                let second = ConstructorId::new(owner, 1);
                let foreign_constructor = ConstructorId::new(foreign, 0);
                let make_summary = |foreign_origin, second_origin| {
                    ExportSummary::test_fixture(
                        module,
                        Vec::new(),
                        vec![
                            (
                                "Pair",
                                owner,
                                ExportedTypeAccess::Transparent,
                                Origin::Source(span),
                            ),
                            (
                                "Foreign",
                                foreign,
                                ExportedTypeAccess::Transparent,
                                foreign_origin,
                            ),
                        ],
                        vec![
                            (
                                "First",
                                first,
                                Some(Type::Nominal(foreign)),
                                Origin::Source(span),
                            ),
                            (
                                "Second",
                                second,
                                Some(Type::Nominal(foreign)),
                                second_origin,
                            ),
                            (
                                "ForeignValue",
                                foreign_constructor,
                                None,
                                Origin::Source(span),
                            ),
                        ],
                        Vec::new(),
                    )
                };
                let clean = make_summary(Origin::Source(span), Origin::Source(span));
                let foreign_conflicting =
                    make_summary(Origin::Source(forged_span), Origin::Source(span));
                let late_sibling_conflicting =
                    make_summary(Origin::Source(forged_span), Origin::Source(forged_span));
                for candidate in [&clean, &foreign_conflicting, &late_sibling_conflicting] {
                    candidate
                        .authenticate(
                            &mut TypeWorkBudget::default(),
                            &mut InterfaceConstraintBudget::default(),
                        )
                        .expect("each independently coherent family route should authenticate");
                }
                let clean_first = clean
                    .constructor("First")
                    .expect("the clean first constructor should exist");

                let assert_empty_snapshot = |resolver: &Resolver| {
                    assert!(resolver.imported.nominals().next().is_none());
                    assert!(resolver.imported.constructor(first).is_none());
                    assert!(resolver.imported.constructor(second).is_none());
                    assert!(resolver.imported.constructor(foreign_constructor).is_none());
                };
                let assert_clean_snapshot = |resolver: &Resolver| {
                    assert_eq!(
                        resolver
                            .imported
                            .nominals()
                            .map(|nominal| nominal.id)
                            .collect::<Vec<_>>(),
                        [owner, foreign],
                    );
                    let retained_owner = resolver
                        .imported
                        .nominal(owner)
                        .expect("the complete owner should be retained");
                    assert_eq!(retained_owner.access, ImportedTypeAccess::Transparent);
                    assert_eq!(retained_owner.constructors.as_ref(), [first, second]);
                    let retained_foreign = resolver
                        .imported
                        .nominal(foreign)
                        .expect("the shared foreign closure should be retained once");
                    assert_eq!(retained_foreign.access, ImportedTypeAccess::Hidden);
                    assert!(retained_foreign.constructors.is_empty());
                    assert_eq!(retained_foreign.constructor_count, 1);
                    for (identity, spelling) in [(first, "First"), (second, "Second")] {
                        let constructor = resolver
                            .imported
                            .constructor(identity)
                            .expect("both physical owner constructors should be retained");
                        assert_eq!(constructor.spelling, spelling);
                        assert_eq!(constructor.payload.as_ref(), Some(&Type::Nominal(foreign)));
                        assert_eq!(
                            constructor.scheme.value_type(),
                            &Type::Function(
                                Box::new(Type::Nominal(foreign)),
                                Box::new(Type::Nominal(owner)),
                            ),
                        );
                        assert_eq!(constructor.origin, Origin::Source(span));
                    }
                    assert!(resolver.imported.constructor(foreign_constructor).is_none());
                };

                // Shape and family planning cost five cells. The first sibling's
                // three-node scheme and one-node payload cost eight cells,
                // including two cells for each newly observed owner and foreign
                // identity. The second sibling costs four traversal cells because
                // the family-wide observer has already seen both identities. The
                // deferred foreign closure validation and staging record cost two.
                let mut constraint_short = Resolver::with_budgets(
                    ModuleId::new(9_111),
                    TypeWorkBudget::with_limit(FIRST_TYPE_WORK),
                    InterfaceConstraintBudget::with_limit(FIRST_CONSTRAINT_WORK - 1),
                );
                let error = constraint_short
                    .retain_imported_constructor(clean_first, &clean, span)
                    .expect_err("one missing foreign-closure cell must reject atomically");
                assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
                assert_eq!(
                    constraint_short.constraint_work.used(),
                    FIRST_CONSTRAINT_WORK - 1,
                );
                assert_eq!(constraint_short.type_work.used(), 0);
                assert_empty_snapshot(&constraint_short);

                let mut type_short = Resolver::with_budgets(
                    ModuleId::new(9_112),
                    TypeWorkBudget::with_limit(FIRST_TYPE_WORK - 1),
                    InterfaceConstraintBudget::with_limit(FIRST_CONSTRAINT_WORK),
                );
                let error = type_short
                    .retain_imported_constructor(clean_first, &clean, span)
                    .expect_err("one missing aggregate Type cell must reject atomically");
                assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
                assert_eq!(type_short.constraint_work.used(), FIRST_CONSTRAINT_WORK);
                assert_eq!(type_short.type_work.used(), 0);
                assert_empty_snapshot(&type_short);

                let mut resolver = Resolver::with_budgets(
                    ModuleId::new(9_113),
                    TypeWorkBudget::with_limit(FIRST_TYPE_WORK),
                    InterfaceConstraintBudget::with_limit(FIRST_CONSTRAINT_WORK),
                );
                resolver
                    .retain_imported_constructor(clean_first, &clean, span)
                    .expect("the exact family budget should retain both siblings and one closure");
                assert_eq!(resolver.constraint_work.used(), FIRST_CONSTRAINT_WORK);
                assert_eq!(resolver.type_work.used(), FIRST_TYPE_WORK);
                assert_clean_snapshot(&resolver);

                // Both sibling facts must compare before the shared foreign
                // closure. One short stops on that closure's Origin comparison;
                // exact reaches the semantic disagreement. Neither path retains
                // Type cells or changes the published family.
                resolver.type_work = TypeWorkBudget::with_limit(0);
                resolver.constraint_work =
                    InterfaceConstraintBudget::with_limit(DEFERRED_FOREIGN_CONFLICT_WORK - 1);
                let error = resolver
                    .retain_imported_constructor(
                        foreign_conflicting
                            .constructor("First")
                            .expect("the foreign-conflicting route should retain First"),
                        &foreign_conflicting,
                        span,
                    )
                    .expect_err("one missing deferred Origin cell must preserve the clean family");
                assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
                assert_eq!(
                    resolver.constraint_work.used(),
                    DEFERRED_FOREIGN_CONFLICT_WORK - 1,
                );
                assert_eq!(resolver.type_work.used(), 0);
                assert_clean_snapshot(&resolver);

                resolver.type_work = TypeWorkBudget::with_limit(0);
                resolver.constraint_work =
                    InterfaceConstraintBudget::with_limit(DEFERRED_FOREIGN_CONFLICT_WORK);
                let error = resolver
                    .retain_imported_constructor(
                        foreign_conflicting
                            .constructor("First")
                            .expect("the foreign-conflicting route should retain First"),
                        &foreign_conflicting,
                        span,
                    )
                    .expect_err("the deferred foreign Origin disagreement must reject");
                assert_eq!(error.reason, ResolveReason::InternalState);
                assert_eq!(
                    resolver.constraint_work.used(),
                    DEFERRED_FOREIGN_CONFLICT_WORK,
                );
                assert_eq!(resolver.type_work.used(), 0);
                assert_clean_snapshot(&resolver);

                // A late second-sibling fact disagreement owns failure before the
                // same route's foreign-closure disagreement can run.
                resolver.type_work = TypeWorkBudget::with_limit(0);
                resolver.constraint_work =
                    InterfaceConstraintBudget::with_limit(LATE_SIBLING_CONFLICT_WORK - 1);
                let error = resolver
                    .retain_imported_constructor(
                        late_sibling_conflicting
                            .constructor("First")
                            .expect("the late-conflicting route should retain First"),
                        &late_sibling_conflicting,
                        span,
                    )
                    .expect_err("one missing late sibling Origin cell must preserve the family");
                assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
                assert_eq!(
                    resolver.constraint_work.used(),
                    LATE_SIBLING_CONFLICT_WORK - 1,
                );
                assert_eq!(resolver.type_work.used(), 0);
                assert_clean_snapshot(&resolver);

                resolver.type_work = TypeWorkBudget::with_limit(0);
                resolver.constraint_work =
                    InterfaceConstraintBudget::with_limit(LATE_SIBLING_CONFLICT_WORK);
                let error = resolver
                    .retain_imported_constructor(
                        late_sibling_conflicting
                            .constructor("First")
                            .expect("the late-conflicting route should retain First"),
                        &late_sibling_conflicting,
                        span,
                    )
                    .expect_err("the late sibling disagreement must own deterministic rejection");
                assert_eq!(error.reason, ResolveReason::InternalState);
                assert_eq!(resolver.constraint_work.used(), LATE_SIBLING_CONFLICT_WORK,);
                assert_eq!(resolver.type_work.used(), 0);
                assert_clean_snapshot(&resolver);

                // A clean duplicate route performs only Constraint comparisons.
                // The first sibling observes both identities once for the whole
                // family; the second sibling reuses that observer, and D compares
                // the foreign closure before the already retained owner metadata.
                resolver.type_work = TypeWorkBudget::with_limit(0);
                resolver.constraint_work =
                    InterfaceConstraintBudget::with_limit(DUPLICATE_CONSTRAINT_WORK - 1);
                let error = resolver
                    .retain_imported_constructor(clean_first, &clean, span)
                    .expect_err("one missing duplicate owner-metadata cell must preserve state");
                assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
                assert_eq!(
                    resolver.constraint_work.used(),
                    DUPLICATE_CONSTRAINT_WORK - 1,
                );
                assert_eq!(resolver.type_work.used(), 0);
                assert_clean_snapshot(&resolver);

                resolver.type_work = TypeWorkBudget::with_limit(0);
                resolver.constraint_work =
                    InterfaceConstraintBudget::with_limit(DUPLICATE_CONSTRAINT_WORK);
                resolver
                    .retain_imported_constructor(clean_first, &clean, span)
                    .expect("the clean duplicate route should remain reusable after every failure");
                assert_eq!(resolver.constraint_work.used(), DUPLICATE_CONSTRAINT_WORK);
                assert_eq!(resolver.type_work.used(), 0);
                assert_clean_snapshot(&resolver);
            })
            .expect("the shared-foreign family thread should start")
            .join()
            .expect("the shared-foreign family thread should finish");
    }

    #[test]
    fn constructor_family_transaction_rejects_a_late_sibling_conflict_before_owner_metadata() {
        const FIRST_CONSTRAINT_WORK: usize = 9;
        const LATE_CONFLICT_WORK: usize = 13;
        const CLEAN_RETRY_WORK: usize = 16;
        const TYPE_WORK: usize = 11;

        let source = SourceFile::new(
            "late-constructor-family-conflict.ash",
            "First Second forged",
        )
        .expect("the late-conflict source should fit");
        let span = source
            .span(ByteRange::new(0, 5).expect("the constructor range should be ordered"))
            .expect("the constructor span should fit");
        let forged_span = source
            .span(ByteRange::new(13, 19).expect("the forged range should be ordered"))
            .expect("the forged span should fit");
        let module = ModuleId::new(9_097);
        let owner = NominalTypeId::new(module, 0);
        let first = ConstructorId::new(owner, 0);
        let second = ConstructorId::new(owner, 1);
        let summary = |second_origin| {
            ExportSummary::test_fixture(
                module,
                Vec::new(),
                vec![(
                    "Pair",
                    owner,
                    ExportedTypeAccess::Transparent,
                    Origin::Source(span),
                )],
                vec![
                    ("First", first, None, Origin::Source(span)),
                    ("Second", second, None, second_origin),
                ],
                Vec::new(),
            )
        };
        let clean = summary(Origin::Source(span));
        let conflicting = summary(Origin::Source(forged_span));
        for candidate in [&clean, &conflicting] {
            candidate
                .authenticate(
                    &mut TypeWorkBudget::default(),
                    &mut InterfaceConstraintBudget::default(),
                )
                .expect("each complete family route should authenticate independently");
        }

        let assert_clean_snapshot = |resolver: &Resolver| {
            assert_eq!(
                resolver
                    .imported
                    .nominals()
                    .map(|nominal| nominal.id)
                    .collect::<Vec<_>>(),
                [owner],
            );
            let nominal = resolver
                .imported
                .nominal(owner)
                .expect("the clean owner should remain retained");
            assert_eq!(nominal.access, ImportedTypeAccess::Transparent);
            assert_eq!(nominal.constructors.as_ref(), [first, second]);
            for (identity, spelling) in [(first, "First"), (second, "Second")] {
                let constructor = resolver
                    .imported
                    .constructor(identity)
                    .expect("the clean constructor fact should remain retained");
                assert_eq!(constructor.spelling, spelling);
                assert!(constructor.payload.is_none());
                assert_eq!(constructor.scheme.value_type(), &Type::Nominal(owner));
                assert_eq!(constructor.origin, Origin::Source(span));
            }
        };

        let mut resolver = Resolver::with_budgets(
            ModuleId::new(9_098),
            TypeWorkBudget::with_limit(TYPE_WORK),
            InterfaceConstraintBudget::with_limit(
                FIRST_CONSTRAINT_WORK + LATE_CONFLICT_WORK + CLEAN_RETRY_WORK,
            ),
        );
        resolver
            .retain_imported_constructor(
                clean
                    .constructor("First")
                    .expect("the clean first constructor should exist"),
                &clean,
                span,
            )
            .expect("the first complete family should publish");
        assert_eq!(resolver.constraint_work.used(), FIRST_CONSTRAINT_WORK);
        assert_eq!(resolver.type_work.used(), TYPE_WORK);
        assert_clean_snapshot(&resolver);

        let error = resolver
            .retain_imported_constructor(
                conflicting
                    .constructor("First")
                    .expect("the conflicting first constructor should exist"),
                &conflicting,
                span,
            )
            .expect_err("the late second-constructor Origin conflict must reject");
        assert_eq!(error.reason, ResolveReason::InternalState);
        assert_eq!(
            resolver.constraint_work.used(),
            FIRST_CONSTRAINT_WORK + LATE_CONFLICT_WORK,
            "owner metadata must not run before every constructor fact agrees",
        );
        assert_eq!(resolver.type_work.used(), TYPE_WORK);
        assert_clean_snapshot(&resolver);

        resolver
            .retain_imported_constructor(
                clean
                    .constructor("First")
                    .expect("the reusable clean constructor should exist"),
                &clean,
                span,
            )
            .expect("the clean family should remain reusable after the failed route");
        assert_eq!(
            resolver.constraint_work.used(),
            FIRST_CONSTRAINT_WORK + LATE_CONFLICT_WORK + CLEAN_RETRY_WORK,
        );
        assert_eq!(resolver.type_work.used(), TYPE_WORK);
        assert_clean_snapshot(&resolver);
    }

    #[test]
    fn constructor_family_transaction_rejects_a_late_missing_sibling_atomically_and_reuses_inputs()
    {
        const MISSING_CONSTRAINT_WORK: usize = 8;
        const CLEAN_RETRY_WORK: usize = 9;
        const TYPE_WORK: usize = 11;

        let source = SourceFile::new("late-missing-constructor-family.ash", "First Second")
            .expect("the late-missing source should fit");
        let span = source
            .span(ByteRange::new(0, 5).expect("the constructor range should be ordered"))
            .expect("the constructor span should fit");
        let module = ModuleId::new(9_102);
        let owner = NominalTypeId::new(module, 0);
        let first = ConstructorId::new(owner, 0);
        let second = ConstructorId::new(owner, 1);
        let make_summary = || {
            ExportSummary::test_fixture(
                module,
                Vec::new(),
                vec![(
                    "Pair",
                    owner,
                    ExportedTypeAccess::Transparent,
                    Origin::Source(span),
                )],
                vec![
                    ("First", first, None, Origin::Source(span)),
                    ("Second", second, None, Origin::Source(span)),
                ],
                Vec::new(),
            )
        };
        let clean = make_summary();
        let mut malformed = make_summary();
        for candidate in [&clean, &malformed] {
            candidate
                .authenticate(
                    &mut TypeWorkBudget::default(),
                    &mut InterfaceConstraintBudget::default(),
                )
                .expect("each complete family summary should authenticate before mutation");
        }
        assert!(
            malformed.remove_last_public_constructor_fact_preserving_family_for_test(),
            "the mutator should remove the late physical fact",
        );
        assert!(malformed.constructor("First").is_some());
        assert!(malformed.constructor("Second").is_none());
        assert_eq!(
            malformed
                .nominal_fact(owner)
                .expect("the malformed summary should retain owner metadata")
                .constructors,
            [first, second],
            "the malformed owner must still claim the complete family",
        );
        assert_eq!(
            malformed.authenticate(
                &mut TypeWorkBudget::default(),
                &mut InterfaceConstraintBudget::default(),
            ),
            Err(ResolvedBuildFailure::InvalidState),
            "raw authentication must reject a missing physical family member",
        );

        let mut resolver = Resolver::with_budgets(
            ModuleId::new(9_103),
            TypeWorkBudget::with_limit(TYPE_WORK),
            InterfaceConstraintBudget::with_limit(MISSING_CONSTRAINT_WORK + CLEAN_RETRY_WORK),
        );
        let error = resolver
            .retain_imported_constructor(
                malformed
                    .constructor("First")
                    .expect("the first physical fact should remain selectable"),
                &malformed,
                span,
            )
            .expect_err("the private family helper must reject the missing late sibling");
        assert_eq!(error.reason, ResolveReason::InternalState);
        assert_eq!(resolver.constraint_work.used(), MISSING_CONSTRAINT_WORK);
        assert_eq!(resolver.type_work.used(), 0);
        assert!(resolver.imported.nominals().next().is_none());
        assert!(resolver.imported.constructor(first).is_none());
        assert!(resolver.imported.constructor(second).is_none());

        resolver
            .retain_imported_constructor(
                clean
                    .constructor("First")
                    .expect("the clean first constructor should exist"),
                &clean,
                span,
            )
            .expect("the unchanged clean family should remain reusable after rejection");
        assert_eq!(
            resolver.constraint_work.used(),
            MISSING_CONSTRAINT_WORK + CLEAN_RETRY_WORK,
        );
        assert_eq!(resolver.type_work.used(), TYPE_WORK);
        assert_eq!(
            resolver
                .imported
                .nominals()
                .map(|nominal| nominal.id)
                .collect::<Vec<_>>(),
            [owner],
        );
        let nominal = resolver
            .imported
            .nominal(owner)
            .expect("the retry should retain the complete owner");
        assert_eq!(nominal.access, ImportedTypeAccess::Transparent);
        assert_eq!(nominal.constructors.as_ref(), [first, second]);
        assert!(resolver.imported.constructor(first).is_some());
        assert!(resolver.imported.constructor(second).is_some());
    }

    #[test]
    fn named_and_targeted_constructor_routes_share_one_family_transaction_in_both_orders() {
        const ROUTE_CONSTRAINT_WORK: usize = 12;
        const TYPE_WORK: usize = 11;

        let source = SourceFile::new("named-targeted-constructor-family.ash", "First Second")
            .expect("the named-targeted source should fit");
        let span = source
            .span(ByteRange::new(0, 5).expect("the constructor range should be ordered"))
            .expect("the constructor span should fit");
        let module = ModuleId::new(9_099);
        let owner = NominalTypeId::new(module, 0);
        let first = ConstructorId::new(owner, 0);
        let second = ConstructorId::new(owner, 1);
        let summary = ExportSummary::test_fixture(
            module,
            Vec::new(),
            vec![(
                "Pair",
                owner,
                ExportedTypeAccess::Transparent,
                Origin::Source(span),
            )],
            vec![
                ("First", first, None, Origin::Source(span)),
                ("Second", second, None, Origin::Source(span)),
            ],
            Vec::new(),
        );
        summary
            .authenticate(
                &mut TypeWorkBudget::default(),
                &mut InterfaceConstraintBudget::default(),
            )
            .expect("the shared family summary should authenticate");
        let exported_nominal = summary
            .nominal("Pair")
            .expect("the public Pair nominal should exist");
        let exported_constructor = summary
            .constructor("First")
            .expect("the public First constructor should exist");

        for named_first in [true, false] {
            let mut resolver = Resolver::with_budgets(
                ModuleId::new(if named_first { 9_100 } else { 9_101 }),
                TypeWorkBudget::with_limit(TYPE_WORK),
                InterfaceConstraintBudget::with_limit(ROUTE_CONSTRAINT_WORK),
            );
            let mut retained_constructor_owners = HashSet::new();
            let retain_named =
                |resolver: &mut Resolver,
                 retained_constructor_owners: &mut HashSet<NominalTypeId>| {
                    resolver.retain_imported_nominal(
                        exported_nominal,
                        &summary,
                        Some("Pair"),
                        span,
                        retained_constructor_owners,
                    )
                };
            let retain_targeted =
                |resolver: &mut Resolver,
                 retained_constructor_owners: &mut HashSet<NominalTypeId>| {
                    resolver.retain_imported_constructor_once_per_route(
                        exported_constructor,
                        &summary,
                        span,
                        retained_constructor_owners,
                    )
                };
            if named_first {
                retain_named(&mut resolver, &mut retained_constructor_owners)
                    .expect("the named route should retain the complete family");
                retain_targeted(&mut resolver, &mut retained_constructor_owners)
                    .expect("the targeted route should reuse the named family transaction");
            } else {
                retain_targeted(&mut resolver, &mut retained_constructor_owners)
                    .expect("the targeted route should retain the complete family");
                retain_named(&mut resolver, &mut retained_constructor_owners)
                    .expect("the named route should reuse the targeted family transaction");
            }

            assert_eq!(resolver.constraint_work.used(), ROUTE_CONSTRAINT_WORK);
            assert_eq!(resolver.type_work.used(), TYPE_WORK);
            assert_eq!(retained_constructor_owners, HashSet::from([owner]));
            assert_eq!(
                resolver
                    .imported
                    .nominals()
                    .map(|nominal| nominal.id)
                    .collect::<Vec<_>>(),
                [owner],
            );
            let nominal = resolver
                .imported
                .nominal(owner)
                .expect("the shared route should retain Pair");
            assert_eq!(nominal.access, ImportedTypeAccess::Transparent);
            assert_eq!(nominal.constructors.as_ref(), [first, second]);
            assert!(resolver.imported.constructor(first).is_some());
            assert!(resolver.imported.constructor(second).is_some());
        }
    }

    #[test]
    fn deep_constructor_scheme_import_lifecycle_is_exact_reusable_and_stack_safe() {
        const DEPTH: usize = 32_768;
        // Fused constructor and nominal name/order authentication contributes
        // two constraint
        // cells. The nominal-carrier pre-scan, family ordinal, withheld-owner
        // relation, physical fact, and canonical-family closure add five more;
        // the two public reverse-index records add two. Type authentication performs one fused body-free Kind walk
        // over the physical scheme and its independently retained payload,
        // collecting its exact owner-variable closure in that same walk.
        const RAW_CONSTRAINT_WORK: usize = 9;
        const RAW_CONSTRAINT_PRE_CLOSE: usize = 6;
        const RAW_CONSTRAINT_PRE_REVERSE: usize = 7;
        const RAW_TYPE_WORK: usize = 5 * DEPTH + 11;
        // First-route constraint work validates the two-cell owner shape,
        // retains one constructor-family transaction action, then discovers
        // nominal identities in the 2D+3-node physical scheme and independently
        // retained 2D+1-node payload. The first owner identity retains two
        // observer cells.
        const RETAIN_CONSTRAINT_WORK: usize = 4 * DEPTH + 9;
        // First-route Type work retains the three-cell owner, one prepared
        // nominal action, one staged constructor record, the 2D+1-node payload,
        // the 2D+3-node scheme, and one constructor-map record.
        const RETAIN_TYPE_WORK: usize = 4 * DEPTH + 10;
        // A repeated route validates the two-cell owner shape, retains one
        // constructor-family transaction action, compares one metadata and
        // Source-Origin cell, the 4D+6 scheme pair and 4D+2 payload pair,
        // observes the owner once, then compares the owner Source Origin. It
        // retains no Type cells.
        const MIRROR_CONSTRAINT_WORK: usize = 8 * DEPTH + 16;

        const { assert!(RAW_TYPE_WORK <= TYPE_WORK_LIMIT) };

        std::thread::Builder::new()
            .name("deep-constructor-scheme-lifecycle".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("deep-constructor-lifecycle.ash", "make")
                    .expect("the lifecycle source should fit");
                let span = source
                    .span(ByteRange::new(0, 4).expect("the lifecycle range should be ordered"))
                    .expect("the lifecycle span should fit");
                let module = ModuleId::new(9_100);
                let nominal = NominalTypeId::new(module, 0);
                let constructor = ConstructorId::new(nominal, 0);
                let deep_payload = || {
                    let mut ty = Type::Unit;
                    for _ in 0..DEPTH {
                        ty = Type::Function(Box::new(Type::Int), Box::new(ty));
                    }
                    ty
                };
                let summary = ExportSummary::test_fixture(
                    module,
                    Vec::new(),
                    vec![(
                        "Deep",
                        nominal,
                        ExportedTypeAccess::Transparent,
                        Origin::Source(span),
                    )],
                    vec![(
                        "Make",
                        constructor,
                        Some(deep_payload()),
                        Origin::Source(span),
                    )],
                    Vec::new(),
                );
                let mut raw_constraint_short =
                    InterfaceConstraintBudget::with_limit(RAW_CONSTRAINT_WORK - 1);
                let mut raw_constraint_short_type = TypeWorkBudget::with_limit(RAW_TYPE_WORK);
                assert_eq!(
                    summary
                        .authenticate(&mut raw_constraint_short_type, &mut raw_constraint_short,),
                    Err(ResolvedBuildFailure::ConstraintResource)
                );
                assert_eq!(raw_constraint_short.used(), RAW_CONSTRAINT_PRE_REVERSE);
                assert_eq!(raw_constraint_short_type.used(), RAW_TYPE_WORK);

                let mut raw_type_short = TypeWorkBudget::with_limit(RAW_TYPE_WORK - 1);
                let mut raw_type_short_constraint =
                    InterfaceConstraintBudget::with_limit(RAW_CONSTRAINT_WORK);
                assert_eq!(
                    summary.authenticate(&mut raw_type_short, &mut raw_type_short_constraint),
                    Err(ResolvedBuildFailure::TypeResource)
                );
                assert_eq!(raw_type_short.used(), RAW_TYPE_WORK - 1);
                assert_eq!(raw_type_short_constraint.used(), RAW_CONSTRAINT_PRE_CLOSE,);

                for _ in 0..2 {
                    let mut raw_type = TypeWorkBudget::with_limit(RAW_TYPE_WORK);
                    let mut raw_constraint =
                        InterfaceConstraintBudget::with_limit(RAW_CONSTRAINT_WORK);
                    summary
                        .authenticate(&mut raw_type, &mut raw_constraint)
                        .expect("the exact admissible constructor summary should authenticate");
                    assert_eq!(raw_type.used(), RAW_TYPE_WORK);
                    assert_eq!(raw_constraint.used(), RAW_CONSTRAINT_WORK);
                }
                summary
                    .authenticate(
                        &mut TypeWorkBudget::default(),
                        &mut InterfaceConstraintBudget::default(),
                    )
                    .expect("the deep constructor summary must fit the unchanged default limit");
                let exported = summary
                    .constructor("Make")
                    .expect("the authenticated summary should retain Make's physical scheme");

                {
                    let mut unbounded = TypeWorkBudget::unbounded();
                    let payload = exported
                        .payload
                        .as_ref()
                        .map(|payload| {
                            Resolver::clone_imported_payload_with_budget(
                                payload,
                                span,
                                &mut unbounded,
                            )
                        })
                        .transpose()
                        .expect("the staged deep payload should clone");
                    let scheme = exported
                        .scheme
                        .clone_with_budget(&mut unbounded)
                        .expect("the staged deep scheme should clone");
                    let mut abandoned = ImportedConstructorFactBuffer(Vec::new());
                    abandoned
                        .try_reserve(1)
                        .expect("the abandoned-fact guard should reserve one record");
                    abandoned.push(ImportedConstructorFact {
                        id: exported.id,
                        spelling: exported.spelling.clone(),
                        payload: payload.map(IterativeTypeOwner::into_inner),
                        scheme,
                        origin: exported.origin.clone(),
                    });
                    drop(abandoned);
                }

                let mut constraint_short = Resolver::with_budgets(
                    ModuleId::new(9_101),
                    TypeWorkBudget::with_limit(RETAIN_TYPE_WORK),
                    InterfaceConstraintBudget::with_limit(RETAIN_CONSTRAINT_WORK - 1),
                );
                let error = constraint_short
                    .retain_imported_constructor(exported, &summary, span)
                    .expect_err("one missing discovery cell must reject before retention");
                assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
                assert_eq!(
                    constraint_short.constraint_work.used(),
                    RETAIN_CONSTRAINT_WORK - 2,
                    "the final two-cell first-identity observation is atomic",
                );
                assert_eq!(constraint_short.type_work.used(), 0);
                assert!(constraint_short.imported.nominals().next().is_none());
                assert!(constraint_short.imported.constructor(constructor).is_none());
                drop(constraint_short);

                let mut type_short = Resolver::with_budgets(
                    ModuleId::new(9_102),
                    TypeWorkBudget::with_limit(RETAIN_TYPE_WORK - 1),
                    InterfaceConstraintBudget::with_limit(RETAIN_CONSTRAINT_WORK),
                );
                let error = type_short
                    .retain_imported_constructor(exported, &summary, span)
                    .expect_err("one missing aggregate Type cell must reject atomically");
                assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
                assert_eq!(type_short.type_work.used(), 0);
                assert_eq!(type_short.constraint_work.used(), RETAIN_CONSTRAINT_WORK);
                assert!(type_short.imported.nominals().next().is_none());
                assert!(type_short.imported.constructor(constructor).is_none());
                drop(type_short);

                let assert_imported_shape = |resolver: &Resolver| {
                    let imported = resolver
                        .imported
                        .constructor(constructor)
                        .expect("one authenticated ImportedConstructorFact should survive");
                    assert!(imported.scheme.type_parameters.is_empty());
                    assert!(imported.scheme.requirements.is_empty());
                    let Type::Function(domain, result) = imported.scheme.value_type() else {
                        panic!("the physical constructor scheme should retain payload -> result")
                    };
                    let mut payload = domain.as_ref();
                    for _ in 0..DEPTH {
                        let Type::Function(argument, codomain) = payload else {
                            panic!("the retained constructor payload lost a Function cell")
                        };
                        assert!(matches!(argument.as_ref(), Type::Int));
                        payload = codomain;
                    }
                    assert!(matches!(payload, Type::Unit));
                    assert!(matches!(result.as_ref(), Type::Nominal(id) if *id == nominal));
                };

                for consumer in [9_103, 9_104] {
                    let mut exact = Resolver::with_budgets(
                        ModuleId::new(consumer),
                        TypeWorkBudget::with_limit(RETAIN_TYPE_WORK),
                        InterfaceConstraintBudget::with_limit(
                            RETAIN_CONSTRAINT_WORK + MIRROR_CONSTRAINT_WORK - 1,
                        ),
                    );
                    exact
                        .retain_imported_constructor(exported, &summary, span)
                        .expect("the exact physical constructor-scheme lifecycle should fit");
                    assert_eq!(exact.type_work.used(), RETAIN_TYPE_WORK);
                    assert_eq!(exact.constraint_work.used(), RETAIN_CONSTRAINT_WORK);
                    assert_imported_shape(&exact);

                    let error = exact
                        .retain_imported_constructor(exported, &summary, span)
                        .expect_err("the one-short alternate route must reject before mutation");
                    assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
                    assert_eq!(exact.type_work.used(), RETAIN_TYPE_WORK);
                    assert_eq!(
                        exact.constraint_work.used(),
                        RETAIN_CONSTRAINT_WORK + MIRROR_CONSTRAINT_WORK - 1,
                    );
                    assert_imported_shape(&exact);
                    drop(exact);
                }

                let mut mirror_exact = Resolver::with_budgets(
                    ModuleId::new(9_105),
                    TypeWorkBudget::with_limit(RETAIN_TYPE_WORK),
                    InterfaceConstraintBudget::with_limit(
                        RETAIN_CONSTRAINT_WORK + MIRROR_CONSTRAINT_WORK,
                    ),
                );
                mirror_exact
                    .retain_imported_constructor(exported, &summary, span)
                    .expect("the first exact route should publish one constructor fact");
                mirror_exact
                    .retain_imported_constructor(exported, &summary, span)
                    .expect("the exact alternate route comparison should fit");
                assert_eq!(mirror_exact.type_work.used(), RETAIN_TYPE_WORK);
                assert_eq!(
                    mirror_exact.constraint_work.used(),
                    RETAIN_CONSTRAINT_WORK + MIRROR_CONSTRAINT_WORK,
                );
                drop(mirror_exact);
                drop(summary);
            })
            .expect("the lifecycle worker should spawn")
            .join()
            .expect("accepted and rejected deep constructor facts must tear down iteratively");
    }

    #[test]
    fn recursive_resolution_buffers_do_not_expose_broad_mutation() {
        let source = include_str!("resolve.rs");
        let broad_mutation_trait = ["Deref", "Mut"].concat();
        assert!(
            !source.contains(&broad_mutation_trait),
            "resolver-owned recursive buffers must not implement broad mutation",
        );
        for owner in [
            "ResolvedTypeBuffer",
            "ResolvedExpressionBuffer",
            "ResolvedDeclarationBuffer",
            "ResolveTaskBuffer",
        ] {
            assert!(
                source.contains(&format!("struct {owner}")),
                "the source guard must remain attached to {owner}",
            );
        }
    }

    struct HiddenInterfaceBudgetFixture(PathBuf);

    impl HiddenInterfaceBudgetFixture {
        fn create() -> Self {
            loop {
                let id = IMPORT_BUDGET_FIXTURE_IDS.fetch_add(1, Ordering::Relaxed);
                let directory = std::env::temp_dir().join(format!(
                    "ash-hidden-interface-budget-{}-{id}",
                    std::process::id()
                ));
                match fs::create_dir(&directory) {
                    Ok(()) => {
                        fs::write(directory.join("entry.ash"), "import middle as Middle\n")
                            .expect("the hidden-interface entry should be writable");
                        fs::write(
                            directory.join("middle.ash"),
                            concat!(
                                "import base as Base\n",
                                "pub apply : Int -> Int where Base.Render<Int>\n",
                                "apply value = Base.render((value, true))\n",
                            ),
                        )
                        .expect("the hidden-interface intermediary should be writable");
                        fs::write(
                            directory.join("base.ash"),
                            "pub interface Render<A> {\nrender<B> : (A, B) -> Int\n}\n",
                        )
                        .expect("the hidden-interface owner should be writable");
                        return Self(directory);
                    }
                    Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                    Err(error) => {
                        panic!("the hidden-interface budget fixture should be creatable: {error}")
                    }
                }
            }
        }
    }

    impl Drop for HiddenInterfaceBudgetFixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    struct HiddenInterfaceImportOutcome {
        result: Result<(), ResolveError>,
        constraint_used: usize,
        type_used: usize,
        interface: InterfaceId,
        middle: ModuleId,
        import_span: crate::source::Span,
        retained: Option<(InterfaceId, ModuleId, crate::source::Span)>,
    }

    fn retain_hidden_interface_import_with_limits(
        constraint_limit: usize,
        type_limit: usize,
    ) -> HiddenInterfaceImportOutcome {
        let fixture = HiddenInterfaceBudgetFixture::create();
        let graph = load_module_graph(&fixture.0.join("entry.ash"), &ModuleRoots::empty())
            .expect("the hidden-interface import graph should load");
        let mut checked = Vec::new();
        let mut middle = None;
        for module in graph
            .modules()
            .iter()
            .filter(|module| module.id() != graph.entry())
        {
            let dependencies = module
                .dependencies()
                .iter()
                .map(|edge| {
                    let dependency = checked
                        .iter()
                        .find(|checked: &&crate::resolved::CheckedModule| {
                            checked.module() == edge.target()
                        })
                        .expect("dependencies should check before their importers");
                    DependencyExports::new(edge, dependency.exports()).unwrap()
                })
                .collect::<Vec<_>>();
            let checked_module = check_module(
                resolve_module(module, &dependencies)
                    .expect("the hidden-interface dependency should resolve"),
            )
            .expect("the hidden-interface dependency should check");
            if Path::new(module.source().display_path()).file_name() == Some("middle.ash".as_ref())
            {
                middle = Some(checked_module.module());
            }
            checked.push(checked_module);
        }
        let entry = graph
            .module(graph.entry())
            .expect("the hidden-interface entry should load");
        let middle = middle.expect("the intermediary should check");
        let summary = checked
            .iter()
            .find(|checked| checked.module() == middle)
            .expect("the checked intermediary should remain available")
            .exports();
        let interface = summary
            .hidden_interfaces()
            .next()
            .expect("the intermediary should retain one hidden interface");
        let import_span = entry.surface().imports[0].span;
        let mut resolver = Resolver::with_budgets(
            entry.id(),
            TypeWorkBudget::with_limit(type_limit),
            InterfaceConstraintBudget::with_limit(constraint_limit),
        );
        let result = resolver.retain_imported_interface_fact(
            interface,
            summary,
            ImportedInterfaceAccess::HiddenSummaryClosure,
            middle,
            import_span,
        );
        let retained = resolver
            .imported
            .interface_imports()
            .next()
            .map(|imported| {
                (
                    imported.fact.id,
                    imported.direct_dependency,
                    imported.available_at,
                )
            });
        HiddenInterfaceImportOutcome {
            result,
            constraint_used: resolver.constraint_work.used(),
            type_used: resolver.type_work.used(),
            interface: interface.id,
            middle,
            import_span,
            retained,
        }
    }

    struct ImportBudgetFixture(PathBuf);

    impl ImportBudgetFixture {
        fn create(entry: &str, dependency: &str) -> Self {
            loop {
                let id = IMPORT_BUDGET_FIXTURE_IDS.fetch_add(1, Ordering::Relaxed);
                let directory = std::env::temp_dir()
                    .join(format!("ash-import-budget-{}-{id}", std::process::id()));
                match fs::create_dir(&directory) {
                    Ok(()) => {
                        fs::write(directory.join("entry.ash"), entry)
                            .expect("the import budget entry should be writable");
                        fs::write(directory.join("dependency.ash"), dependency)
                            .expect("the import budget dependency should be writable");
                        return Self(directory);
                    }
                    Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                    Err(error) => panic!("the import budget fixture should be creatable: {error}"),
                }
            }
        }
    }

    impl Drop for ImportBudgetFixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn resolve_import_fixture_with_limit(
        entry: &str,
        limit: usize,
    ) -> (Result<ResolvedModule, ResolveError>, usize) {
        resolve_import_fixture_with_dependency_and_limit(
            entry,
            concat!(
                "pub interface Equal<A> {\nequal : A -> A\n}\n",
                "pub impl Equal<Int> {\nequal value = value\n}\n",
            ),
            limit,
        )
    }

    fn resolve_import_fixture_with_dependency_and_limit(
        entry: &str,
        dependency: &str,
        limit: usize,
    ) -> (Result<ResolvedModule, ResolveError>, usize) {
        let fixture = ImportBudgetFixture::create(entry, dependency);
        let graph = load_module_graph(&fixture.0.join("entry.ash"), &ModuleRoots::empty())
            .expect("the import budget graph should load");
        let dependency = graph
            .modules()
            .iter()
            .find(|module| {
                Path::new(module.source().display_path()).file_name()
                    == Some("dependency.ash".as_ref())
            })
            .expect("the import budget dependency should load");
        let dependency =
            check_module(resolve_module(dependency, &[]).expect("the dependency should resolve"))
                .expect("the dependency should check");
        let entry = graph
            .module(graph.entry())
            .expect("the import budget entry should load");
        let dependencies = entry
            .dependencies()
            .iter()
            .map(|edge| DependencyExports::new(edge, dependency.exports()).unwrap())
            .collect::<Vec<_>>();
        let mut type_work = TypeWorkBudget::default();
        let mut constraint_work = InterfaceConstraintBudget::with_limit(limit);
        let result = resolve_module_names_with_budget(
            entry,
            &dependencies,
            &mut type_work,
            &mut constraint_work,
        )
        .map(|admission| ResolvedModule::new(admission.parts));
        (result, constraint_work.used())
    }

    fn resolve_import_fixture_with_type_limit(
        entry: &str,
        dependency: &str,
        limit: usize,
    ) -> (Result<ResolvedModule, ResolveError>, usize) {
        let fixture = ImportBudgetFixture::create(entry, dependency);
        let graph = load_module_graph(&fixture.0.join("entry.ash"), &ModuleRoots::empty())
            .expect("the import budget graph should load");
        let dependency = graph
            .modules()
            .iter()
            .find(|module| {
                Path::new(module.source().display_path()).file_name()
                    == Some("dependency.ash".as_ref())
            })
            .expect("the import budget dependency should load");
        let dependency =
            check_module(resolve_module(dependency, &[]).expect("the dependency should resolve"))
                .expect("the dependency should check");
        let entry = graph
            .module(graph.entry())
            .expect("the import budget entry should load");
        let dependencies = entry
            .dependencies()
            .iter()
            .map(|edge| DependencyExports::new(edge, dependency.exports()).unwrap())
            .collect::<Vec<_>>();
        let mut type_work = TypeWorkBudget::with_limit(limit);
        let mut constraint_work = InterfaceConstraintBudget::default();
        let result = resolve_module_names_with_budget(
            entry,
            &dependencies,
            &mut type_work,
            &mut constraint_work,
        )
        .map(|admission| ResolvedModule::new(admission.parts));
        (result, type_work.used())
    }

    fn resolve_local_fixture_with_constraint_limit(
        text: &str,
        limit: usize,
    ) -> (Result<(), ResolveError>, usize) {
        let source = SourceFile::new("local-constraint-budget.ash", text)
            .expect("the local constraint fixture should fit");
        let tree = parse(lex(&source).expect("the local constraint fixture should lex"));
        let module =
            project_module(&source, &tree).expect("the local constraint fixture should project");
        let mut resolver = Resolver::with_budgets(
            ModuleId::new(0),
            TypeWorkBudget::default(),
            InterfaceConstraintBudget::with_limit(limit),
        );
        let result = resolver
            .validate_local_namespaces(&module)
            .and_then(|()| resolver.resolve_declarations(&module))
            .map(|_| ());
        (result, resolver.constraint_work.used())
    }

    #[test]
    fn occurrence_evidence_slots_charge_the_exact_requirement_product() {
        const PREFIX: &str = concat!(
            "interface First<A> {\nfirst : A -> A\n}\n\n",
            "interface Second<A> {\nsecond : A -> A\n}\n\n",
            "interface Third<A> {\nthird : A -> A\n}\n\n",
            "interface Fourth<A> {\nfourth : A -> A\n}\n\n",
            "fan : Int -> Int where First<Int>, Second<Int>, Third<Int>, Fourth<Int>\n",
            "fan value = value\n\n",
            "main : Unit -> Int\n",
        );
        let one_occurrence = format!("{PREFIX}main () = fan 1\n");
        let four_occurrences = format!("{PREFIX}main () = fan (fan (fan (fan 1)))\n");

        let (one, one_used) = resolve_local_fixture_with_constraint_limit(&one_occurrence, 1_000);
        one.expect("one constrained occurrence should fit");
        let (four, four_used) =
            resolve_local_fixture_with_constraint_limit(&four_occurrences, 1_000);
        four.expect("four constrained occurrences should fit");

        assert_eq!(four_used - one_used, 3 * 4);

        let (exact, exact_used) =
            resolve_local_fixture_with_constraint_limit(&four_occurrences, four_used);
        exact.expect("the exact evidence-slot product budget should fit");
        assert_eq!(exact_used, four_used);

        let (short, short_used) =
            resolve_local_fixture_with_constraint_limit(&four_occurrences, four_used - 1);
        let error =
            short.expect_err("an incomplete final evidence-slot vector should reject resolution");
        assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
        assert_eq!(short_used, four_used - 4);
    }

    #[test]
    fn duplicate_global_route_compares_nominal_closure_without_recloning_it() {
        const ENTRY: &str = "import dependency (lift)\n";
        const DEPENDENCY: &str = concat!(
            "pub type Token = Token\n",
            "pub lift<F : Type -> Type> : F<Token> -> F<Token>\n",
            "lift value = value\n",
        );
        // Fact comparison is metadata P+R+1 = 2, Source-Origin = 1, the
        // parameter record plus its Arrow Kind = 4, and the seven-node value
        // Type pair = 14. The fused read-only closure adds 2U=2 simultaneous
        // unique-ID indexes and Token header+Origin D=2.
        const DUPLICATE_CONSTRAINT_WORK: usize = 2 + 1 + 4 + 14 + 2 + 2;

        let fixture = ImportBudgetFixture::create(ENTRY, DEPENDENCY);
        let graph = load_module_graph(&fixture.0.join("entry.ash"), &ModuleRoots::empty())
            .expect("the duplicate-global graph should load");
        let dependency = graph
            .modules()
            .iter()
            .find(|module| {
                Path::new(module.source().display_path()).file_name()
                    == Some("dependency.ash".as_ref())
            })
            .expect("the duplicate-global dependency should load");
        let dependency =
            check_module(resolve_module(dependency, &[]).expect("the dependency should resolve"))
                .expect("the higher-kinded dependency should check");
        let entry = graph
            .module(graph.entry())
            .expect("the duplicate-global entry should load");
        let summary = dependency.exports();
        let exported = summary
            .term("lift")
            .expect("the dependency should export the higher-kinded global");
        let token = summary
            .nominal("Token")
            .expect("the dependency should export the nominal used by the scheme")
            .id;
        let span = entry.surface().imports[0].span;

        let mut capture_work = TypeWorkBudget::unbounded();
        assert!(
            exported
                .capture
                .same_with_budget(&exported.capture, &mut capture_work)
                .unwrap()
        );
        let capture_work = capture_work.used();
        assert!(capture_work > 0);

        let snapshot = |resolver: &Resolver| {
            let globals = resolver
                .imported
                .globals()
                .map(|global| global.binder)
                .collect::<Vec<_>>();
            let nominals = resolver
                .imported
                .nominals()
                .map(|nominal| (nominal.id, nominal.access, nominal.constructors.to_vec()))
                .collect::<Vec<_>>();
            (globals, nominals, resolver.global_requirement_counts.len())
        };

        let mut resolver = Resolver::new(entry.id());
        resolver
            .retain_imported_global(exported, summary, span, &mut CaptureGraphVisits::default())
            .expect("the first route should retain the canonical global and its closure");
        let baseline = snapshot(&resolver);
        assert_eq!(
            baseline.1,
            vec![(token, ImportedTypeAccess::Hidden, Vec::new())],
        );

        resolver.type_work = TypeWorkBudget::with_limit(capture_work - 1);
        resolver.constraint_work = InterfaceConstraintBudget::with_limit(DUPLICATE_CONSTRAINT_WORK);
        let error = resolver
            .retain_imported_global(exported, summary, span, &mut CaptureGraphVisits::default())
            .expect_err("one missing data-summary comparison unit should reject the route");
        assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(snapshot(&resolver), baseline);

        resolver.type_work = TypeWorkBudget::with_limit(capture_work);
        resolver.constraint_work =
            InterfaceConstraintBudget::with_limit(DUPLICATE_CONSTRAINT_WORK - 1);
        let error = resolver
            .retain_imported_global(exported, summary, span, &mut CaptureGraphVisits::default())
            .expect_err("one missing comparison unit should reject the alternate route");
        assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
        assert_eq!(
            resolver.constraint_work.used(),
            DUPLICATE_CONSTRAINT_WORK - 1,
        );
        assert_eq!(resolver.type_work.used(), capture_work);
        assert_eq!(snapshot(&resolver), baseline);

        resolver.type_work = TypeWorkBudget::with_limit(capture_work);
        resolver.constraint_work = InterfaceConstraintBudget::with_limit(DUPLICATE_CONSTRAINT_WORK);
        resolver
            .retain_imported_global(exported, summary, span, &mut CaptureGraphVisits::default())
            .expect("the exact duplicate comparison should retain no second closure");
        assert_eq!(resolver.constraint_work.used(), DUPLICATE_CONSTRAINT_WORK,);
        assert_eq!(resolver.type_work.used(), capture_work);
        assert_eq!(snapshot(&resolver), baseline);
    }

    #[test]
    fn duplicate_implementation_routes_stage_precedence_without_recloning_the_fact() {
        const ENTRY: &str = "pub import dependency (impl Equal)\n";
        const DEPENDENCY: &str = concat!(
            "pub type Token = Token\n\n",
            "pub interface Equal<A> {\nequal : A -> A\n}\n\n",
            "pub impl Equal<Token> {\nequal value = value\n}\n",
        );
        // Route probe 1 + local authorization validation M=1 + fact equality:
        // metadata 2, head Type 2, unique nominal indexes 2, fact Origin 1,
        // the method's Related-Origin cells 7, and method value Type 6. The
        // canonical Token definition is header+Source-Origin 2. Two one-hop
        // prepends and the effective/public hop comparisons complete the route.
        const PUBLIC_DUPLICATE_CONSTRAINT_WORK: usize =
            1 + 1 + (2 + 2 + 2 + 1 + 7 + 6) + 2 + 1 + 1 + 1 + 1;
        // A private-to-public promotion replaces the public hop comparison with
        // one public-order/rank reservation cell, so its exact total is equal.
        const PUBLIC_PROMOTION_CONSTRAINT_WORK: usize =
            1 + 1 + (2 + 2 + 2 + 1 + 7 + 6) + 2 + 1 + 1 + 1 + 1;

        let fixture = ImportBudgetFixture::create(ENTRY, DEPENDENCY);
        let graph = load_module_graph(&fixture.0.join("entry.ash"), &ModuleRoots::empty())
            .expect("the duplicate-implementation graph should load");
        let dependency = graph
            .modules()
            .iter()
            .find(|module| {
                Path::new(module.source().display_path()).file_name()
                    == Some("dependency.ash".as_ref())
            })
            .expect("the duplicate-implementation dependency should load");
        let dependency =
            check_module(resolve_module(dependency, &[]).expect("the dependency should resolve"))
                .expect("the nominal-head implementation should check");
        let entry = graph
            .module(graph.entry())
            .expect("the duplicate-implementation entry should load");
        let summary = dependency.exports();
        let exported = summary
            .implementations()
            .next()
            .expect("the dependency should export one implementation");
        let implementation = exported.fact().id;
        let mut capture_work = TypeWorkBudget::unbounded();
        for method in &exported.fact().methods {
            assert!(
                method
                    .capture
                    .same_with_budget(&method.capture, &mut capture_work)
                    .unwrap()
            );
        }
        let capture_work = capture_work.used();
        assert!(capture_work > 0);
        let token = summary
            .nominal("Token")
            .expect("the implementation head should retain its nominal")
            .id;
        let import = &entry.surface().imports[0];
        let SurfaceImportSelection::Targeted(items) = &import.selection else {
            panic!("the fixture should use a targeted implementation import");
        };
        let SurfaceImportItem::Implementation { span, .. } = &items[0] else {
            panic!("the fixture should select implementations");
        };
        let public_selection = ImplementationImportSelection {
            direct_dependency: dependency.module(),
            selector_span: *span,
            import_span: import.span,
            public: true,
            route_rank: ImplementationRouteRank::new(0, 0, 0),
        };
        let private_selection = ImplementationImportSelection {
            public: false,
            ..public_selection
        };
        let snapshot = |resolver: &Resolver| {
            let implementations = resolver
                .imported
                .implementations()
                .map(|implementation| {
                    (
                        implementation.fact.id,
                        implementation.authorization().hops().to_vec(),
                        implementation
                            .public_authorization()
                            .map(|authorization| authorization.hops().to_vec()),
                    )
                })
                .collect::<Vec<_>>();
            let nominals = resolver
                .imported
                .nominals()
                .map(|nominal| (nominal.id, nominal.access, nominal.constructors.to_vec()))
                .collect::<Vec<_>>();
            (
                implementations,
                nominals,
                resolver
                    .implementation_route_ranks
                    .get(&implementation)
                    .copied(),
                resolver
                    .public_implementation_route_ranks
                    .get(&implementation)
                    .copied(),
                resolver.imported.public_implementation_ids().to_vec(),
            )
        };

        let mut duplicate = Resolver::new(entry.id());
        duplicate
            .retain_imported_implementation_fact(
                exported,
                summary,
                public_selection,
                &mut CaptureGraphVisits::default(),
            )
            .expect("the first public route should retain the fact and nominal closure");
        let public_baseline = snapshot(&duplicate);
        assert_eq!(
            public_baseline.1,
            vec![(token, ImportedTypeAccess::Hidden, Vec::new())],
        );
        duplicate.type_work = TypeWorkBudget::with_limit(capture_work - 1);
        duplicate.constraint_work =
            InterfaceConstraintBudget::with_limit(PUBLIC_DUPLICATE_CONSTRAINT_WORK);
        let error = duplicate
            .retain_imported_implementation_fact(
                exported,
                summary,
                public_selection,
                &mut CaptureGraphVisits::default(),
            )
            .expect_err("one missing method-summary comparison unit should reject the route");
        assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(snapshot(&duplicate), public_baseline);

        duplicate.type_work = TypeWorkBudget::with_limit(capture_work);
        duplicate.constraint_work =
            InterfaceConstraintBudget::with_limit(PUBLIC_DUPLICATE_CONSTRAINT_WORK - 1);
        let error = duplicate
            .retain_imported_implementation_fact(
                exported,
                summary,
                public_selection,
                &mut CaptureGraphVisits::default(),
            )
            .expect_err("one missing public-hop comparison cell should reject the duplicate");
        assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
        assert_eq!(
            duplicate.constraint_work.used(),
            PUBLIC_DUPLICATE_CONSTRAINT_WORK - 1,
        );
        assert_eq!(duplicate.type_work.used(), capture_work);
        assert_eq!(snapshot(&duplicate), public_baseline);

        duplicate.type_work = TypeWorkBudget::with_limit(capture_work);
        duplicate.constraint_work =
            InterfaceConstraintBudget::with_limit(PUBLIC_DUPLICATE_CONSTRAINT_WORK);
        duplicate
            .retain_imported_implementation_fact(
                exported,
                summary,
                public_selection,
                &mut CaptureGraphVisits::default(),
            )
            .expect("the exact duplicate route should retain no second fact or closure");
        assert_eq!(
            duplicate.constraint_work.used(),
            PUBLIC_DUPLICATE_CONSTRAINT_WORK,
        );
        assert_eq!(duplicate.type_work.used(), capture_work);
        assert_eq!(snapshot(&duplicate), public_baseline);

        let mut promotion = Resolver::new(entry.id());
        promotion
            .retain_imported_implementation_fact(
                exported,
                summary,
                private_selection,
                &mut CaptureGraphVisits::default(),
            )
            .expect("the first private route should retain the fact and closure");
        let private_baseline = snapshot(&promotion);
        assert!(private_baseline.0[0].2.is_none());
        assert!(private_baseline.4.is_empty());
        promotion.type_work = TypeWorkBudget::with_limit(capture_work);
        promotion.constraint_work =
            InterfaceConstraintBudget::with_limit(PUBLIC_PROMOTION_CONSTRAINT_WORK - 1);
        let error = promotion
            .retain_imported_implementation_fact(
                exported,
                summary,
                public_selection,
                &mut CaptureGraphVisits::default(),
            )
            .expect_err("one missing effective-hop cell should reject public promotion");
        assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
        assert_eq!(
            promotion.constraint_work.used(),
            PUBLIC_PROMOTION_CONSTRAINT_WORK - 1,
        );
        assert_eq!(promotion.type_work.used(), capture_work);
        assert_eq!(snapshot(&promotion), private_baseline);

        promotion.type_work = TypeWorkBudget::with_limit(capture_work);
        promotion.constraint_work =
            InterfaceConstraintBudget::with_limit(PUBLIC_PROMOTION_CONSTRAINT_WORK);
        promotion
            .retain_imported_implementation_fact(
                exported,
                summary,
                public_selection,
                &mut CaptureGraphVisits::default(),
            )
            .expect("the exact promotion should append one public route without recloning");
        assert_eq!(
            promotion.constraint_work.used(),
            PUBLIC_PROMOTION_CONSTRAINT_WORK,
        );
        assert_eq!(promotion.type_work.used(), capture_work);
        let promoted = snapshot(&promotion);
        assert_eq!(promoted.0.len(), 1);
        assert_eq!(promoted.1, private_baseline.1);
        assert_eq!(promoted.2, private_baseline.2);
        assert_eq!(promoted.3, Some(public_selection.route_rank));
        assert_eq!(promoted.4, vec![implementation]);
        assert!(promoted.0[0].2.is_some());
    }

    #[test]
    fn duplicate_interface_route_compares_nominal_closure_with_exact_constraint_work() {
        const ENTRY: &str = "import dependency as Facade\n";
        const FACADE: &str = "pub import base (Observe)\n";
        const BASE: &str = concat!(
            "type Secret<A> = Secret(A)\n\n",
            "pub interface Observe<A> {\nobserve : Secret<A> -> Secret<A>\n}\n",
        );
        // Route 1; fact metadata 2; parameter record, Source-Origin, and Type
        // Kind 3; interface Source-Origin 1; method Source-Origin 1; the
        // seven-node Type pair 14 plus its 2U nominal indexes; and Secret D=5
        // (header, one parameter
        // record/Origin/Kind, defining Origin).
        const EXACT_CONSTRAINT_WORK: usize = 1 + 2 + 3 + 1 + 1 + (14 + 2) + 5;

        let fixture = ImportBudgetFixture::create(ENTRY, FACADE);
        fs::write(fixture.0.join("base.ash"), BASE)
            .expect("the duplicate-interface base should be writable");
        let graph = load_module_graph(&fixture.0.join("entry.ash"), &ModuleRoots::empty())
            .expect("the duplicate-interface graph should load");
        let base = graph
            .modules()
            .iter()
            .find(|module| {
                Path::new(module.source().display_path()).file_name() == Some("base.ash".as_ref())
            })
            .expect("the duplicate-interface base should load");
        let base = check_module(resolve_module(base, &[]).expect("the base should resolve"))
            .expect("the nominal method interface should check");
        let facade = graph
            .modules()
            .iter()
            .find(|module| {
                Path::new(module.source().display_path()).file_name()
                    == Some("dependency.ash".as_ref())
            })
            .expect("the duplicate-interface facade should load");
        let facade_dependencies = facade
            .dependencies()
            .iter()
            .map(|edge| DependencyExports::new(edge, base.exports()).unwrap())
            .collect::<Vec<_>>();
        let facade = check_module(
            resolve_module(facade, &facade_dependencies).expect("the facade should resolve"),
        )
        .expect("the facade should check");
        let entry = graph
            .module(graph.entry())
            .expect("the duplicate-interface entry should load");
        let summary = facade.exports();
        let exported = summary
            .interfaces()
            .next()
            .expect("the facade should re-export Observe");
        let secret = summary
            .hidden_nominals()
            .next()
            .expect("the method should retain Secret as hidden closure")
            .id;
        let span = entry.surface().imports[0].span;
        let snapshot = |resolver: &Resolver| {
            let interface = resolver
                .imported
                .interface_imports()
                .next()
                .map(|interface| {
                    (
                        interface.fact.id,
                        interface.direct_dependency,
                        interface.available_at,
                        interface.publicly_available,
                    )
                });
            let nominals = resolver
                .imported
                .nominals()
                .map(|nominal| (nominal.id, nominal.access, nominal.constructors.to_vec()))
                .collect::<Vec<_>>();
            (interface, nominals)
        };

        let mut resolver = Resolver::new(entry.id());
        resolver
            .retain_imported_interface_fact(
                exported,
                summary,
                ImportedInterfaceAccess::HiddenSummaryClosure,
                facade.module(),
                span,
            )
            .expect("the first hidden route should retain the interface and closure");
        let hidden = snapshot(&resolver);
        assert_eq!(
            hidden.1,
            vec![(secret, ImportedTypeAccess::Hidden, Vec::new())],
        );
        assert!(!hidden.0.expect("the interface should be retained").3);

        resolver.type_work = TypeWorkBudget::with_limit(0);
        resolver.constraint_work = InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK - 1);
        let error = resolver
            .retain_imported_interface_fact(
                exported,
                summary,
                ImportedInterfaceAccess::PublicExport,
                facade.module(),
                span,
            )
            .expect_err("one missing definition cell should reject public promotion");
        assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
        assert_eq!(resolver.constraint_work.used(), EXACT_CONSTRAINT_WORK - 1);
        assert_eq!(resolver.type_work.used(), 0);
        assert_eq!(snapshot(&resolver), hidden);

        resolver.type_work = TypeWorkBudget::with_limit(0);
        resolver.constraint_work = InterfaceConstraintBudget::with_limit(EXACT_CONSTRAINT_WORK);
        resolver
            .retain_imported_interface_fact(
                exported,
                summary,
                ImportedInterfaceAccess::PublicExport,
                facade.module(),
                span,
            )
            .expect("the exact route should promote access without recloning the closure");
        assert_eq!(resolver.constraint_work.used(), EXACT_CONSTRAINT_WORK);
        assert_eq!(resolver.type_work.used(), 0);
        let public = snapshot(&resolver);
        assert_eq!(public.1, hidden.1);
        assert!(public.0.expect("the interface should remain retained").3);
    }

    #[test]
    fn duplicate_impl_route_charges_lookup_without_retaining_a_second_fact() {
        let one_source = "import dependency (impl Equal)\n";
        let two_source = "import dependency (impl Equal)\nimport dependency (impl Equal)\n";
        let (one_probe, one_used) = resolve_import_fixture_with_limit(one_source, 1_000);
        one_probe.expect("the route probe budget should fit");
        let (one_short, one_short_used) =
            resolve_import_fixture_with_limit(one_source, one_used - 1);
        let error = one_short.expect_err(
            "one unit short of the selector's cumulative work should reject resolution",
        );
        assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
        assert!(one_short_used < one_used);

        let (one, exact_one_used) = resolve_import_fixture_with_limit(one_source, one_used);
        one.expect("one explicit implementation route should resolve");
        assert_eq!(exact_one_used, one_used);
        let (two_probe, two_used) = resolve_import_fixture_with_limit(two_source, 1_000);
        two_probe.expect("the duplicate route probe budget should fit");
        let (two, exact_two_used) = resolve_import_fixture_with_limit(two_source, two_used);
        let two = two.expect("the duplicate implementation route should deduplicate");
        assert_eq!(exact_two_used, two_used);
        let implementation = two
            .imported_facts()
            .implementations()
            .next()
            .expect("one implementation fact should remain");
        assert!(
            two.imported_facts()
                .implementation(implementation.fact.id)
                .is_some()
        );
        assert_eq!(two.imported_facts().implementations().count(), 1);

        let (short, short_used) = resolve_import_fixture_with_limit(two_source, two_used - 1);
        let error = short.expect_err("one missing route unit should reject the duplicate edge");
        assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
        assert!(short_used < two_used);
    }

    #[test]
    fn duplicate_impl_route_comparisons_map_effective_and_public_budgets_independently() {
        const HOPS: usize = 3;
        const BOTH_EXACT: usize = HOPS * 2;
        let source = SourceFile::new("duplicate-route-comparison.ash", "abcdefghijkl")
            .expect("the duplicate route source should fit");
        let span = |start, end| {
            source
                .span(ByteRange::new(start, end).expect("the route range should be ordered"))
                .expect("the route range should fit")
        };
        let diagnostic_span = span(0, 11);
        let rank = ImplementationRouteRank::new(0, 0, 0);
        let route = |last_start, last_end| {
            ImplementationAuthorization::from_hops(vec![
                crate::resolved::ImplementationRouteHop {
                    from: ModuleId::new(1),
                    to: ModuleId::new(2),
                    import_span: span(0, 2),
                },
                crate::resolved::ImplementationRouteHop {
                    from: ModuleId::new(2),
                    to: ModuleId::new(3),
                    import_span: span(3, 5),
                },
                crate::resolved::ImplementationRouteHop {
                    from: ModuleId::new(3),
                    to: ModuleId::new(4),
                    import_span: span(last_start, last_end),
                },
            ])
        };
        let candidate = route(6, 8);
        let existing = route(9, 11);

        let mut effective_short = InterfaceConstraintBudget::with_limit(HOPS - 1);
        let error = effective_implementation_route_precedes(
            &candidate,
            rank,
            &existing,
            rank,
            diagnostic_span,
            &mut effective_short,
        )
        .expect_err("the effective comparison should reject one missing hop unit");
        assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
        assert_eq!(
            error.primary.message(),
            "effective implementation route comparison exceeded its work budget",
        );
        assert_eq!(effective_short.used(), HOPS - 1);

        let mut public_short = InterfaceConstraintBudget::with_limit(HOPS - 1);
        let error = public_implementation_route_precedes(
            &candidate,
            rank,
            &existing,
            rank,
            diagnostic_span,
            &mut public_short,
        )
        .expect_err("the public comparison should reject one missing hop unit");
        assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
        assert_eq!(
            error.primary.message(),
            "public implementation route comparison exceeded its work budget",
        );
        assert_eq!(public_short.used(), HOPS - 1);

        let mut both_short = InterfaceConstraintBudget::with_limit(BOTH_EXACT - 1);
        assert!(
            effective_implementation_route_precedes(
                &candidate,
                rank,
                &existing,
                rank,
                diagnostic_span,
                &mut both_short,
            )
            .expect("the exact effective comparison should fit"),
        );
        let error = public_implementation_route_precedes(
            &candidate,
            rank,
            &existing,
            rank,
            diagnostic_span,
            &mut both_short,
        )
        .expect_err("the independently charged public comparison should be one unit short");
        assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
        assert_eq!(both_short.used(), BOTH_EXACT - 1);

        let mut both_exact = InterfaceConstraintBudget::with_limit(BOTH_EXACT);
        assert!(
            effective_implementation_route_precedes(
                &candidate,
                rank,
                &existing,
                rank,
                diagnostic_span,
                &mut both_exact,
            )
            .expect("the exact effective comparison should fit"),
        );
        assert!(
            public_implementation_route_precedes(
                &candidate,
                rank,
                &existing,
                rank,
                diagnostic_span,
                &mut both_exact,
            )
            .expect("the exact public comparison should fit"),
        );
        assert_eq!(both_exact.used(), BOTH_EXACT);
        assert_eq!(both_exact.charge(1), Err(()));
    }

    #[test]
    fn public_import_candidate_staging_uses_exact_graph_type_work_before_freeze() {
        const DEPENDENCY: &str = "pub answer : Unit -> Int\nanswer () = 42\n";
        const PRIVATE: &str = "import dependency (answer as facade_answer)\n";
        const PUBLIC: &str = "pub import dependency (answer as facade_answer)\n";

        let (private, private_used) =
            resolve_import_fixture_with_type_limit(PRIVATE, DEPENDENCY, TYPE_WORK_LIMIT);
        private.expect("the private name import should establish the staging baseline");

        let exact_limit = private_used + 2;
        let (short, short_used) =
            resolve_import_fixture_with_type_limit(PUBLIC, DEPENDENCY, exact_limit - 1);
        let error = short.expect_err(
            "one missing candidate-order unit should reject resolution before summary freeze",
        );
        assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(error.primary.span().range().start(), 23);
        assert_eq!(short_used, private_used);

        let (exact, exact_used) =
            resolve_import_fixture_with_type_limit(PUBLIC, DEPENDENCY, exact_limit);
        let exact = exact.expect("the exact candidate map-and-order budget should resolve");
        assert_eq!(exact_used, exact_limit);
        assert!(exact.export_candidate().term("facade_answer").is_some());

        const OPAQUE_DEPENDENCY: &str = "pub opaque type Token = Token(Int)\n";
        const PRIVATE_OPAQUE: &str = "import dependency (Token)\n";
        const PUBLIC_OPAQUE: &str = "pub import dependency (Token)\n";
        let (private_opaque, private_opaque_used) = resolve_import_fixture_with_type_limit(
            PRIVATE_OPAQUE,
            OPAQUE_DEPENDENCY,
            TYPE_WORK_LIMIT,
        );
        private_opaque.expect("the private opaque import should establish its staging baseline");

        let opaque_exact_limit = private_opaque_used + 6;
        let (opaque_short, opaque_short_used) = resolve_import_fixture_with_type_limit(
            PUBLIC_OPAQUE,
            OPAQUE_DEPENDENCY,
            opaque_exact_limit - 1,
        );
        let error = opaque_short
            .expect_err("the opaque-family withheld entry should exhaust candidate staging");
        assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(error.primary.span().range().start(), 23);
        assert_eq!(opaque_short_used, private_opaque_used + 3);

        let (opaque_exact, opaque_exact_used) = resolve_import_fixture_with_type_limit(
            PUBLIC_OPAQUE,
            OPAQUE_DEPENDENCY,
            opaque_exact_limit,
        );
        let opaque_exact =
            opaque_exact.expect("the exact nominal-and-withheld candidate budget should resolve");
        assert_eq!(opaque_exact_used, opaque_exact_limit);
        assert!(opaque_exact.export_candidate().nominal("Token").is_some());
        assert!(
            opaque_exact
                .export_candidate()
                .is_opaque_constructor("Token")
        );
    }

    #[test]
    fn wide_public_import_candidate_staging_fails_structurally_during_resolution() {
        const ALIAS_COUNT: usize = 1_024;
        const DEPENDENCY: &str = "pub answer : Unit -> Int\nanswer () = 42\n";
        let targeted = |public: bool| {
            let mut source = if public {
                "pub import dependency (".to_owned()
            } else {
                "import dependency (".to_owned()
            };
            for index in 0..ALIAS_COUNT {
                if index > 0 {
                    source.push_str(", ");
                }
                source.push_str(&format!("answer as Alias{index}"));
            }
            source.push_str(")\n");
            source
        };
        let private = targeted(false);
        let public = targeted(true);
        let (private_result, private_used) =
            resolve_import_fixture_with_type_limit(&private, DEPENDENCY, TYPE_WORK_LIMIT);
        private_result.expect("the private wide import should establish the staging baseline");

        let exact_limit = private_used + ALIAS_COUNT * 2;
        let (short, _) =
            resolve_import_fixture_with_type_limit(&public, DEPENDENCY, exact_limit - 1);
        let error = short.expect_err("the final public alias should exhaust candidate staging");
        assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(
            usize::try_from(error.primary.span().range().start())
                .expect("the selector offset should fit"),
            public
                .rfind("answer")
                .expect("the last selector should exist"),
        );

        let (exact, exact_used) =
            resolve_import_fixture_with_type_limit(&public, DEPENDENCY, exact_limit);
        let exact = exact.expect("the exact wide public staging budget should resolve");
        assert_eq!(exact_used, exact_limit);
        assert!(
            exact
                .export_candidate()
                .term(&format!("Alias{}", ALIAS_COUNT - 1))
                .is_some()
        );
    }

    #[test]
    fn opaque_family_scan_charges_every_withheld_entry_for_each_public_alias() {
        const DEPENDENCY: &str = concat!(
            "hidden : Unit -> Unit\n",
            "hidden value = value\n\n",
            "pub opaque type Token =\n",
            "Seal(Int)\n",
            "| Stamp(Int)\n\n",
            "pub opaque type Other =\n",
            "Noise(Int)\n",
            "| Echo(Int)\n",
        );
        const PRIVATE: &str = "import dependency (Token as FirstToken, Token as SecondToken)\n";
        const PUBLIC: &str = "pub import dependency (Token as FirstToken, Token as SecondToken)\n";
        const WITHHELD_ENTRY_COUNT: usize = 5;
        const RETAINED_CANDIDATE_WORK: usize = 10;

        let (private, private_used) =
            resolve_import_fixture_with_type_limit(PRIVATE, DEPENDENCY, TYPE_WORK_LIMIT);
        private.expect("the private repeated aliases should establish the scan baseline");

        let exact_limit = private_used + RETAINED_CANDIDATE_WORK + 2 * WITHHELD_ENTRY_COUNT;
        let (short, short_used) =
            resolve_import_fixture_with_type_limit(PUBLIC, DEPENDENCY, exact_limit - 1);
        let error =
            short.expect_err("the second complete withheld-order scan should fail atomically");
        assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(
            error.primary.message(),
            "opaque constructor-family scan exceeded its type-work budget",
        );
        assert_eq!(
            usize::try_from(error.primary.span().range().start())
                .expect("the selector offset should fit"),
            PUBLIC
                .find("Token as SecondToken")
                .expect("the repeated selector should exist"),
        );
        assert_eq!(short_used, private_used + 2 + WITHHELD_ENTRY_COUNT + 6 + 2,);

        let (exact, exact_used) =
            resolve_import_fixture_with_type_limit(PUBLIC, DEPENDENCY, exact_limit);
        let exact = exact.expect("the exact repeated opaque-family scan budget should resolve");
        assert_eq!(exact_used, exact_limit);
        assert!(exact.export_candidate().nominal("FirstToken").is_some());
        assert!(exact.export_candidate().nominal("SecondToken").is_some());
        assert!(exact.export_candidate().is_opaque_constructor("Seal"));
        assert!(exact.export_candidate().is_opaque_constructor("Stamp"));
        assert!(!exact.export_candidate().is_opaque_constructor("Noise"));
        assert!(!exact.export_candidate().is_opaque_constructor("Echo"));
    }

    #[test]
    fn implementation_selector_index_probes_use_exact_constraint_budgets() {
        // Exhaustive dependency-summary admission precedes every selected-name
        // probe. The two fused name/namespace cells are followed by the nominal,
        // family-ordinal, withheld-owner, physical, closure, and two reverse
        // index cells for this one-nullary-constructor fixture.
        const SUMMARY_AUTHENTICATION_WORK: usize = 9;
        const NOMINAL_SELECTOR_WORK: usize = 4;
        const CONSTRUCTOR_SELECTOR_WORK: usize = 5;
        const MISSING_SELECTOR_WORK: usize = 8;

        let (nominal_short, nominal_short_used) = resolve_import_fixture_with_dependency_and_limit(
            "import dependency (impl Nominal)\n",
            "pub type Nominal = Nominal\n",
            SUMMARY_AUTHENTICATION_WORK + NOMINAL_SELECTOR_WORK - 1,
        );
        let error =
            nominal_short.expect_err("one missing nominal-index probe should reject the selector");
        assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
        assert_eq!(
            nominal_short_used,
            SUMMARY_AUTHENTICATION_WORK + NOMINAL_SELECTOR_WORK - 1,
        );

        let (nominal_exact, nominal_exact_used) = resolve_import_fixture_with_dependency_and_limit(
            "import dependency (impl Nominal)\n",
            "pub type Nominal = Nominal\n",
            SUMMARY_AUTHENTICATION_WORK + NOMINAL_SELECTOR_WORK,
        );
        let error = nominal_exact.expect_err("a public nominal is not an interface");
        assert_eq!(error.reason, ResolveReason::InterfaceKind);
        assert_eq!(
            nominal_exact_used,
            SUMMARY_AUTHENTICATION_WORK + NOMINAL_SELECTOR_WORK,
        );

        let (constructor_short, constructor_short_used) =
            resolve_import_fixture_with_dependency_and_limit(
                "import dependency (impl Constructor)\n",
                "pub type Nominal = Constructor\n",
                SUMMARY_AUTHENTICATION_WORK + CONSTRUCTOR_SELECTOR_WORK - 1,
            );
        let error = constructor_short
            .expect_err("one missing constructor-index probe should reject the selector");
        assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
        assert_eq!(
            constructor_short_used,
            SUMMARY_AUTHENTICATION_WORK + CONSTRUCTOR_SELECTOR_WORK - 1,
        );

        let (constructor_exact, constructor_exact_used) =
            resolve_import_fixture_with_dependency_and_limit(
                "import dependency (impl Constructor)\n",
                "pub type Nominal = Constructor\n",
                SUMMARY_AUTHENTICATION_WORK + CONSTRUCTOR_SELECTOR_WORK,
            );
        let error = constructor_exact.expect_err("a public constructor is not an interface");
        assert_eq!(error.reason, ResolveReason::InterfaceKind);
        assert_eq!(
            constructor_exact_used,
            SUMMARY_AUTHENTICATION_WORK + CONSTRUCTOR_SELECTOR_WORK,
        );

        let (missing_short, missing_short_used) = resolve_import_fixture_with_dependency_and_limit(
            "import dependency (impl Missing)\n",
            "pub type Nominal = Nominal\n",
            SUMMARY_AUTHENTICATION_WORK + MISSING_SELECTOR_WORK - 1,
        );
        let error =
            missing_short.expect_err("one missing withheld-index probe should reject the selector");
        assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
        assert_eq!(
            missing_short_used,
            SUMMARY_AUTHENTICATION_WORK + MISSING_SELECTOR_WORK - 1,
        );

        let (missing_exact, missing_exact_used) = resolve_import_fixture_with_dependency_and_limit(
            "import dependency (impl Missing)\n",
            "pub type Nominal = Nominal\n",
            SUMMARY_AUTHENTICATION_WORK + MISSING_SELECTOR_WORK,
        );
        let error = missing_exact.expect_err("an absent interface should remain unavailable");
        assert_eq!(error.reason, ResolveReason::UnavailableExport);
        assert_eq!(
            missing_exact_used,
            SUMMARY_AUTHENTICATION_WORK + MISSING_SELECTOR_WORK,
        );
    }

    #[test]
    fn wide_implementation_selector_expansion_has_an_exact_constraint_limit() {
        use std::fmt::Write as _;

        const WIDTH: usize = 16;
        const ENTRY: &str = "import dependency (impl Marker)\n";

        let mut dependency = String::from("pub interface Marker<A> {\nmark : A -> A\n}\n\n");
        for index in 0..WIDTH {
            writeln!(dependency, "pub type Head{index} = Head{index}")
                .expect("writing to a String cannot fail");
            writeln!(
                dependency,
                "pub impl Marker<Head{index}> {{\nmark value = value\n}}"
            )
            .expect("writing to a String cannot fail");
        }
        let fixture = ImportBudgetFixture::create(ENTRY, &dependency);
        let graph = load_module_graph(&fixture.0.join("entry.ash"), &ModuleRoots::empty())
            .expect("the wide-selector graph should load");
        let dependency = graph
            .modules()
            .iter()
            .find(|module| {
                Path::new(module.source().display_path()).file_name()
                    == Some("dependency.ash".as_ref())
            })
            .expect("the wide-selector dependency should load");
        let dependency =
            check_module(resolve_module(dependency, &[]).expect("the dependency should resolve"))
                .expect("distinct nominal heads should check without overlap");
        let entry = graph
            .module(graph.entry())
            .expect("the wide-selector entry should load");
        let import = entry
            .surface()
            .imports
            .first()
            .expect("the entry should retain its targeted import");
        let SurfaceImportSelection::Targeted(items) = &import.selection else {
            panic!("the fixture should contain a targeted import");
        };
        let SurfaceImportItem::Implementation { interface, span } = &items[0] else {
            panic!("the fixture should contain one implementation selector");
        };
        let selector_span = *span;
        let selection = ImplementationImportSelection {
            direct_dependency: dependency.module(),
            selector_span,
            import_span: import.span,
            public: false,
            route_rank: ImplementationRouteRank::new(0, 0, 0),
        };
        let select_with_limit = |limit| {
            let mut resolver = Resolver::with_budgets(
                entry.id(),
                TypeWorkBudget::default(),
                InterfaceConstraintBudget::with_limit(limit),
            );
            let result = resolver.select_imported_implementations(
                dependency.exports(),
                interface,
                selection,
                &mut CaptureGraphVisits::default(),
            );
            let heads = resolver
                .imported
                .implementations()
                .map(|implementation| match implementation.fact.arguments() {
                    [Type::Nominal(id)] => *id,
                    _ => panic!("each selected implementation should retain its nominal head"),
                })
                .collect::<Vec<_>>();
            (result, resolver.constraint_work.used(), heads)
        };

        let (measured, exact_limit, measured_heads) = select_with_limit(1_000_000);
        measured.expect("the generous selector budget should measure complete expansion");
        assert_eq!(measured_heads.len(), WIDTH);
        let mut distinct_heads = measured_heads.clone();
        distinct_heads.sort_unstable();
        distinct_heads.dedup();
        assert_eq!(distinct_heads.len(), WIDTH);

        let (short, short_used, short_heads) = select_with_limit(exact_limit - 1);
        let error = short.expect_err("one missing unit should reject selector expansion");
        assert_eq!(short_used, exact_limit - 1);
        assert_eq!(short_heads.len(), WIDTH - 1);
        assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
        assert_eq!(error.primary.span(), selector_span);
        assert_eq!(
            error.primary.message(),
            "imported nominal authentication exceeded its constraint-work budget",
        );

        let (exact, exact_used, exact_heads) = select_with_limit(exact_limit);
        exact.expect("the measured selector budget should retain every matching fact");
        assert_eq!(exact_used, exact_limit);
        assert_eq!(exact_heads, measured_heads);
    }

    #[test]
    fn hidden_interface_import_route_uses_its_exact_constraint_budget() {
        // ConstraintWork owns one route visit, three interface/method/binder
        // retained facts, two traversals of the five-cell method type, and the
        // method binder's record, Source-Origin, and Type-Kind authentication,
        // plus one private canonical method-authority row and its poly-only
        // checker-view ordinal index. The binder record moves from the removed
        // aggregate pre-scan into the canonical method pass; the new ordinal
        // index is one additional graph slot only for this polymorphic method.
        // TypeWork owns the same three retained carriers, two five-cell type
        // traversals, and two records plus Type Kinds for the interface and
        // method binders, plus one independent retained canonical method binder.
        const EXACT_CONSTRAINT_WORK: usize = 1 + 3 + 2 * 5 + 3 + 1 + 1;
        const EXACT_TYPE_WORK: usize = 3 + 2 * 5 + 2 * (1 + 1) + (1 + 1);

        let constraint_short =
            retain_hidden_interface_import_with_limits(EXACT_CONSTRAINT_WORK - 1, EXACT_TYPE_WORK);
        let error = constraint_short
            .result
            .expect_err("one missing unit should reject hidden interface retention");
        assert_eq!(error.reason, ResolveReason::ConstraintResourceExhausted);
        assert_eq!(constraint_short.constraint_used, EXACT_CONSTRAINT_WORK - 1,);
        assert_eq!(
            constraint_short.type_used,
            EXACT_TYPE_WORK - 2 * (1 + 1),
            "constraint failure precedes the final four method-binder TypeWork cells",
        );
        assert!(constraint_short.retained.is_none());

        let type_short =
            retain_hidden_interface_import_with_limits(EXACT_CONSTRAINT_WORK, EXACT_TYPE_WORK - 1);
        let error = type_short
            .result
            .expect_err("one missing type unit should reject hidden interface retention");
        assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(type_short.constraint_used, EXACT_CONSTRAINT_WORK);
        assert_eq!(type_short.type_used, EXACT_TYPE_WORK - 1);
        assert!(type_short.retained.is_none());

        let exact =
            retain_hidden_interface_import_with_limits(EXACT_CONSTRAINT_WORK, EXACT_TYPE_WORK);
        exact
            .result
            .expect("the exact route-and-shape budget should retain hidden interface metadata");
        assert_eq!(exact.constraint_used, EXACT_CONSTRAINT_WORK);
        assert_eq!(exact.type_used, EXACT_TYPE_WORK);
        let (retained_interface, direct_dependency, available_at) = exact
            .retained
            .expect("one hidden interface fact should cross the constrained summary");
        assert_eq!(retained_interface, exact.interface);
        assert_eq!(direct_dependency, exact.middle);
        assert_ne!(retained_interface.module(), direct_dependency);
        assert_eq!(available_at, exact.import_span);
    }

    #[test]
    fn resolver_resources_preserve_the_resource_and_resolution_stage() {
        use crate::{
            message::{Catalogue, Locale},
            presentation::{compile_resolve_diagnostic, write_human, write_json},
        };
        let source = SourceFile::new("resolve-resource.ash", "name").unwrap();
        let span = source.span(ByteRange::new(0, 4).unwrap()).unwrap();
        for (reason, resource, explanation) in [
            (
                ResolveReason::TypeResourceExhausted,
                "type-work",
                "The compiler ran out of resources while resolving types.",
            ),
            (
                ResolveReason::ConstraintResourceExhausted,
                "constraint-work",
                "The compiler ran out of resources while resolving interfaces and constraints.",
            ),
        ] {
            let error = error(reason, span, "ignored");
            let view = compile_resolve_diagnostic(&error, &[&source]).unwrap();
            for locale in [Locale::English, Locale::Bulgarian] {
                let mut output = Vec::new();
                write_human(&mut output, &view, &Catalogue::new(locale).unwrap()).unwrap();
                if locale == Locale::English {
                    assert!(String::from_utf8(output).unwrap().contains(explanation));
                }
            }
            let mut output = Vec::new();
            write_json(&mut output, &view).unwrap();
            let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
            assert_eq!(json["reason"], reason.to_string());
            assert_eq!(json["responsibility"], "compiler");
            assert_eq!(json["facts"][0]["value"], resource);
            assert_eq!(json["facts"][1]["value"], "resolution");
            assert_eq!(json["labels"][0]["relationship"], "resolution_site");
        }
    }

    #[test]
    fn identity_exhaustion_preserves_each_space_in_localized_messages_and_json() {
        use crate::message::{Catalogue, Locale};

        let source = SourceFile::new("exhaustion.ash", "name").unwrap();
        let span = source.span(ByteRange::new(0, 4).unwrap()).unwrap();
        let english = Catalogue::new(Locale::English).unwrap();
        let bulgarian = Catalogue::new(Locale::Bulgarian).unwrap();
        for (space, fact, en, bg) in [
            (
                ResolveIdentitySpace::TermBinder,
                "term-binder",
                "value bindings",
                "обвързвания на стойности",
            ),
            (
                ResolveIdentitySpace::TypeBinder,
                "type-binder",
                "type parameters",
                "типови параметри",
            ),
            (
                ResolveIdentitySpace::LocalNominal,
                "local-nominal",
                "local nominal types",
                "локални номинални типове",
            ),
            (
                ResolveIdentitySpace::Continuation,
                "continuation",
                "continuations",
                "продължения",
            ),
            (
                ResolveIdentitySpace::LexicalEvidence,
                "lexical-evidence",
                "lexical evidence and resource providers",
                "лексикални свидетелства и доставчици на ресурси",
            ),
        ] {
            let error = identity_error(space, span, "legacy wording must not drive presentation");
            assert!(!error.is_source_rejection());
            let message = error.message().unwrap();
            assert_eq!(
                english.format(&message).unwrap(),
                format!("Ash exhausted its identifier space for {en}.")
            );
            assert_eq!(
                bulgarian.format(&message).unwrap(),
                format!("Ash изчерпа пространството от идентификатори за {bg}.")
            );
            let view = crate::presentation::compile_resolve_diagnostic(&error, &[&source]).unwrap();
            let mut output = Vec::new();
            crate::presentation::write_json(&mut output, &view).unwrap();
            let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
            assert_eq!(json["responsibility"], "compiler");
            assert_eq!(json["facts"][0]["name"], "identity_space");
            assert_eq!(json["facts"][0]["kind"], "resolver-identity-space");
            assert_eq!(json["facts"][0]["value"], fact);
            assert_eq!(json["labels"][0]["relationship"], "identity_allocation");
        }
    }

    #[test]
    fn declaration_capacity_messages_keep_the_existing_internal_reason() {
        use crate::message::{Catalogue, Locale};
        let source = SourceFile::new("capacity.ash", "name").unwrap();
        let span = source.span(ByteRange::new(0, 4).unwrap()).unwrap();
        for (space, name, en, bg) in [
            (
                ResolveIdentitySpace::Interface,
                "interface",
                "interfaces in a module",
                "интерфейси в модул",
            ),
            (
                ResolveIdentitySpace::Method,
                "method",
                "methods in an interface",
                "методи в интерфейс",
            ),
            (
                ResolveIdentitySpace::Effect,
                "effect",
                "effects in a module",
                "ефекти в модул",
            ),
            (
                ResolveIdentitySpace::Operation,
                "operation",
                "operations in an effect",
                "операции в ефект",
            ),
            (
                ResolveIdentitySpace::Implementation,
                "implementation",
                "implementations in a module",
                "реализации в модул",
            ),
            (
                ResolveIdentitySpace::Requirement,
                "requirement",
                "interface requirements in a declaration",
                "изисквания за интерфейси в декларация",
            ),
            (
                ResolveIdentitySpace::Nominal,
                "nominal",
                "nominal types in a module",
                "номинални типове в модул",
            ),
            (
                ResolveIdentitySpace::Constructor,
                "constructor",
                "constructors in a declaration",
                "конструктори в декларация",
            ),
        ] {
            let error = error(ResolveReason::InternalState, span, "legacy description")
                .with_context(ResolveContext::IdentityExhaustion(space));
            let view = crate::presentation::compile_resolve_diagnostic(&error, &[&source]).unwrap();
            for (locale, subject) in [(Locale::English, en), (Locale::Bulgarian, bg)] {
                let mut output = Vec::new();
                crate::presentation::write_human(
                    &mut output,
                    &view,
                    &Catalogue::new(locale).unwrap(),
                )
                .unwrap();
                let output = String::from_utf8(output).unwrap();
                assert!(output.contains(subject));
                assert!(!output.contains("legacy description"));
            }
            let mut output = Vec::new();
            crate::presentation::write_json(&mut output, &view).unwrap();
            let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
            assert_eq!(json["reason"], "resolve.internal-state");
            assert_eq!(json["responsibility"], "compiler");
            assert_eq!(json["facts"][0]["name"], "identity_space");
            assert_eq!(json["facts"][0]["value"], name);
            assert_eq!(json["labels"][0]["relationship"], "identity_allocation");
            assert_eq!(json["labels"][0]["byte_end"], 4);
        }
    }

    #[test]
    fn internal_messages_do_not_depend_on_legacy_prose() {
        use crate::message::{Catalogue, Locale};
        let source = SourceFile::new("import.ash", "import dep as Dep").unwrap();
        let span = source.span(ByteRange::new(0, 17).unwrap()).unwrap();
        for (context, cause, explanation) in [
            (
                ResolveContext::DependencySummaryMismatch,
                "dependency-summary-mismatch",
                "The compiler received incomplete or mismatched checked information for this module's imports.",
            ),
            (
                ResolveContext::DependencySummaryInvalid,
                "dependency-summary-invalid",
                "The compiler could not validate the checked information for this imported module.",
            ),
            (
                ResolveContext::MissingFileScope,
                "missing-file-scope",
                "The compiler lost the file's name-resolution scope.",
            ),
            (
                ResolveContext::MissingLexicalScope,
                "missing-lexical-scope",
                "The compiler lost the current lexical scope while resolving a binding.",
            ),
            (
                ResolveContext::MissingNominalScope,
                "missing-nominal-scope",
                "The compiler lost the scope for local nominal types.",
            ),
            (
                ResolveContext::MissingConstructorScope,
                "missing-constructor-scope",
                "The compiler lost the scope for local constructors.",
            ),
        ] {
            let error = error(
                ResolveReason::InternalState,
                span,
                "legacy wording is not presentation input",
            )
            .with_context(context);
            let view = crate::presentation::compile_resolve_diagnostic(&error, &[&source]).unwrap();
            for locale in [Locale::English, Locale::Bulgarian] {
                let mut output = Vec::new();
                crate::presentation::write_human(
                    &mut output,
                    &view,
                    &Catalogue::new(locale).unwrap(),
                )
                .unwrap();
                let output = String::from_utf8(output).unwrap();
                assert!(!output.contains("legacy wording"));
                if locale == Locale::English {
                    assert!(output.contains(explanation));
                }
            }
            let mut output = Vec::new();
            crate::presentation::write_json(&mut output, &view).unwrap();
            let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
            assert_eq!(json["reason"], "resolve.internal-state");
            assert_eq!(json["responsibility"], "compiler");
            assert_eq!(json["facts"][0]["value"], cause);
            assert_eq!(json["labels"][0]["byte_end"], 17);
        }
    }

    #[test]
    fn work_state_messages_keep_each_existing_part_and_problem() {
        use crate::message::{Catalogue, Locale};
        let source = SourceFile::new("state.ash", "name").unwrap();
        let span = source.span(ByteRange::new(0, 4).unwrap()).unwrap();
        for (part, problem, en, bg) in [
            ("equation", "missing", "an equation", "уравнение"),
            (
                "operational-pattern",
                "missing",
                "an operational parameter pattern",
                "шаблон на операционен параметър",
            ),
            (
                "operational-pattern",
                "extra",
                "an operational parameter pattern",
                "шаблон на операционен параметър",
            ),
            (
                "operational-parameter",
                "missing",
                "an operational parameter",
                "операционен параметър",
            ),
            (
                "operational-body",
                "wrong",
                "an operational body",
                "операционно тяло",
            ),
            (
                "tuple-type-element",
                "missing",
                "a tuple type element",
                "елемент на кортежен тип",
            ),
            (
                "effect-row-argument",
                "missing",
                "an effect-row type argument",
                "типов аргумент на ред от ефекти",
            ),
            (
                "effect-row-argument",
                "extra",
                "an effect-row type argument",
                "типов аргумент на ред от ефекти",
            ),
            (
                "function-codomain",
                "missing",
                "a function result type",
                "тип на резултата на функция",
            ),
            (
                "function-domain",
                "missing",
                "a function argument type",
                "тип на аргумента на функция",
            ),
            (
                "type-argument",
                "missing",
                "a type argument",
                "типов аргумент",
            ),
            ("type", "incomplete", "a type", "тип"),
            ("type", "missing", "a type", "тип"),
            ("block", "wrong", "a block", "блок"),
            (
                "binding-pattern",
                "missing",
                "a binding pattern",
                "шаблон на обвързване",
            ),
            (
                "binding-initializer",
                "missing",
                "a binding initializer",
                "начален израз на обвързване",
            ),
            (
                "recursive-member",
                "missing",
                "a recursive group member",
                "член на рекурсивна група",
            ),
            (
                "block-result",
                "missing",
                "a block result",
                "резултат на блок",
            ),
            (
                "block-binding",
                "missing",
                "a block binding",
                "обвързване в блок",
            ),
            (
                "function-body",
                "missing",
                "a function body",
                "тяло на функция",
            ),
            (
                "function-body",
                "wrong",
                "a function body",
                "тяло на функция",
            ),
            (
                "tuple-element",
                "missing",
                "a tuple element",
                "елемент на кортеж",
            ),
            ("expression", "missing", "an expression", "израз"),
            ("expression", "incomplete", "an expression", "израз"),
            (
                "match-pattern",
                "missing",
                "a match pattern",
                "шаблон на съпоставяне",
            ),
            (
                "function-pattern",
                "missing",
                "a function parameter pattern",
                "шаблон на параметър на функция",
            ),
            (
                "handler-pattern",
                "missing",
                "a handler parameter pattern",
                "шаблон на параметър на обработчик",
            ),
            (
                "right-operand",
                "missing",
                "a right operand",
                "десен операнд",
            ),
            ("left-operand", "missing", "a left operand", "ляв операнд"),
        ] {
            let error = error(
                ResolveReason::InternalState,
                span,
                "legacy wording is not presentation input",
            )
            .with_context(ResolveContext::WorkState { part, problem });
            let view = crate::presentation::compile_resolve_diagnostic(&error, &[&source]).unwrap();
            for (locale, subject) in [(Locale::English, en), (Locale::Bulgarian, bg)] {
                let mut output = Vec::new();
                crate::presentation::write_human(
                    &mut output,
                    &view,
                    &Catalogue::new(locale).unwrap(),
                )
                .unwrap();
                let output = String::from_utf8(output).unwrap();
                assert!(output.contains(subject), "{part}: {output}");
                assert!(!output.contains("legacy wording"));
                if locale == Locale::English {
                    let expected = match problem {
                        "missing" => "is missing",
                        "extra" => "unexpectedly retains",
                        "wrong" => "has the wrong value for",
                        "incomplete" => "is incomplete for",
                        _ => unreachable!(),
                    };
                    assert!(output.contains(expected));
                }
            }
            let mut output = Vec::new();
            crate::presentation::write_json(&mut output, &view).unwrap();
            let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
            assert_eq!(json["reason"], "resolve.internal-state");
            assert_eq!(json["responsibility"], "compiler");
            assert_eq!(json["facts"][0]["value"], "work-state");
            assert_eq!(json["facts"][1]["value"], part);
            assert_eq!(json["facts"][2]["value"], problem);
            assert_eq!(json["labels"][0]["byte_end"], 4);
        }
    }

    #[test]
    fn declaration_order_messages_preserve_kind_and_problem() {
        use crate::message::{Catalogue, Locale};
        let source = SourceFile::new("order.ash", "type T = T").unwrap();
        let span = source.span(ByteRange::new(0, 10).unwrap()).unwrap();
        for (kind, en, bg) in [
            ("nominal", "nominal types", "номиналните типове"),
            ("interface", "interfaces", "интерфейсите"),
            ("effect", "effects", "ефектите"),
            ("global", "global values", "глобалните стойности"),
            ("implementation", "implementations", "реализациите"),
        ] {
            for (problem, explanation) in [
                ("invalid-index", "a declaration index is out of range"),
                (
                    "repeated-or-reordered",
                    "a declaration is repeated or out of order",
                ),
                (
                    "skipped-or-reordered",
                    "a declaration is skipped or out of order",
                ),
                ("omitted", "a declaration is missing"),
                (
                    "repeated-skipped-or-reordered",
                    "a declaration is repeated, skipped, or out of order",
                ),
            ] {
                let error = error(ResolveReason::InternalState, span, "unused legacy prose")
                    .with_context(ResolveContext::DeclarationOrder { kind, problem });
                let view =
                    crate::presentation::compile_resolve_diagnostic(&error, &[&source]).unwrap();
                for (locale, subject) in [(Locale::English, en), (Locale::Bulgarian, bg)] {
                    let mut output = Vec::new();
                    crate::presentation::write_human(
                        &mut output,
                        &view,
                        &Catalogue::new(locale).unwrap(),
                    )
                    .unwrap();
                    let output = String::from_utf8(output).unwrap();
                    assert!(output.contains(subject));
                    assert!(!output.contains("legacy prose"));
                    if locale == Locale::English {
                        assert!(output.contains(explanation));
                    }
                }
                let mut output = Vec::new();
                crate::presentation::write_json(&mut output, &view).unwrap();
                let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
                assert_eq!(json["reason"], "resolve.internal-state");
                assert_eq!(json["responsibility"], "compiler");
                assert_eq!(json["facts"][0]["value"], "declaration-order");
                assert_eq!(json["facts"][1]["value"], kind);
                assert_eq!(json["facts"][2]["value"], problem);
                assert_eq!(json["labels"][0]["byte_end"], 10);
            }
        }
    }

    #[test]
    fn binder_identity_allocation_reports_exhaustion_without_wrapping() {
        let source =
            SourceFile::new("exhaustion.ash", "name").expect("the allocator fixture should fit");
        let span = source
            .span(ByteRange::new(0, 4).expect("the range is ordered"))
            .expect("the range belongs to the fixture");
        let mut resolver = Resolver::new(ModuleId::new(0));
        resolver.next_binder = u32::MAX;

        let error = resolver
            .allocate_binder("name", span)
            .expect_err("the reserved exhaustion sentinel must not be exposed");

        assert_eq!(error.reason, ResolveReason::BinderIdExhausted);
        assert_eq!(resolver.next_binder, u32::MAX);
        let view = crate::presentation::compile_resolve_diagnostic(&error, &[&source]).unwrap();
        let mut output = Vec::new();
        crate::presentation::write_json(&mut output, &view).unwrap();
        let json: serde_json::Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(json["responsibility"], "compiler");
        assert_eq!(json["facts"][0]["name"], "identity_space");
        assert_eq!(json["facts"][0]["value"], "term-binder");
    }

    #[test]
    fn hidden_impl_binder_exhaustion_precedes_global_body_resolution() {
        let text = "interface Convert<A> {\nconvert : A -> A\n}\n\nbefore : Int -> Int\nbefore value = missing\n\nimpl Convert<Int> {\nconvert value = value\n}\n";
        let source = SourceFile::new("hidden-exhaustion.ash", text)
            .expect("the exhaustion fixture should fit");
        let tree = parse(lex(&source).expect("the fixture should lex"));
        let module = project_module(&source, &tree).expect("the fixture should project");
        let mut resolver = Resolver::new(ModuleId::new(0));
        resolver.next_binder = u32::MAX - 1;
        resolver
            .validate_local_namespaces(&module)
            .expect("the fixture namespaces should be distinct");

        let error = match resolver.resolve_declarations(&module) {
            Err(error) => error,
            Ok(_) => panic!("the hidden binder should exhaust before body resolution"),
        };

        assert_eq!(error.reason, ResolveReason::BinderIdExhausted);
        assert_eq!(resolver.next_binder, u32::MAX);
    }

    #[test]
    fn failed_nested_and_recursive_resolution_restore_the_scope_stack() {
        for (name, text) in [
            (
                "scope-error.ash",
                "main : Unit -> Unit\nmain () = fn(value) {\n{\nmissing\n}\n}\n",
            ),
            (
                "recursive-scope-error.ash",
                "main : Unit -> Int\nmain () = {\nlet rec repeat : Unit -> Int = fn(ignored) {\nmissing\n}\nrepeat ()\n}\n",
            ),
        ] {
            let source = SourceFile::new(name, text).expect("the scope fixture should fit");
            let tree = parse(lex(&source).expect("the fixture should lex"));
            let module = project_module(&source, &tree).expect("the fixture should project");
            let SurfaceDefinitionKind::Equational(main) = &module.definitions[0].kind else {
                panic!("the fixture should expose an equational main");
            };
            let body = &main.equations[0].body;
            let mut resolver = Resolver::new(ModuleId::new(0));
            let initial_scope_count = resolver.scopes.len();

            let error = resolver
                .resolve_expr(body)
                .expect_err("the nested unknown name should fail");

            assert_eq!(error.reason, ResolveReason::UnknownName);
            assert_eq!(resolver.scopes.len(), initial_scope_count);
        }
    }

    #[test]
    fn late_expression_resolution_errors_discard_deep_completed_work_on_a_small_stack() {
        const WIDTH: usize = 32_768;

        std::thread::Builder::new()
            .name("late-resolver-expression-disposal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("late-resolver.ash", "x")
                    .expect("the resolver fixture should fit");
                let span = source
                    .span(ByteRange::new(0, 1).expect("the range should be ordered"))
                    .expect("the range should belong to the fixture");
                let module = ModuleId::new(0);
                let owner = NominalTypeId::new(module, 0);
                let name = |text: &str| {
                    SurfaceReference::Unqualified(SurfaceName {
                        text: text.to_owned(),
                        span,
                    })
                };
                let wide = || SurfaceType {
                    kind: SurfaceTypeKind::Application {
                        constructor: name("Wide"),
                        arguments: vec![
                            SurfaceType {
                                kind: SurfaceTypeKind::Int,
                                span,
                            };
                            WIDTH
                        ],
                    },
                    span,
                };
                let deep_block = || SurfaceExpr {
                    kind: SurfaceExprKind::Block(SurfaceBlock {
                        declarations: vec![SurfaceLocalDeclaration::Binding(Box::new(
                            SurfaceBinding {
                                pattern: SurfacePattern {
                                    kind: SurfacePatternKind::Wildcard,
                                    span,
                                },
                                annotation: Some(wide()),
                                initializer: SurfaceExpr {
                                    kind: SurfaceExprKind::Unit,
                                    span,
                                },
                                span,
                            },
                        ))],
                        result: Box::new(SurfaceExpr {
                            kind: SurfaceExprKind::Unit,
                            span,
                        }),
                        span,
                    }),
                    span,
                };
                let missing = || SurfaceExpr {
                    kind: SurfaceExprKind::Name(name("missing")),
                    span,
                };
                let resolver = || {
                    let mut resolver = Resolver::new(module);
                    resolver.type_names.insert("Wide".to_owned(), owner);
                    resolver.nominal_parameter_counts.insert(owner, WIDTH);
                    resolver
                };

                let tuple = SurfaceExpr {
                    kind: SurfaceExprKind::Tuple(vec![deep_block(), missing()]),
                    span,
                };
                assert_eq!(
                    resolver()
                        .resolve_expr(&tuple)
                        .expect_err("the late tuple sibling should be unknown")
                        .reason,
                    ResolveReason::UnknownName,
                );

                let matched = SurfaceExpr {
                    kind: SurfaceExprKind::Match(crate::surface::SurfaceMatchExpr {
                        scrutinee: Box::new(deep_block()),
                        arms: vec![
                            crate::surface::SurfaceMatchArm {
                                pattern: SurfacePattern {
                                    kind: SurfacePatternKind::Wildcard,
                                    span,
                                },
                                body: deep_block(),
                                span,
                            },
                            crate::surface::SurfaceMatchArm {
                                pattern: SurfacePattern {
                                    kind: SurfacePatternKind::Wildcard,
                                    span,
                                },
                                body: missing(),
                                span,
                            },
                        ],
                    }),
                    span,
                };
                assert_eq!(
                    resolver()
                        .resolve_expr(&matched)
                        .expect_err("the late match body should be unknown")
                        .reason,
                    ResolveReason::UnknownName,
                );

                let late_annotation = SurfaceExpr {
                    kind: SurfaceExprKind::Block(SurfaceBlock {
                        declarations: vec![SurfaceLocalDeclaration::Binding(Box::new(
                            SurfaceBinding {
                                pattern: SurfacePattern {
                                    kind: SurfacePatternKind::Wildcard,
                                    span,
                                },
                                annotation: Some(SurfaceType {
                                    kind: SurfaceTypeKind::Named(name("Missing")),
                                    span,
                                }),
                                initializer: deep_block(),
                                span,
                            },
                        ))],
                        result: Box::new(SurfaceExpr {
                            kind: SurfaceExprKind::Unit,
                            span,
                        }),
                        span,
                    }),
                    span,
                };
                assert_eq!(
                    resolver()
                        .resolve_expr(&late_annotation)
                        .expect_err("the late binding annotation should be unknown")
                        .reason,
                    ResolveReason::UnknownType,
                );
            })
            .expect("the late-resolution thread should start")
            .join()
            .expect("late resolver errors must dismantle all completed work iteratively");
    }

    const DEEP_DECLARATION_TYPE_WIDTH: usize = 32_768;

    fn declaration_fixture(name: &str, text: &str) -> SurfaceModule {
        let source = SourceFile::new(name, text).expect("the declaration fixture should fit");
        let tree = parse(lex(&source).expect("the declaration fixture should lex"));
        project_module(&source, &tree).expect("the declaration fixture should project")
    }

    #[test]
    fn lexical_method_lookup_and_parameter_registry_have_exact_work_boundaries() {
        for (interface_count, method_count, parameter_count) in
            [(1, 1, 0), (64, 1, 0), (1, 64, 0), (1, 1, 2)]
        {
            let mut text = String::from("interface R<A> {\n");
            text.push_str(if parameter_count == 0 {
                "read : A -> Unit\n"
            } else {
                "read<X, Y> : (A, X, Y) -> Unit\n"
            });
            for index in 1..method_count {
                text.push_str(&format!("spare{index} : A -> Unit\n"));
            }
            text.push_str("}\n");
            for index in 1..interface_count {
                text.push_str(&format!(
                    "interface Spare{index}<A> {{\nspareInterface{index} : A -> Unit\n}}\n"
                ));
            }
            text.push_str(
                "main : Unit -> Unit\nmain () = {\nwith R<Unit> {\nread ignored = ()\n}\n()\n}\n",
            );
            let surface = declaration_fixture("lexical-method-lookup-work.ash", &text);
            let SurfaceDefinitionKind::Equational(main) = &surface.definitions[0].kind else {
                panic!("equational main");
            };
            let SurfaceExprKind::Block(block) = &main.equations[0].body.kind else {
                panic!("evidence block");
            };
            let SurfaceLocalDeclaration::Evidence(source) = &block.declarations[0] else {
                panic!("lexical source");
            };
            let fresh = || {
                let mut resolver = Resolver::new(ModuleId::new(7_015));
                let mut declarations = resolver
                    .resolve_declarations(&surface)
                    .expect("resolved fixture");
                resolver.resolved_interfaces =
                    ResolvedInterfaceBuffer(std::mem::take(&mut declarations.interfaces));
                resolver.type_work = TypeWorkBudget::unbounded();
                resolver
            };
            let resolver = fresh();
            let parameters = &resolver.resolved_interfaces.0[0].methods[0].type_parameters;
            assert_eq!(parameters.len(), parameter_count);
            let mut parameter_clones = TypeWorkBudget::unbounded();
            for parameter in parameters {
                clone_resolved_type_variable_with_budget(parameter, &mut parameter_clones)
                    .expect("canonical parameter clone");
            }
            // Full local interface and method tables; two retained parameter
            // buffers and two copies of each parameter's unchanged metadata.
            let exact_work =
                interface_count + method_count + 2 * parameter_count + 2 * parameter_clones.used();
            let mut short = fresh();
            short.type_work = TypeWorkBudget::with_limit(exact_work - 1);
            let failure = short
                .resolve_lexical_method_group(source, 0)
                .expect_err("one-short lookup/registry work must reject");
            assert_eq!(failure.reason, ResolveReason::TypeResourceExhausted);
            for _ in 0..2 {
                let mut exact = fresh();
                exact.type_work = TypeWorkBudget::with_limit(exact_work);
                let (group, end) = exact
                    .resolve_lexical_method_group(source, 0)
                    .expect("fresh exact retry");
                assert_eq!(end, 1);
                assert_eq!(group.contextual_parameters.len(), parameter_count);
                assert_eq!(exact.lexical_method_parameters.0.len(), parameter_count);
                assert_eq!(exact.type_work.used(), exact_work);
            }
            let imported_fresh = || {
                let row = &resolver.resolved_interfaces.0[0];
                let fact = CheckedInterfaceFact::new(
                    row.id,
                    row.spelling.clone(),
                    row.parameters.clone(),
                    None,
                    row.methods
                        .iter()
                        .map(|method| {
                            CheckedInterfaceMethodFact::with_mirrored_binder_authority_for_test(
                                method.id,
                                method.spelling.clone(),
                                method.type_parameters.clone(),
                                method.annotation.ty.clone(),
                                method.origin.clone(),
                                method.annotation.span,
                                method.span,
                            )
                        })
                        .collect(),
                    row.origin.clone(),
                    row.span,
                );
                let mut imported = Resolver::new(ModuleId::new(7_016));
                imported.method_names.insert(
                    "read".into(),
                    ResolvedTermBinding::imported(
                        ResolvedTermName::Method(row.methods[0].id),
                        source.span,
                    ),
                );
                imported
                    .imported
                    .insert_interface(fact, row.id.module(), source.span, true);
                imported
            };
            let imported_work = exact_work - interface_count;
            for one_short in [true, false, false] {
                let mut imported = imported_fresh();
                imported.type_work =
                    TypeWorkBudget::with_limit(imported_work - usize::from(one_short));
                let result = imported.resolve_lexical_method_group(source, 0);
                if one_short {
                    assert_eq!(
                        result.expect_err("one-short imported method lookup").reason,
                        ResolveReason::TypeResourceExhausted
                    );
                } else {
                    let (group, _) = result.expect("fresh exact imported retry");
                    assert_eq!(group.contextual_parameters.len(), parameter_count);
                    assert_eq!(imported.type_work.used(), imported_work);
                }
            }
            let mut no_method = fresh();
            no_method.method_names.clear();
            no_method.type_work = TypeWorkBudget::with_limit(0);
            let (group, _) = no_method
                .resolve_lexical_method_group(source, 0)
                .expect("unknown method defers to existing membership checking");
            assert!(group.method.is_none());
            assert_eq!(no_method.type_work.used(), 0);
        }
    }

    #[test]
    fn local_newtype_fact_retention_is_exact_atomic_and_retryable() {
        const EXACT_WORK: usize = 7;
        let surface = declaration_fixture(
            "local-newtype-fact-budget.ash",
            concat!(
                "main : Unit -> Unit\n",
                "main () = {\n",
                "    newtype Token = Token(Int)\n",
                "    ()\n",
                "}\n",
            ),
        );
        let SurfaceDefinitionKind::Equational(main) = &surface.definitions[0].kind else {
            panic!("expected equational main")
        };
        let SurfaceExprKind::Block(block) = &main.equations[0].body.kind else {
            panic!("expected local-newtype block")
        };
        let SurfaceLocalDeclaration::Newtype(declaration) = &block.declarations[0] else {
            panic!("expected local newtype")
        };

        let module = ModuleId::new(7_014);
        let mut resolver =
            Resolver::with_type_work(module, TypeWorkBudget::with_limit(EXACT_WORK - 1));
        resolver.lexical_nominal_scopes.push(HashMap::new());
        resolver.lexical_constructor_scopes.push(HashMap::new());
        let error = resolver
            .resolve_local_newtype(declaration)
            .expect_err("one missing fact unit must reject before publication");
        assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(resolver.type_work.used(), 1);
        assert!(resolver.lexical_nominals.0.is_empty());
        assert!(resolver.lexical_constructors.0.is_empty());
        assert!(resolver.lexical_nominal_parameters.0.is_empty());
        assert!(resolver.lexical_nominal_scopes[0].is_empty());
        assert!(resolver.lexical_constructor_scopes[0].is_empty());
        assert_eq!(resolver.next_lexical_nominal, 0);

        resolver.type_work = TypeWorkBudget::with_limit(EXACT_WORK);
        let owner = resolver
            .resolve_local_newtype(declaration)
            .expect("the exact retry should publish one complete fact family");
        assert_eq!(owner, NominalTypeId::lexical(module, 0));
        assert_eq!(resolver.type_work.used(), EXACT_WORK);
        assert_eq!(resolver.lexical_nominals.0.len(), 1);
        assert_eq!(resolver.lexical_constructors.0.len(), 1);
        assert_eq!(resolver.lexical_nominal_parameters.0.len(), 1);
        assert_eq!(
            resolver.lexical_nominal_scopes[0].get("Token"),
            Some(&owner)
        );
        assert_eq!(
            resolver.lexical_constructor_scopes[0]
                .get("Token")
                .map(|constructor| constructor.owner()),
            Some(owner),
        );
    }

    #[test]
    fn deep_lexical_nominal_and_constructor_probes_are_exact_atomic_and_retryable() {
        const DEPTH: usize = 32_768;
        let source = SourceFile::new("deep-lexical-lookup-budget.ash", "Deep")
            .expect("the lexical lookup fixture should fit");
        let span = source
            .span(ByteRange::new(0, 4).expect("the range should be ordered"))
            .expect("the range should belong to the fixture");
        let reference = SurfaceReference::Unqualified(SurfaceName {
            text: "Deep".to_owned(),
            span,
        });
        let owner = NominalTypeId::lexical(ModuleId::new(7_014), 0);
        let constructor = ConstructorId::new(owner, 0);
        let mut resolver =
            Resolver::with_type_work(ModuleId::new(7_014), TypeWorkBudget::with_limit(DEPTH - 1));
        let mut outer_nominals = HashMap::new();
        outer_nominals.insert("Deep".to_owned(), owner);
        resolver.lexical_nominal_scopes.push(outer_nominals);
        resolver
            .lexical_nominal_scopes
            .extend((1..DEPTH).map(|_| HashMap::new()));
        let mut outer_constructors = HashMap::new();
        outer_constructors.insert("Deep".to_owned(), constructor);
        resolver.lexical_constructor_scopes.push(outer_constructors);
        resolver
            .lexical_constructor_scopes
            .extend((1..DEPTH).map(|_| HashMap::new()));

        let error = resolver
            .nominal_reference(&reference)
            .expect_err("one missing probe unit must reject the outer nominal lookup");
        assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(resolver.type_work.used(), DEPTH - 1);
        assert_eq!(resolver.lexical_nominal_scopes.len(), DEPTH);
        assert_eq!(resolver.lexical_nominal_scopes[0].get("Deep"), Some(&owner));

        resolver.type_work = TypeWorkBudget::with_limit(DEPTH);
        assert_eq!(
            resolver
                .nominal_reference(&reference)
                .expect("the exact retry should reach the outer nominal")
                .id,
            owner,
        );
        assert_eq!(resolver.type_work.used(), DEPTH);

        resolver.type_work = TypeWorkBudget::with_limit(DEPTH - 1);
        let error = resolver
            .constructor_reference(&reference)
            .expect_err("one missing probe unit must reject the outer constructor lookup");
        assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(resolver.type_work.used(), DEPTH - 1);
        assert_eq!(resolver.lexical_constructor_scopes.len(), DEPTH);
        assert_eq!(
            resolver.lexical_constructor_scopes[0].get("Deep"),
            Some(&constructor),
        );

        resolver.type_work = TypeWorkBudget::with_limit(DEPTH);
        assert_eq!(
            resolver
                .constructor_reference(&reference)
                .expect("the exact retry should reach the outer constructor"),
            constructor,
        );
        assert_eq!(resolver.type_work.used(), DEPTH);

        let expression = SurfaceExpr {
            kind: SurfaceExprKind::Name(reference),
            span,
        };
        resolver.type_work = TypeWorkBudget::with_limit(DEPTH - 1);
        let error = resolver
            .resolve_expr(&expression)
            .expect_err("one missing probe unit must reject inline constructor lookup");
        assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(resolver.type_work.used(), DEPTH - 1);
        assert_eq!(resolver.lexical_constructor_scopes.len(), DEPTH);

        resolver.type_work = TypeWorkBudget::with_limit(DEPTH);
        let resolved = resolver
            .resolve_expr(&expression)
            .expect("the exact inline retry should reach the outer constructor");
        let ResolvedExprKind::Constructor(occurrence) = resolved.kind else {
            panic!("the inline lookup should resolve the constructor")
        };
        assert_eq!(occurrence.constructor, constructor);
        assert_eq!(resolver.type_work.used(), DEPTH);
    }

    #[test]
    fn fixed_kind_binder_allocation_is_exact_and_atomic() {
        // One Arrow, two Type leaves, and one retained binder record cost four units.
        const EXACT_WORK: usize = 4;
        let surface = declaration_fixture(
            "kind-binder-budget.ash",
            "type Holder<F : Type -> Type> = Holder\n",
        );
        let parameter = &surface.type_declarations[0].parameters[0];

        let mut short =
            Resolver::with_type_work(ModuleId::new(0), TypeWorkBudget::with_limit(EXACT_WORK - 1));
        let error = short
            .allocate_type_variable(&parameter.name, parameter.kind.as_ref(), Kind::Type)
            .expect_err("one missing record unit must reject the whole binder");
        assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(short.type_work.used(), EXACT_WORK - 1);
        assert_eq!(short.next_type_variable, 0);

        let mut exact =
            Resolver::with_type_work(ModuleId::new(0), TypeWorkBudget::with_limit(EXACT_WORK));
        let retained = exact
            .allocate_type_variable(&parameter.name, parameter.kind.as_ref(), Kind::Type)
            .expect("the exact kind-and-record budget should retain one binder");
        assert_eq!(exact.type_work.used(), EXACT_WORK);
        assert_eq!(exact.next_type_variable, 1);
        assert_eq!(
            retained.kind,
            Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
        );
    }

    #[test]
    fn method_parameter_validation_is_exact_atomic_and_retryable() {
        // Interface duplicate validation and the method free-name set each
        // visit owner A once. Method duplicate validation visits the declared
        // and first-occurrence sets for A, B, and C.
        const OWNER_AND_BINDER_SET_VISITS: usize = 1 + 1 + 2 * 3;
        // Interface A costs two units, the method type has six surface nodes,
        // and omitted-kind B and C cost two units each.
        const COMPLETE_WORK: usize = 2 + OWNER_AND_BINDER_SET_VISITS + 6 + 2 * 2;
        let surface = declaration_fixture(
            "method-parameter-validation-budget.ash",
            "interface Fixture<A> {\nmethod<B, C> : (A, B, C) -> A\n}\n",
        );
        let declaration = &surface.interfaces[0];

        let mut short = Resolver::with_type_work(
            ModuleId::new(0),
            TypeWorkBudget::with_limit(COMPLETE_WORK - 1),
        );
        let failure = match short.prepare_interface_type_parameters(declaration) {
            Err(failure) => failure,
            Ok(_) => {
                panic!("one missing validation or retention unit must reject the method binders")
            }
        };
        assert_eq!(failure.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(short.type_work.used(), COMPLETE_WORK - 1);

        let mut exact =
            Resolver::with_type_work(ModuleId::new(0), TypeWorkBudget::with_limit(COMPLETE_WORK));
        let prepared = exact
            .prepare_interface_type_parameters(declaration)
            .expect("the exact validation and retention budget should fit");
        assert_eq!(exact.type_work.used(), COMPLETE_WORK);
        assert_eq!(exact.next_type_variable, 3);
        assert_eq!(
            prepared.methods[0]
                .iter()
                .map(|parameter| parameter.spelling.as_str())
                .collect::<Vec<_>>(),
            ["B", "C"],
        );

        for (source, validation_work, spelling, primary_occurrence, related_occurrence) in [
            (
                "interface Duplicate<A> {\nmethod<A> : A -> A\n}\n",
                4,
                "A",
                1,
                0,
            ),
            (
                "interface Duplicate<A> {\nmethod<B, B> : (A, B) -> B\n}\n",
                6,
                "B",
                1,
                0,
            ),
        ] {
            let surface = declaration_fixture("duplicate-method-parameter.ash", source);
            let declaration = &surface.interfaces[0];
            // Interface validation and allocation cost three units; method
            // free-name owner installation costs one more before the atomic
            // two-set duplicate-validation charge.
            let exact_work = 4 + validation_work;

            let mut short = Resolver::with_type_work(
                ModuleId::new(0),
                TypeWorkBudget::with_limit(exact_work - 1),
            );
            let failure = match short.prepare_interface_type_parameters(declaration) {
                Err(failure) => failure,
                Ok(_) => panic!("one-short validation must fail before duplicate publication"),
            };
            assert_eq!(failure.reason, ResolveReason::TypeResourceExhausted);
            assert_eq!(
                short.type_work.used(),
                4,
                "the all-at-once validation charge must not partially publish",
            );
            short
                .type_work
                .charge(exact_work - 5)
                .expect("the rejected validation charge must leave its capacity reusable");
            assert_eq!(short.type_work.used(), exact_work - 1);
            assert_eq!(short.next_type_variable, 1);

            let mut exact =
                Resolver::with_type_work(ModuleId::new(0), TypeWorkBudget::with_limit(exact_work));
            let failure = match exact.prepare_interface_type_parameters(declaration) {
                Err(failure) => failure,
                Ok(_) => panic!("the exact validation budget should reach the duplicate"),
            };
            assert_eq!(failure.reason, ResolveReason::DuplicateTypeParameter);
            assert_eq!(exact.type_work.used(), exact_work);
            assert_eq!(exact.next_type_variable, 1);
            assert_eq!(failure.related.len(), 1);
            let expected_primary = source
                .match_indices(spelling)
                .nth(primary_occurrence)
                .map(|(offset, _)| offset as u32)
                .expect("the duplicate primary marker should exist");
            let expected_related = source
                .match_indices(spelling)
                .nth(related_occurrence)
                .map(|(offset, _)| offset as u32)
                .expect("the duplicate related marker should exist");
            assert_eq!(failure.primary.span().range().start(), expected_primary,);
            assert_eq!(failure.primary.span().range().end(), expected_primary + 1);
            assert_eq!(failure.related[0].span().range().start(), expected_related);
            assert_eq!(
                failure.related[0].span().range().end(),
                expected_related + 1
            );
        }
    }

    #[test]
    fn wide_interface_parameter_and_method_scope_work_is_exact_atomic_and_retryable() {
        const PARAMETER_COUNT: usize = 32;
        const METHOD_COUNT: usize = 32;
        // Preparation visits each interface binder once for duplicate
        // validation and retains its Type Kind plus binder record. Every
        // method then installs the P owners in both free-name sets and visits
        // the three nodes of `P0 -> P0`:
        //   3P + M(2P + 3).
        const PREPARATION_WORK: usize =
            3 * PARAMETER_COUNT + METHOD_COUNT * (2 * PARAMETER_COUNT + 3);
        // Resolution clones every canonical interface binder, then each
        // method retains one P-wide scope map and resolves the same three
        // annotation nodes:
        //   2P + M(P + 3).
        const RESOLUTION_WORK: usize = 2 * PARAMETER_COUNT + METHOD_COUNT * (PARAMETER_COUNT + 3);
        const EXACT_WORK: usize = PREPARATION_WORK + RESOLUTION_WORK;

        let parameter_names = (0..PARAMETER_COUNT)
            .map(|index| format!("P{index}"))
            .collect::<Vec<_>>();
        let mut text = format!("interface Wide<{}> {{\n", parameter_names.join(", "));
        for index in 0..METHOD_COUNT {
            text.push_str(&format!("method{index} : P0 -> P0\n"));
        }
        text.push_str("}\n");
        let surface = declaration_fixture("wide-interface-scope-budget.ash", &text);

        let mut one_short =
            Resolver::with_type_work(ModuleId::new(0), TypeWorkBudget::with_limit(EXACT_WORK - 1));
        let identities = one_short
            .install_interface_identities(&surface.interfaces)
            .expect("the wide interface identities should fit");
        let pending = one_short
            .prepare_interface_type_parameters(&surface.interfaces[0])
            .expect("the one-short boundary should reach resolved scope retention");
        let failure = one_short
            .resolve_interface_declarations(
                &surface.interfaces,
                identities,
                vec![pending],
                surface.span,
            )
            .expect_err("one missing scope or annotation visit must reject atomically");
        assert_eq!(failure.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(one_short.type_work.used(), EXACT_WORK - 1);
        assert!(one_short.type_scopes.is_empty());
        assert_eq!(one_short.next_type_variable as usize, PARAMETER_COUNT);

        let mut exact =
            Resolver::with_type_work(ModuleId::new(0), TypeWorkBudget::with_limit(EXACT_WORK));
        let identities = exact
            .install_interface_identities(&surface.interfaces)
            .expect("the retry identities should fit");
        let pending = exact
            .prepare_interface_type_parameters(&surface.interfaces[0])
            .expect("the retry preparation formula should fit exactly");
        let (interfaces, retained) = exact
            .resolve_interface_declarations(
                &surface.interfaces,
                identities,
                vec![pending],
                surface.span,
            )
            .expect("the exact wide interface formula should resolve");
        assert_eq!(exact.type_work.used(), EXACT_WORK);
        assert!(exact.type_scopes.is_empty());
        assert_eq!(interfaces[0].parameters.len(), PARAMETER_COUNT);
        assert_eq!(interfaces[0].methods.len(), METHOD_COUNT);
        assert_eq!(retained.len(), PARAMETER_COUNT);
    }

    #[test]
    fn interface_parameter_duplicate_validation_is_exact_and_atomic() {
        const DUPLICATE_VISITS: usize = 3;
        let surface = declaration_fixture(
            "interface-duplicate-budget.ash",
            "interface Duplicate<A, B, B> {\nmethod : A -> A\n}\n",
        );
        let declaration = &surface.interfaces[0];

        let mut one_short = Resolver::with_type_work(
            ModuleId::new(0),
            TypeWorkBudget::with_limit(DUPLICATE_VISITS - 1),
        );
        let failure = match one_short.prepare_interface_type_parameters(declaration) {
            Err(failure) => failure,
            Ok(_) => panic!("one-short duplicate validation must fail before binder allocation"),
        };
        assert_eq!(failure.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(one_short.type_work.used(), 0);
        assert_eq!(one_short.next_type_variable, 0);

        let mut exact = Resolver::with_type_work(
            ModuleId::new(0),
            TypeWorkBudget::with_limit(DUPLICATE_VISITS),
        );
        let failure = match exact.prepare_interface_type_parameters(declaration) {
            Err(failure) => failure,
            Ok(_) => panic!("the exact validation budget must reach the duplicate binder"),
        };
        assert_eq!(failure.reason, ResolveReason::DuplicateTypeParameter);
        assert_eq!(exact.type_work.used(), DUPLICATE_VISITS);
        assert_eq!(exact.next_type_variable, 0);
        assert_eq!(failure.related.len(), 1);
    }

    #[test]
    fn interface_determination_resolution_is_exact_atomic_and_retryable() {
        const PARAMETER_COUNT: usize = 16;
        const OCCURRENCE_COUNT: usize = PARAMETER_COUNT * 2;
        // One map insertion per binder, then one lookup and one retained
        // record per written determination occurrence.
        const EXACT_WORK: usize = PARAMETER_COUNT + 2 * OCCURRENCE_COUNT;

        let parameter_names = (0..PARAMETER_COUNT)
            .map(|index| format!("P{index}"))
            .collect::<Vec<_>>();
        let reverse_names = parameter_names.iter().rev().cloned().collect::<Vec<_>>();
        let text = format!(
            "interface Relation<{}> where ({}) -> ({}) {{\nrelate : P0 -> P0\n}}\n",
            parameter_names.join(", "),
            parameter_names.join(", "),
            reverse_names.join(", "),
        );
        let surface = declaration_fixture("determination-budget.ash", &text);
        let declaration = &surface.interfaces[0];
        let determination = declaration
            .determination
            .as_ref()
            .expect("the fixture has one determination");
        let parameters = declaration
            .parameters
            .iter()
            .enumerate()
            .map(|(index, parameter)| ResolvedTypeVariable {
                id: TypeVariableId::resolved(ModuleId::new(0), index as u32),
                spelling: parameter.name.text.clone(),
                kind: Kind::Type,
                origin: Origin::Source(parameter.name.span),
            })
            .collect::<Vec<_>>();

        let mut one_short =
            Resolver::with_type_work(ModuleId::new(0), TypeWorkBudget::with_limit(EXACT_WORK - 1));
        let failure = one_short
            .resolve_interface_determination(determination, &parameters)
            .expect_err("one missing retained occurrence must reject the determination");
        assert_eq!(failure.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(one_short.type_work.used(), EXACT_WORK - 1);

        let mut exact =
            Resolver::with_type_work(ModuleId::new(0), TypeWorkBudget::with_limit(EXACT_WORK));
        let resolved = exact
            .resolve_interface_determination(determination, &parameters)
            .expect("a fresh exact retry should retain every occurrence");
        assert_eq!(exact.type_work.used(), EXACT_WORK);
        assert_eq!(resolved.determinant.parameters.len(), PARAMETER_COUNT);
        assert_eq!(resolved.dependent.parameters.len(), PARAMETER_COUNT);
        assert_eq!(resolved.determinant.parameters[0].spelling, "P0");
        assert_eq!(resolved.dependent.parameters[0].spelling, "P15");
    }

    #[test]
    fn late_unknown_determination_name_has_an_exact_retryable_boundary() {
        // Four map insertions, three successful lookup/retention pairs, then
        // the late unknown lookup itself.
        const EXACT_UNKNOWN_WORK: usize = 4 + 2 * 3 + 1;
        let text = concat!(
            "interface Relation<A, B, C, D> where (A, B) -> (C, Missing) {\n",
            "relate : A -> A\n",
            "}\n",
        );
        let surface = declaration_fixture("late-unknown-determination-budget.ash", text);
        let declaration = &surface.interfaces[0];
        let determination = declaration
            .determination
            .as_ref()
            .expect("the fixture has one determination");
        let parameters = declaration
            .parameters
            .iter()
            .enumerate()
            .map(|(index, parameter)| ResolvedTypeVariable {
                id: TypeVariableId::resolved(ModuleId::new(0), index as u32),
                spelling: parameter.name.text.clone(),
                kind: Kind::Type,
                origin: Origin::Source(parameter.name.span),
            })
            .collect::<Vec<_>>();

        let mut one_short = Resolver::with_type_work(
            ModuleId::new(0),
            TypeWorkBudget::with_limit(EXACT_UNKNOWN_WORK - 1),
        );
        let failure = one_short
            .resolve_interface_determination(determination, &parameters)
            .expect_err("one missing lookup visit must stop before the late unknown name");
        assert_eq!(failure.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(one_short.type_work.used(), EXACT_UNKNOWN_WORK - 1);

        let mut exact = Resolver::with_type_work(
            ModuleId::new(0),
            TypeWorkBudget::with_limit(EXACT_UNKNOWN_WORK),
        );
        let failure = exact
            .resolve_interface_determination(determination, &parameters)
            .expect_err("a fresh exact retry must reach the causal unknown spelling");
        assert_eq!(failure.reason, ResolveReason::UnknownType);
        assert_eq!(exact.type_work.used(), EXACT_UNKNOWN_WORK);
        let missing = text.find("Missing").expect("the unknown spelling exists") as u32;
        assert_eq!(failure.primary.span().range().start(), missing);
        assert_eq!(failure.primary.span().range().end(), missing + 7);
    }

    #[test]
    fn global_registry_binder_retention_is_exact_and_atomic() {
        // One retained binder record plus one Arrow and two Type leaves.
        const EXACT_WORK: usize = 4;
        let surface = declaration_fixture(
            "global-registry-kind-budget.ash",
            "uses<F : Type -> Type> : F -> F\nuses value = value\n",
        );
        let span = surface.definitions[0].span;
        let parameter = ResolvedTypeVariable {
            id: TypeVariableId::resolved(ModuleId::new(0), 41),
            spelling: "F".to_owned(),
            kind: Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type)),
            origin: Origin::Source(span),
        };
        let parameters = vec![vec![parameter]];

        let mut short =
            Resolver::with_type_work(ModuleId::new(0), TypeWorkBudget::with_limit(EXACT_WORK - 1));
        short.next_type_variable = 43;
        let registry = ResolvedRegistry::new(Vec::new(), Vec::new());
        let error = short
            .clone_global_type_parameters_for_registry(&parameters, span)
            .expect_err("one missing Kind node must reject the staged registry copy");
        assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(short.type_work.used(), EXACT_WORK - 1);
        assert_eq!(short.next_type_variable, 43);
        assert!(registry.type_variable(parameters[0][0].id).is_none());

        let mut exact =
            Resolver::with_type_work(ModuleId::new(0), TypeWorkBudget::with_limit(EXACT_WORK));
        exact.next_type_variable = 43;
        let retained = exact
            .clone_global_type_parameters_for_registry(&parameters, span)
            .expect("the exact binder-kind budget should stage the complete registry copy");
        let registry = registry.with_additional_type_variables(retained);
        assert_eq!(exact.type_work.used(), EXACT_WORK);
        assert_eq!(exact.next_type_variable, 43);
        let retained = registry
            .type_variable(parameters[0][0].id)
            .expect("the successful staged copy should publish one registry record");
        assert_eq!(retained.kind, parameters[0][0].kind);
    }

    #[test]
    fn imported_parameter_clone_late_failure_dismantles_deep_completed_binders() {
        const DEPTH: usize = 32_768;
        const FIRST_PARAMETER_WORK: usize = 2;
        const SECOND_PARAMETER_RECORD_WORK: usize = 1;
        const EXACT_WORK: usize = 2 * FIRST_PARAMETER_WORK;

        std::thread::Builder::new()
            .name("imported-parameter-late-clone-rejection".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("imported-parameters.ash", "Pair")
                    .expect("the imported-parameter source should fit");
                let span = source
                    .span(ByteRange::new(0, 4).expect("the parameter range should be ordered"))
                    .expect("the parameter range should belong to the fixture");
                let module = ModuleId::new(9_001);
                let mut deep_origin = Origin::Source(span);
                for _ in 0..DEPTH {
                    deep_origin = Origin::Generated {
                        cause: Box::new(deep_origin),
                        reason: crate::source::GeneratedReason::TypeChecking,
                    };
                }
                let parameters = vec![
                    ResolvedTypeVariable {
                        id: TypeVariableId::resolved(module, 0),
                        spelling: "A".to_owned(),
                        kind: Kind::Type,
                        origin: deep_origin,
                    },
                    ResolvedTypeVariable {
                        id: TypeVariableId::resolved(module, 1),
                        spelling: "B".to_owned(),
                        kind: Kind::Type,
                        origin: Origin::Source(span),
                    },
                ];

                let mut short = Resolver::with_type_work(
                    ModuleId::new(9_002),
                    TypeWorkBudget::with_limit(FIRST_PARAMETER_WORK + SECOND_PARAMETER_RECORD_WORK),
                );
                let failure = short
                    .clone_type_variables_for_retention(
                        &parameters,
                        span,
                        "imported parameter clone exceeded its type-work budget",
                    )
                    .expect_err("the second parameter Kind clone must fail after its record cell");
                assert_eq!(failure.reason, ResolveReason::TypeResourceExhausted);
                assert_eq!(
                    short.type_work.used(),
                    FIRST_PARAMETER_WORK + SECOND_PARAMETER_RECORD_WORK,
                );

                let mut exact = Resolver::with_type_work(
                    ModuleId::new(9_002),
                    TypeWorkBudget::with_limit(EXACT_WORK),
                );
                let retained = exact
                    .clone_type_variables_for_retention(
                        &parameters,
                        span,
                        "imported parameter clone exceeded its type-work budget",
                    )
                    .expect("the immutable imported parameters must remain reusable");
                assert_eq!(exact.type_work.used(), EXACT_WORK);
                assert_eq!(retained.len(), parameters.len());
                for parameter in retained.into_vec() {
                    discard_origin_iteratively(parameter.origin);
                }
                for parameter in parameters {
                    discard_origin_iteratively(parameter.origin);
                }
            })
            .expect("the imported parameter clone worker should spawn")
            .join()
            .expect("accepted and rejected imported binders must tear down iteratively");
    }

    #[test]
    fn imported_implementation_kinded_head_retention_is_exact_and_atomic() {
        const DEPTH: usize = 32_768;
        // M is one method record, A is the argument, C is the complete
        // application-vector carrier, H is one head binder, K is its
        // three-node Kind, and V is the three-cell method value type:
        // M + (C + A) + (H + K) + V + (H + K + V) + A
        // = 1 + 2 + 4 + 3 + 7 + 1 = 18.
        const METHOD_RECORDS: usize = 1;
        const APPLICATION_CARRIER_CELLS: usize = 1;
        const ARGUMENT_CELLS: usize = 1;
        const HEAD_RECORDS: usize = 1;
        const KIND_NODES: usize = 3;
        const VALUE_CELLS: usize = 3;
        const EXACT_WORK: usize = METHOD_RECORDS
            + APPLICATION_CARRIER_CELLS
            + ARGUMENT_CELLS
            + (HEAD_RECORDS + KIND_NODES)
            + VALUE_CELLS
            + (HEAD_RECORDS + KIND_NODES + VALUE_CELLS)
            + ARGUMENT_CELLS;
        const ENTRY: &str = "import dependency (impl Marker)\n";
        const DEPENDENCY: &str = "pub interface Marker<A> {\nmark : A -> A\n}\n";

        std::thread::Builder::new()
            .name("imported-implementation-deep-head-rejection".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let fixture = ImportBudgetFixture::create(ENTRY, DEPENDENCY);
                let graph = load_module_graph(&fixture.0.join("entry.ash"), &ModuleRoots::empty())
                    .expect("the implementation-retention graph should load");
                let dependency = graph
                    .modules()
                    .iter()
                    .find(|module| {
                        Path::new(module.source().display_path()).file_name()
                            == Some("dependency.ash".as_ref())
                    })
                    .expect("the implementation-retention dependency should load");
                let checked_dependency = check_module(
                    resolve_module(dependency, &[]).expect("the dependency should resolve"),
                )
                .expect("the dependency interface should check");
                let entry = graph
                    .module(graph.entry())
                    .expect("the implementation-retention entry should load");
                let import = entry
                    .surface()
                    .imports
                    .first()
                    .expect("the entry should retain its implementation selector");
                let SurfaceImportSelection::Targeted(items) = &import.selection else {
                    panic!("the fixture should contain a targeted import");
                };
                let SurfaceImportItem::Implementation { span, .. } = &items[0] else {
                    panic!("the fixture should select implementations");
                };

                let module = checked_dependency.module();
                let interface = InterfaceId::new(module, 0);
                let method = MethodId::new(interface, 0);
                let implementation = ImplId::new(module, 0);
                let implementation_method = ImplMethodId::new(implementation, method);
                let parameter = TypeVariableId::resolved(module, 0);
                let kind = || Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
                let source_span = dependency.surface().span;
                let mut parameter_origin = Origin::Source(source_span);
                for _ in 0..DEPTH {
                    parameter_origin = Origin::Generated {
                        cause: Box::new(parameter_origin),
                        reason: crate::source::GeneratedReason::TypeChecking,
                    };
                }
                let fact = CheckedImplementationFact {
                    id: implementation,
                    application: crate::interface::InterfaceApplication::new(
                        interface,
                        Box::new([Type::Variable(parameter)]),
                    ),
                    head_parameters: Box::new([ResolvedTypeVariable {
                        id: parameter,
                        spelling: "F".to_owned(),
                        kind: kind(),
                        origin: parameter_origin,
                    }]),
                    prerequisites: Box::new([]),
                    methods: Box::new([crate::resolved::CheckedImplementationMethodFact {
                        capture: crate::core::capture::CaptureValueSummary::default(),
                        id: implementation_method,
                        method,
                        binder: BinderId::resolved(module, 0),
                        scheme: ConstrainedScheme {
                            type_parameters: Box::new([(parameter, kind())]),
                            requirements: Box::new([]),
                            value_type: Type::Function(
                                Box::new(Type::Variable(parameter)),
                                Box::new(Type::Variable(parameter)),
                            ),
                        },
                        head_type_parameter_count: 1,
                        origin: Origin::Source(source_span),
                        span: source_span,
                    }]),
                    origin: Origin::Source(source_span),
                    span: source_span,
                };
                let exported = AuthorizedImplementationFact::local_for_test(fact);
                let selection = ImplementationImportSelection {
                    direct_dependency: module,
                    selector_span: *span,
                    import_span: import.span,
                    public: false,
                    route_rank: ImplementationRouteRank::new(0, 0, 0),
                };

                let retain_with_limit = |limit| {
                    let mut resolver = Resolver::with_budgets(
                        entry.id(),
                        TypeWorkBudget::with_limit(limit),
                        InterfaceConstraintBudget::default(),
                    );
                    let result = resolver.retain_imported_implementation_fact(
                        &exported,
                        checked_dependency.exports(),
                        selection,
                        &mut CaptureGraphVisits::default(),
                    );
                    let retained_kind = resolver
                        .imported
                        .implementation(implementation)
                        .map(|fact| fact.head_parameters[0].kind.clone());
                    let retained_identity = resolver
                        .implementation_route_ranks
                        .contains_key(&implementation)
                        || resolver
                            .public_implementation_route_ranks
                            .contains_key(&implementation);
                    (
                        result,
                        resolver.type_work.used(),
                        retained_kind,
                        retained_identity,
                    )
                };

                let (short, short_used, short_kind, short_identity) =
                    retain_with_limit(EXACT_WORK - 1);
                let error =
                    short.expect_err("one missing type-work unit must reject the whole fact");
                assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
                assert_eq!(short_used, EXACT_WORK - 1);
                assert_eq!(short_kind, None);
                assert!(!short_identity);

                let (exact, exact_used, exact_kind, exact_identity) = retain_with_limit(EXACT_WORK);
                exact.expect("the exact implementation-retention budget should fit");
                assert_eq!(exact_used, EXACT_WORK);
                assert_eq!(exact_kind, Some(kind()));
                assert!(exact_identity);
            })
            .expect("the imported implementation retention worker should spawn")
            .join()
            .expect("accepted and rejected implementation facts must tear down iteratively");
    }

    #[test]
    fn imported_method_binder_kind_authentication_is_exact() {
        // One compared binder record plus one Arrow and two Type pairs.
        const EXACT_WORK: usize = 4;
        let surface = declaration_fixture(
            "imported-method-kind-authentication.ash",
            "uses<F : Type -> Type> : F -> F\nuses value = value\n",
        );
        let span = surface.definitions[0].span;
        let id = TypeVariableId::resolved(ModuleId::new(0), 0);
        let kind = || Kind::Arrow(Box::new(Kind::Type), Box::new(Kind::Type));
        let scheme = [(id, kind())];
        let binders = [ResolvedTypeVariable {
            id,
            spelling: "F".to_owned(),
            kind: kind(),
            origin: Origin::Source(span),
        }];

        let mut short = InterfaceConstraintBudget::with_limit(EXACT_WORK - 1);
        assert_eq!(
            same_kinded_parameters_with_constraint_budget(&scheme, &binders, &mut short),
            Err(()),
        );
        assert_eq!(short.used(), EXACT_WORK - 1);

        let mut exact = InterfaceConstraintBudget::with_limit(EXACT_WORK);
        assert_eq!(
            same_kinded_parameters_with_constraint_budget(&scheme, &binders, &mut exact),
            Ok(true),
        );
        assert_eq!(exact.used(), EXACT_WORK);

        let mismatched = [(id, Kind::Type)];
        let mut mismatch = InterfaceConstraintBudget::with_limit(2);
        assert_eq!(
            same_kinded_parameters_with_constraint_budget(&mismatched, &binders, &mut mismatch),
            Ok(false),
        );
        assert_eq!(mismatch.used(), 2);
    }

    #[test]
    fn deep_surface_kind_conversion_is_linear_exact_and_stack_safe() {
        const DEPTH: usize = 32_768;
        const NODES: usize = 2 * DEPTH + 1;

        struct SurfaceKindOwner(Option<SurfaceKind>);

        impl Drop for SurfaceKindOwner {
            fn drop(&mut self) {
                let Some(surface) = self.0.take() else {
                    return;
                };
                let mut work = vec![surface];
                while let Some(SurfaceKind { kind, .. }) = work.pop() {
                    if let SurfaceKindKind::Function { domain, codomain } = kind {
                        work.push(*codomain);
                        work.push(*domain);
                    }
                }
            }
        }

        std::thread::Builder::new()
            .name("deep-surface-kind-conversion".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("deep-kind.ash", "Type")
                    .expect("the deep kind fixture should fit");
                let span = source
                    .span(ByteRange::new(0, 4).expect("the kind range should be ordered"))
                    .expect("the kind range should belong to the fixture");
                let mut surface = SurfaceKind {
                    kind: SurfaceKindKind::Type,
                    span,
                };
                for _ in 0..DEPTH {
                    surface = SurfaceKind {
                        kind: SurfaceKindKind::Function {
                            domain: Box::new(SurfaceKind {
                                kind: SurfaceKindKind::Type,
                                span,
                            }),
                            codomain: Box::new(surface),
                        },
                        span,
                    };
                }

                let surface_owner = SurfaceKindOwner(Some(surface));
                let surface = surface_owner
                    .0
                    .as_ref()
                    .expect("the fixture should remain owned");
                reset_surface_kind_conversion_counts();
                reset_kind_node_charge_visits();
                let mut exact = TypeWorkBudget::with_limit(NODES);
                let converted = surface_kind_to_kind(surface, &mut exact)
                    .expect("the exact source-kind node budget should convert the deep kind");
                assert_eq!(exact.used(), NODES);
                assert_eq!(
                    surface_kind_conversion_counts(),
                    (NODES, DEPTH, NODES),
                    "each source node must transition Visit -> Arrow when needed -> rebuilt exactly once",
                );
                assert_eq!(
                    kind_node_charge_visits(),
                    0,
                    "surface conversion must not retraverse rebuilt semantic kinds",
                );

                let mut short = TypeWorkBudget::with_limit(NODES - 1);
                assert_eq!(surface_kind_to_kind(surface, &mut short), Err(()));
                assert_eq!(short.used(), NODES - 1);
                drop(converted);
            })
            .expect("the deep surface-kind thread should start")
            .join()
            .expect("surface-kind conversion should fit within 256 KiB");
    }

    fn declaration_name(text: &str, span: crate::source::Span) -> SurfaceReference {
        SurfaceReference::Unqualified(SurfaceName {
            text: text.to_owned(),
            span,
        })
    }

    fn declaration_named_type(text: &str, span: crate::source::Span) -> SurfaceType {
        SurfaceType {
            kind: SurfaceTypeKind::Named(declaration_name(text, span)),
            span,
        }
    }

    fn deep_declaration_type(span: crate::source::Span) -> SurfaceType {
        SurfaceType {
            kind: SurfaceTypeKind::Application {
                constructor: declaration_name("Wide", span),
                arguments: vec![
                    SurfaceType {
                        kind: SurfaceTypeKind::Int,
                        span,
                    };
                    DEEP_DECLARATION_TYPE_WIDTH
                ],
            },
            span,
        }
    }

    fn deep_declaration_block(span: crate::source::Span) -> SurfaceExpr {
        SurfaceExpr {
            kind: SurfaceExprKind::Block(SurfaceBlock {
                declarations: vec![SurfaceLocalDeclaration::Binding(Box::new(SurfaceBinding {
                    pattern: SurfacePattern {
                        kind: SurfacePatternKind::Wildcard,
                        span,
                    },
                    annotation: Some(deep_declaration_type(span)),
                    initializer: SurfaceExpr {
                        kind: SurfaceExprKind::Unit,
                        span,
                    },
                    span,
                }))],
                result: Box::new(SurfaceExpr {
                    kind: SurfaceExprKind::Unit,
                    span,
                }),
                span,
            }),
            span,
        }
    }

    fn declaration_resolver(surface: &SurfaceModule) -> Resolver {
        let module = ModuleId::new(0);
        let mut resolver = Resolver::new(module);
        resolver
            .validate_local_namespaces(surface)
            .expect("the ownership fixture namespaces should be valid");
        let owner = NominalTypeId::new(ModuleId::new(1), 0);
        resolver.type_names.insert("Wide".to_owned(), owner);
        resolver
            .nominal_parameter_counts
            .insert(owner, DEEP_DECLARATION_TYPE_WIDTH);
        resolver
    }

    fn expected_declaration_error(
        result: Result<ResolvedDeclarations, ResolveError>,
        message: &str,
    ) -> ResolveError {
        match result {
            Err(error) => error,
            Ok(_) => panic!("{message}"),
        }
    }

    #[test]
    fn late_interface_and_requirement_errors_discard_deep_declarations_on_a_small_stack() {
        std::thread::Builder::new()
            .name("late-interface-requirement-disposal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut interfaces = declaration_fixture(
                    "late-interface.ash",
                    concat!(
                        "interface Marker<A> {\nmark : A\n}\n\n",
                        "interface Target<A> {\nfirst : A\nsecond : A\n}\n",
                    ),
                );
                let span = interfaces.span;
                interfaces.interfaces[1].methods[0].annotation = deep_declaration_type(span);
                interfaces.interfaces[1].methods[1].annotation =
                    declaration_named_type("Marker", span);
                let error = expected_declaration_error(
                    declaration_resolver(&interfaces).resolve_declarations(&interfaces),
                    "the late method annotation should use an interface as a type",
                );
                assert_eq!(error.reason, ResolveReason::TypeKind);

                let mut requirements = declaration_fixture(
                    "late-requirement.ash",
                    concat!(
                        "interface Marker<A> {\nmark : A\n}\n\n",
                        "value : Unit -> Unit where Marker<Int>, Marker<Int>\n",
                        "value () = ()\n",
                    ),
                );
                let span = requirements.span;
                let SurfaceDefinitionKind::Equational(definition) =
                    &mut requirements.definitions[0].kind
                else {
                    panic!("the requirement fixture should remain equational")
                };
                definition.interface.requirements[0].arguments[0] = deep_declaration_type(span);
                definition.interface.requirements[1].interface = declaration_name("Missing", span);
                let error = expected_declaration_error(
                    declaration_resolver(&requirements).resolve_declarations(&requirements),
                    "the later requirement should name no interface",
                );
                assert_eq!(error.reason, ResolveReason::UnknownInterface);
            })
            .expect("the declaration-disposal thread should start")
            .join()
            .expect("late interface and requirement errors must dispose deep work iteratively");
    }

    #[test]
    fn late_definition_and_inline_errors_discard_deep_declarations_on_a_small_stack() {
        std::thread::Builder::new()
            .name("late-definition-inline-disposal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut equations = declaration_fixture(
                    "late-equation.ash",
                    concat!(
                        "value : Unit -> Unit\n",
                        "value () = ()\n",
                        "value other = missing\n",
                    ),
                );
                let span = equations.span;
                let SurfaceDefinitionKind::Equational(definition) =
                    &mut equations.definitions[0].kind
                else {
                    panic!("the equation fixture should remain equational")
                };
                definition.equations[0].body = deep_declaration_block(span);
                let error = expected_declaration_error(
                    declaration_resolver(&equations).resolve_declarations(&equations),
                    "the later equation body should name no term",
                );
                assert_eq!(error.reason, ResolveReason::UnknownName);

                let mut definitions = declaration_fixture(
                    "late-definition.ash",
                    concat!(
                        "first : Unit -> Unit\nfirst () = ()\n\n",
                        "second : Unit -> Unit\nsecond () = missing\n",
                    ),
                );
                let span = definitions.span;
                let SurfaceDefinitionKind::Equational(first) = &mut definitions.definitions[0].kind
                else {
                    panic!("the first definition should remain equational")
                };
                first.equations[0].body = deep_declaration_block(span);
                let error = expected_declaration_error(
                    declaration_resolver(&definitions).resolve_declarations(&definitions),
                    "the later definition body should name no term",
                );
                assert_eq!(error.reason, ResolveReason::UnknownName);

                let mut operational = declaration_fixture(
                    "late-operational.ash",
                    concat!(
                        "interface Marker<A> {\nmark : A\n}\n\n",
                        "fn operational(first : Int, second : Int) -> Int {\n0\n}\n",
                    ),
                );
                let span = operational.span;
                let SurfaceDefinitionKind::InlineOperational(definition) =
                    &mut operational.definitions[0].kind
                else {
                    panic!("the operational fixture should remain inline")
                };
                definition.header.parameters[0].annotation = deep_declaration_type(span);
                definition.header.parameters[1].annotation = declaration_named_type("Marker", span);
                let error = expected_declaration_error(
                    declaration_resolver(&operational).resolve_declarations(&operational),
                    "the later operational parameter annotation should be unknown",
                );
                assert_eq!(error.reason, ResolveReason::TypeKind);
            })
            .expect("the declaration-disposal thread should start")
            .join()
            .expect("late definition and inline errors must dispose deep work iteratively");
    }

    #[test]
    fn late_implementation_errors_discard_deep_groups_on_a_small_stack() {
        std::thread::Builder::new()
            .name("late-implementation-disposal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut surface = declaration_fixture(
                    "late-implementation.ash",
                    concat!(
                        "interface Marker<A> {\nmark : A -> A\n}\n\n",
                        "impl Marker<Int> {\nmark value = value\n}\n\n",
                        "impl Marker<Bool> {\n",
                        "mark value = value\n",
                        "mark other = missing\n",
                        "}\n",
                    ),
                );
                let span = surface.span;
                surface.implementations[0].equations[0].body = deep_declaration_block(span);
                surface.implementations[1].equations[0].body = deep_declaration_block(span);
                let error = expected_declaration_error(
                    declaration_resolver(&surface).resolve_declarations(&surface),
                    "the later implementation equation should name no term",
                );
                assert_eq!(error.reason, ResolveReason::UnknownName);
            })
            .expect("the implementation-disposal thread should start")
            .join()
            .expect("late implementation errors must dispose deep groups iteratively");
    }

    #[test]
    fn late_registry_and_export_errors_discard_deep_declarations_on_a_small_stack() {
        std::thread::Builder::new()
            .name("late-registry-export-disposal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut registry = declaration_fixture(
                    "late-registry.ash",
                    concat!(
                        "type First =\nFirst(Int)\n\n",
                        "type Later =\nLater(Int, Int)\n",
                    ),
                );
                let span = registry.span;
                registry.type_declarations[0].constructors[0].fields[0] =
                    deep_declaration_type(span);
                registry.type_declarations[1].constructors[0].fields[0] =
                    deep_declaration_type(span);
                registry.type_declarations[1].constructors[0].fields[1] =
                    declaration_named_type("Missing", span);
                let error = declaration_resolver(&registry)
                    .resolve_registry(&registry.type_declarations)
                    .expect_err("the later constructor field should name no type");
                assert_eq!(error.reason, ResolveReason::UnknownType);

                let mut exported = declaration_fixture(
                    "late-export.ash",
                    "private_value : Unit -> Unit\nprivate_value () = ()\n",
                );
                let span = exported.span;
                let SurfaceDefinitionKind::Equational(definition) =
                    &mut exported.definitions[0].kind
                else {
                    panic!("the export fixture should remain equational")
                };
                definition.equations[0].body = deep_declaration_block(span);
                let mut resolver = declaration_resolver(&exported);
                let declarations = resolver
                    .resolve_declarations(&exported)
                    .expect("the complete deep declaration should resolve before export staging");
                resolver.type_work = TypeWorkBudget::with_limit(0);
                let error = build_export_candidate(
                    &exported,
                    &declarations.registry,
                    &declarations.interfaces,
                    &declarations.effects,
                    &declarations.definitions,
                    std::mem::take(&mut resolver.public_import_candidate),
                    &mut resolver.type_work,
                )
                .expect_err("export staging should fail after complete declaration resolution");
                assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
            })
            .expect("the registry-disposal thread should start")
            .join()
            .expect("late registry and export errors must dispose deep declarations iteratively");
    }

    #[test]
    fn late_registry_error_discards_an_installed_deep_newtype_representation_on_a_small_stack() {
        std::thread::Builder::new()
            .name("deep-newtype-representation-disposal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut fixture = declaration_fixture(
                    "late-newtype.ash",
                    concat!(
                        "newtype First = First(Int)\n\n",
                        "type Later = Later(Int, Int)\n",
                    ),
                );
                let span = fixture.span;
                fixture.type_declarations[0].constructors[0].fields[0] =
                    deep_declaration_type(span);
                fixture.type_declarations[1].constructors[0].fields[1] =
                    declaration_named_type("Missing", span);
                let error = declaration_resolver(&fixture)
                    .resolve_registry(&fixture.type_declarations)
                    .expect_err(
                        "the later declaration should fail after retaining First's representation",
                    );
                assert_eq!(error.reason, ResolveReason::UnknownType);
            })
            .expect("deep newtype disposal thread should start")
            .join()
            .expect("installed deep newtype representations must drop iteratively");
    }

    #[test]
    fn free_type_discovery_charges_before_retaining_each_name() {
        let source = SourceFile::new("free-type-budget.ash", "A B C")
            .expect("the budget fixture should fit");
        let name = |text: &str, start, end| {
            let span = source
                .span(ByteRange::new(start, end).expect("the range is ordered"))
                .expect("the range belongs to the fixture");
            SurfaceType {
                kind: SurfaceTypeKind::Named(SurfaceReference::Unqualified(SurfaceName {
                    text: text.to_owned(),
                    span,
                })),
                span,
            }
        };
        let annotation = SurfaceType {
            kind: SurfaceTypeKind::Tuple(vec![name("A", 0, 1), name("B", 2, 3), name("C", 4, 5)]),
            span: source
                .span(ByteRange::new(0, 5).expect("the range is ordered"))
                .expect("the range belongs to the fixture"),
        };
        let mut budget = TypeWorkBudget::default();
        budget
            .charge(TYPE_WORK_LIMIT - 2)
            .expect("the fixture leaves two units");
        let mut seen = HashMap::new();
        let mut output = Vec::new();

        let error = collect_free_type_names(
            &annotation,
            &HashMap::new(),
            &HashMap::new(),
            &HashSet::new(),
            &mut seen,
            &mut output,
            true,
            &mut budget,
        )
        .expect_err("the second name exceeds the remaining budget");

        assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(error.primary.span().range().start(), 2);
        assert_eq!(error.primary.span().range().end(), 3);
        assert_eq!(
            output
                .iter()
                .map(|free| free.name.text.as_str())
                .collect::<Vec<_>>(),
            ["A"]
        );
        assert_eq!(seen.get("A"), Some(&Some(FreeTypeNameRole::Type)));
    }

    #[test]
    fn constructor_tuple_payloads_charge_the_synthesized_wrapper_exactly() {
        // One outer nominal provenance record, one constructor provenance
        // record, two field-provenance slots, one synthesized Tuple node, and
        // two resolved Int nodes: 1 + 1 + 2 + 1 + 2 = 7.
        const EXACT_WORK: usize = 7;
        let source = SourceFile::new(
            "constructor-tuple-budget.ash",
            "type Pair =\nPair(Int, Int)\n",
        )
        .expect("the budget fixture should fit");
        let tree = parse(lex(&source).expect("the fixture should lex"));
        let module = project_module(&source, &tree).expect("the fixture should project");
        let second_field_span = module.type_declarations[0].constructors[0].fields[1].span;

        let mut exact = Resolver::new(ModuleId::new(0));
        exact
            .type_work
            .charge(TYPE_WORK_LIMIT - EXACT_WORK)
            .expect("the fixture leaves every named provenance and payload term");
        let (registry, _) = exact
            .resolve_registry(&module.type_declarations)
            .expect("the exact constructor payload allowance should fit");
        assert_eq!(
            registry.constructors()[0].payload,
            Some(Type::Tuple(vec![Type::Int, Type::Int].into_boxed_slice()))
        );
        assert_eq!(exact.type_work.charge(1), Err(()));

        let mut short = Resolver::new(ModuleId::new(0));
        short
            .type_work
            .charge(TYPE_WORK_LIMIT - (EXACT_WORK - 1))
            .expect("the fixture leaves one cell fewer than the complete transaction");
        let error = short
            .resolve_registry(&module.type_declarations)
            .expect_err("the tuple wrapper must consume the remaining budget");
        assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(error.primary.span().range(), second_field_span.range());
    }

    #[test]
    fn wide_constructor_provenance_is_exact_atomic_and_stack_safe() {
        const WIDTH: usize = 32_768;
        // One nominal provenance record, one constructor record, WIDTH field
        // provenance slots, one Tuple wrapper, and WIDTH field Type nodes.
        const EXACT_WORK: usize = 2 * WIDTH + 3;
        std::thread::Builder::new()
            .name("wide-constructor-provenance".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                let fields = std::iter::repeat_n("Int", WIDTH)
                    .collect::<Vec<_>>()
                    .join(", ");
                let text = format!("type Wide =\nWide({fields})\n");
                let source = SourceFile::new("wide-constructor-provenance.ash", &text)
                    .expect("the wide provenance fixture should fit");
                let tree = parse(lex(&source).expect("the wide fixture should lex"));
                let module = project_module(&source, &tree)
                    .expect("the wide fixture should project iteratively");

                for limit in [0, 1, EXACT_WORK - 1] {
                    let mut resolver = Resolver::with_type_work(
                        ModuleId::new(0),
                        TypeWorkBudget::with_limit(limit),
                    );
                    let failure = resolver
                        .resolve_registry(&module.type_declarations)
                        .expect_err("every named one-short transaction must reject atomically");
                    assert_eq!(failure.reason, ResolveReason::TypeResourceExhausted);
                }

                let mut resolver = Resolver::with_type_work(
                    ModuleId::new(0),
                    TypeWorkBudget::with_limit(EXACT_WORK),
                );
                let (registry, provenance) = resolver
                    .resolve_registry(&module.type_declarations)
                    .expect("the published wide provenance formula should fit exactly");
                assert_eq!(resolver.type_work.used(), EXACT_WORK);
                assert_eq!(provenance.len(), 1);
                assert_eq!(provenance[0].len(), 1);
                assert_eq!(provenance[0][0].fields.len(), WIDTH);
                let Some(Type::Tuple(elements)) = &registry.constructors()[0].payload else {
                    panic!("the wide constructor should retain its synthetic Tuple root");
                };
                assert_eq!(elements.len(), WIDTH);
                drop(provenance);
                drop(registry);
            })
            .expect("the wide provenance thread should start")
            .join()
            .expect("wide success, rejection, and teardown should fit 256 KiB");
    }

    #[test]
    fn declaration_order_retention_is_exact_atomic_and_stack_safe() {
        const DECLARATIONS: usize = 32_768;
        std::thread::Builder::new()
            .name("wide-declaration-order-retention".into())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("wide-declaration-order.ash", "x")
                    .expect("the declaration-order fixture should fit");
                let span = source
                    .span(ByteRange::new(0, 1).expect("the range is ordered"))
                    .expect("the range belongs to the fixture");
                let order = (0..DECLARATIONS)
                    .map(SurfaceDeclarationIndex::Global)
                    .collect::<Vec<_>>();

                let mut short = TypeWorkBudget::with_limit(DECLARATIONS - 1);
                let failure = retain_declaration_order(&order, span, &mut short)
                    .expect_err("one missing record unit must publish no order");
                assert_eq!(failure.reason, ResolveReason::TypeResourceExhausted);
                assert_eq!(short.used(), 0);

                let mut exact = TypeWorkBudget::with_limit(DECLARATIONS);
                let retained = retain_declaration_order(&order, span, &mut exact)
                    .expect("one unit per declaration-order record should fit exactly");
                assert_eq!(exact.used(), DECLARATIONS);
                assert_eq!(retained.len(), DECLARATIONS);
                assert_eq!(
                    retained.last(),
                    Some(&crate::resolved::ResolvedDeclarationIndex::Global(
                        DECLARATIONS - 1,
                    ))
                );
            })
            .expect("the declaration-order thread should start")
            .join()
            .expect("order success, failure, and teardown should fit 256 KiB");
    }

    #[test]
    fn wide_tuple_resolution_keeps_pending_type_work_constant_width() {
        const WIDTH: usize = 4_096;

        let source =
            SourceFile::new("wide-tuple-budget.ash", "Int").expect("the budget fixture should fit");
        let span = source
            .span(ByteRange::new(0, 3).expect("the range is ordered"))
            .expect("the range belongs to the fixture");
        let int = SurfaceType {
            kind: SurfaceTypeKind::Int,
            span,
        };
        let annotation = SurfaceType {
            kind: SurfaceTypeKind::Tuple(vec![int; WIDTH]),
            span,
        };
        let mut resolver = Resolver::new(ModuleId::new(0));
        resolver
            .type_work
            .charge(TYPE_WORK_LIMIT - 1)
            .expect("the fixture leaves one unit for the tuple root");

        let error = resolver
            .resolve_type(&annotation)
            .expect_err("the first tuple field exceeds the remaining budget");

        assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
        assert!(
            resolver.max_type_pending_tasks <= 3,
            "wide tuples retained {} pending resolver tasks",
            resolver.max_type_pending_tasks
        );
    }

    #[test]
    fn wide_nominal_application_resolution_keeps_pending_type_work_constant_width() {
        const WIDTH: usize = 4_096;

        let source = SourceFile::new("wide-application-budget.ash", "Wide<Int>")
            .expect("the budget fixture should fit");
        let full_span = source
            .span(ByteRange::new(0, 9).expect("the range is ordered"))
            .expect("the range belongs to the fixture");
        let constructor_span = source
            .span(ByteRange::new(0, 4).expect("the range is ordered"))
            .expect("the range belongs to the fixture");
        let argument_span = source
            .span(ByteRange::new(5, 8).expect("the range is ordered"))
            .expect("the range belongs to the fixture");
        let owner = NominalTypeId::new(source.id(), 0);
        let argument = SurfaceType {
            kind: SurfaceTypeKind::Int,
            span: argument_span,
        };
        let annotation = SurfaceType {
            kind: SurfaceTypeKind::Application {
                constructor: SurfaceReference::Unqualified(SurfaceName {
                    text: "Wide".to_owned(),
                    span: constructor_span,
                }),
                arguments: vec![argument; WIDTH],
            },
            span: full_span,
        };
        let mut resolver = Resolver::new(ModuleId::new(0));
        resolver.type_names.insert("Wide".to_owned(), owner);
        resolver.nominal_parameter_counts.insert(owner, WIDTH);
        resolver
            .type_work
            .charge(TYPE_WORK_LIMIT - 1)
            .expect("the fixture leaves one unit for the application root");

        let error = resolver
            .resolve_type(&annotation)
            .expect_err("the first nominal argument exceeds the remaining budget");

        assert_eq!(error.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(error.primary.span(), argument_span);
        assert!(
            resolver.max_type_pending_tasks <= 3,
            "wide applications retained {} pending resolver tasks",
            resolver.max_type_pending_tasks
        );
    }

    #[test]
    fn nominal_application_provenance_records_each_unary_fold_exactly() {
        let source = SourceFile::new("application-provenance.ash", "Pair<Int, Bool>")
            .expect("the provenance fixture should fit");
        let span = |start, end| {
            source
                .span(ByteRange::new(start, end).expect("the range is ordered"))
                .expect("the range belongs to the fixture")
        };
        let full_span = span(0, 15);
        let constructor_span = span(0, 4);
        let first_span = span(5, 8);
        let second_span = span(10, 14);
        let owner = NominalTypeId::new(source.id(), 0);
        let annotation = SurfaceType {
            kind: SurfaceTypeKind::Application {
                constructor: SurfaceReference::Unqualified(SurfaceName {
                    text: "Pair".to_owned(),
                    span: constructor_span,
                }),
                arguments: vec![
                    SurfaceType {
                        kind: SurfaceTypeKind::Int,
                        span: first_span,
                    },
                    SurfaceType {
                        kind: SurfaceTypeKind::Bool,
                        span: second_span,
                    },
                ],
            },
            span: full_span,
        };
        let mut resolver = Resolver::new(ModuleId::new(0));
        resolver.type_names.insert("Pair".to_owned(), owner);
        resolver.nominal_parameter_counts.insert(owner, 2);

        let resolved = resolver
            .resolve_type(&annotation)
            .expect("the saturated application should resolve");

        let Type::Application(second_function, second_argument) = &resolved.ty else {
            panic!("the second source argument should be the outer unary application")
        };
        assert_eq!(second_argument.as_ref(), &Type::Bool);
        let Type::Application(first_function, first_argument) = second_function.as_ref() else {
            panic!("the first source argument should be the inner unary application")
        };
        assert_eq!(first_function.as_ref(), &Type::Nominal(owner));
        assert_eq!(first_argument.as_ref(), &Type::Int);

        let nodes = resolved.provenance.nodes();
        assert_eq!(nodes.len(), 5);
        assert_eq!(resolved.provenance.root(), 4);
        assert_eq!(nodes[0], ResolvedTypeProvenanceNode::Fact(first_span));
        assert_eq!(nodes[1], ResolvedTypeProvenanceNode::Fact(second_span));
        assert_eq!(nodes[2], ResolvedTypeProvenanceNode::Fact(constructor_span));
        assert_eq!(
            nodes[3],
            ResolvedTypeProvenanceNode::Application {
                span: full_span,
                function: 2,
                argument: 0,
                argument_span: first_span,
            }
        );
        assert_eq!(
            nodes[4],
            ResolvedTypeProvenanceNode::Application {
                span: full_span,
                function: 3,
                argument: 1,
                argument_span: second_span,
            }
        );
        crate::types::discard_type_iteratively(resolved.ty);
    }

    #[test]
    fn nominal_application_retention_is_exact_and_transactional_per_source_argument() {
        const ARGUMENTS: usize = 3;
        const EXACT_WORK: usize = 1 + 2 * ARGUMENTS;

        let source = SourceFile::new("application-retention.ash", "Triple<Int, Bool, Unit>")
            .expect("the retention fixture should fit");
        let span = |start, end| {
            source
                .span(ByteRange::new(start, end).expect("the range is ordered"))
                .expect("the range belongs to the fixture")
        };
        let full_span = span(0, 23);
        let constructor_span = span(0, 6);
        let owner = NominalTypeId::new(source.id(), 0);
        let annotation = SurfaceType {
            kind: SurfaceTypeKind::Application {
                constructor: SurfaceReference::Unqualified(SurfaceName {
                    text: "Triple".to_owned(),
                    span: constructor_span,
                }),
                arguments: vec![
                    SurfaceType {
                        kind: SurfaceTypeKind::Int,
                        span: span(7, 10),
                    },
                    SurfaceType {
                        kind: SurfaceTypeKind::Bool,
                        span: span(12, 16),
                    },
                    SurfaceType {
                        kind: SurfaceTypeKind::Unit,
                        span: span(18, 22),
                    },
                ],
            },
            span: full_span,
        };
        let resolver = |limit| {
            let mut resolver =
                Resolver::with_type_work(ModuleId::new(0), TypeWorkBudget::with_limit(limit));
            resolver.type_names.insert("Triple".to_owned(), owner);
            resolver.nominal_parameter_counts.insert(owner, ARGUMENTS);
            resolver
        };

        let mut short = resolver(EXACT_WORK - 1);
        let failure = short
            .resolve_type(&annotation)
            .expect_err("one missing fold-retention unit must reject the whole application");
        assert_eq!(failure.reason, ResolveReason::TypeResourceExhausted);
        assert_eq!(failure.primary.span(), full_span);
        assert_eq!(
            failure.primary.message(),
            "source type resolution exceeded its work budget"
        );
        assert_eq!(short.type_work.used(), 1 + ARGUMENTS);

        let mut exact = resolver(EXACT_WORK);
        let resolved = exact
            .resolve_type(&annotation)
            .expect("one retained unary node per source argument should fit exactly");
        assert_eq!(exact.type_work.used(), EXACT_WORK);
        assert_eq!(exact.type_work.charge(1), Err(()));
        assert_eq!(
            resolved
                .provenance
                .nodes()
                .iter()
                .filter(|node| matches!(node, ResolvedTypeProvenanceNode::Application { .. }))
                .count(),
            ARGUMENTS
        );
        crate::types::discard_type_iteratively(resolved.ty);
    }

    #[test]
    fn late_sibling_failure_discards_a_wide_application_on_a_small_stack() {
        const WIDTH: usize = 32_768;

        std::thread::Builder::new()
            .name("resolver-late-sibling-disposal".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("late-sibling.ash", "Wide<Int>, Missing")
                    .expect("the disposal fixture should fit");
                let span = |start, end| {
                    source
                        .span(ByteRange::new(start, end).expect("the range is ordered"))
                        .expect("the range belongs to the fixture")
                };
                let wide_span = span(0, 9);
                let constructor_span = span(0, 4);
                let argument_span = span(5, 8);
                let missing_span = span(11, 18);
                let owner = NominalTypeId::new(source.id(), 0);
                let annotation = SurfaceType {
                    kind: SurfaceTypeKind::Tuple(vec![
                        SurfaceType {
                            kind: SurfaceTypeKind::Application {
                                constructor: SurfaceReference::Unqualified(SurfaceName {
                                    text: "Wide".to_owned(),
                                    span: constructor_span,
                                }),
                                arguments: vec![
                                    SurfaceType {
                                        kind: SurfaceTypeKind::Int,
                                        span: argument_span,
                                    };
                                    WIDTH
                                ],
                            },
                            span: wide_span,
                        },
                        SurfaceType {
                            kind: SurfaceTypeKind::Named(SurfaceReference::Unqualified(
                                SurfaceName {
                                    text: "Missing".to_owned(),
                                    span: missing_span,
                                },
                            )),
                            span: missing_span,
                        },
                    ]),
                    span: span(0, 18),
                };
                let mut resolver = Resolver::new(ModuleId::new(0));
                resolver.type_names.insert("Wide".to_owned(), owner);
                resolver.nominal_parameter_counts.insert(owner, WIDTH);

                let error = resolver
                    .resolve_type(&annotation)
                    .expect_err("the later unknown sibling should reject resolution");
                assert_eq!(error.reason, ResolveReason::UnknownType);
                assert_eq!(error.primary.span(), missing_span);
            })
            .expect("the disposal thread should start")
            .join()
            .expect("late resolver failure should dispose completed types iteratively");
    }

    #[test]
    fn source_effect_row_rebuild_is_exact_retryable_and_stack_safe() {
        const DEPTH: usize = 16_384;
        std::thread::Builder::new()
            .name("source-effect-row-rebuild".to_owned())
            .stack_size(256 * 1024)
            .spawn(|| {
                let source = SourceFile::new("source-effect-row.ash", "{State<Int>}")
                    .expect("the row fixture should fit");
                let span = source
                    .span(ByteRange::new(0, 12).expect("the row range is ordered"))
                    .expect("the row span should fit");
                let effect = EffectId::new(ModuleId::new(41), 0);
                let fixture = |reverse| {
                    let nested = |leaf| {
                        let mut argument = leaf;
                        for _ in 0..DEPTH {
                            argument = Type::function(Type::Unit, argument);
                        }
                        argument
                    };
                    let integer = (
                        EffectInstance::new(effect, vec![nested(Type::Int)].into_boxed_slice()),
                        span,
                        vec![17].into_boxed_slice(),
                    );
                    let boolean = (
                        EffectInstance::new(effect, vec![nested(Type::Bool)].into_boxed_slice()),
                        span,
                        vec![29].into_boxed_slice(),
                    );
                    if reverse {
                        vec![boolean, integer]
                    } else {
                        vec![integer, boolean]
                    }
                };

                let mut measured = TypeWorkBudget::unbounded();
                let (row, roots) = build_source_effect_row_with_provenance(
                    fixture(false),
                    None,
                    span,
                    &mut measured,
                )
                .expect("the unbounded measurement should rebuild the row and provenance");
                let exact_work = measured.used();
                let expected_roots = roots.into_vec();
                drop(row);

                let mut one_short = TypeWorkBudget::with_limit(exact_work - 1);
                let failure = build_source_effect_row_with_provenance(
                    fixture(false),
                    None,
                    span,
                    &mut one_short,
                )
                .expect_err("one missing unit must publish no partial row or provenance");
                assert_eq!(failure.reason, ResolveReason::TypeResourceExhausted);

                let mut exact = TypeWorkBudget::with_limit(exact_work);
                let (row, roots) =
                    build_source_effect_row_with_provenance(fixture(true), None, span, &mut exact)
                        .expect(
                            "a fresh exact retry should publish the complete row and provenance",
                        );
                assert_eq!(exact.used(), exact_work);
                assert_eq!(row.known().len(), 2);
                assert_eq!(roots.as_ref(), expected_roots);
                drop(row);
            })
            .expect("the row owner test should start")
            .join()
            .expect("success, rejection, retry, and teardown should fit a small stack");
    }
}
