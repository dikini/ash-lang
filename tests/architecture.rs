use std::{
    cell::Cell,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fs,
    path::{Path, PathBuf},
};

use ash::{
    core::{
        AshPureDialect, CoreBuilder, NodeId, Primitive, PureComputation, PureExprKind, PureValue,
        TypedExpr, ValidatedProgram,
        binding::BindingNode,
        data::{ConstructorNode, MatchNode, TupleNode},
        function::{ApplicationNode, FunctionNode},
        literal::{BooleanNode, IntegerNode, UnitNode},
        primitive::PrimitiveNode,
        recursion::RecursiveBindingNode,
        type_ops::{TypeAbstractionNode, TypeApplicationNode},
        validate,
        variable::VariableNode,
    },
    integer::Integer,
    resolved::BinderId,
    source::{ByteRange, Origin, SourceFile},
    types::{Kind, Type},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum InventoryScope {
    Field,
    KindSite,
    Transient,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum KindEnvironmentOwner {
    Canonical,
    Surface,
    Resolved,
    Checked,
    Summary,
    Evidence,
    Registry,
    Core,
    Transient,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum KindRule {
    ProjectionOnly,
    ValueType,
    InterfaceArgument,
    Scheme,
    DeclaredKind,
    ApplicationStructure,
    KindStructure,
    CoreInstantiation,
    CarrierRetention,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RequiredKindResult {
    DeferredProjection,
    Value,
    InterfaceParameter,
    SchemeValue,
    Declared,
    StructuralSubtree,
    KindSubtree,
    InstantiationArgument,
    PreservedCarrier,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FailureOwner {
    Projection,
    ModuleStaging,
    Resolution,
    ResolvedKind,
    InterfaceValidation,
    EvidenceSelection,
    EvidenceValidation,
    Elaboration,
    CoreAdmission,
    CoreValidation,
    Evaluation,
    PipelineObservation,
    TypeOperation,
    PatternCoverage,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum BudgetOwner {
    Projection,
    ResolutionType,
    InterfaceType,
    EvidenceType,
    InferenceType,
    CoreType,
    Evaluation,
    PipelineType,
    Type,
    Kind,
    PatternCoverage,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DisposalOwner {
    TypeTree,
    KindTree,
    SurfaceTree,
    ResolvedTree,
    SummaryTree,
    CheckedTree,
    EvidenceTree,
    RegistryTree,
    CoreTree,
    EvaluatorState,
    TransientWork,
    Observation,
    CoreTreeAndRegistryTree,
    CoreTreeAndTransientWork,
    EvidenceTreeAndTransientWork,
    ResolvedTreeAndTransientWork,
    ResolvedTreeAndCheckedTree,
    TypeTreeAndKindTree,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum RetentionMode {
    Owned,
    Shared,
    Borrowed,
    Mixed,
}

macro_rules! define_kind_site_profiles {
    ($($name:ident => ($scope:ident, $retention:ident, $environment:ident, $rule:ident, $result:ident, $failure:ident, $budget:ident, $disposal:ident)),+ $(,)?) => {
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        enum ProfileId {
            $($name),+
        }

        const ALL_PROFILE_IDS: &[ProfileId] = &[$(ProfileId::$name),+];

        #[derive(Clone, Copy, Debug, Eq, PartialEq)]
        struct ExactProfile {
            id: ProfileId,
            retention: RetentionMode,
        }

        impl ProfileId {
            const fn exact(self) -> ExactProfile {
                let retention = match self {
                    $(Self::$name => RetentionMode::$retention),+
                };
                ExactProfile { id: self, retention }
            }

            const fn with_retention(self, retention: RetentionMode) -> ExactProfile {
                ExactProfile { id: self, retention }
            }
        }

        impl ExactProfile {
            const fn expand(self, key: &'static str, carrier: &'static str) -> KindSite {
                let (scope, environment, rule, required_result, failure_owner, budget, disposal_owner) = match self.id {
                    $(ProfileId::$name => (
                        InventoryScope::$scope,
                        KindEnvironmentOwner::$environment,
                        KindRule::$rule,
                        RequiredKindResult::$result,
                        FailureOwner::$failure,
                        BudgetOwner::$budget,
                        DisposalOwner::$disposal,
                    )),+
                };
                KindSite {
                    key,
                    carrier,
                    profile: Some(self),
                    scope,
                    retention: self.retention,
                    environment,
                    rule,
                    required_result,
                    failure_owner,
                    budget,
                    disposal_owner,
                }
            }
        }
    };
}

define_kind_site_profiles! {
    FieldMixedCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTreeAndRegistryTree => (Field, Mixed, Core, CarrierRetention, PreservedCarrier, CoreAdmission, CoreType, CoreTreeAndRegistryTree),
    FieldMixedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTreeAndTransientWork => (Field, Mixed, Transient, CarrierRetention, PreservedCarrier, CoreValidation, CoreType, CoreTreeAndTransientWork),
    FieldMixedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTreeAndTransientWork => (Field, Mixed, Transient, CarrierRetention, PreservedCarrier, Elaboration, InferenceType, ResolvedTreeAndTransientWork),
    FieldMixedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTreeAndTransientWork => (Field, Mixed, Transient, CarrierRetention, PreservedCarrier, EvidenceSelection, EvidenceType, EvidenceTreeAndTransientWork),
    FieldMixedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeCoreTreeAndRegistryTree => (Field, Mixed, Transient, CarrierRetention, PreservedCarrier, Elaboration, InferenceType, CoreTreeAndRegistryTree),
    FieldMixedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeEvidenceTreeAndTransientWork => (Field, Mixed, Transient, CarrierRetention, PreservedCarrier, Elaboration, InferenceType, EvidenceTreeAndTransientWork),
    FieldBorrowedEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree => (Field, Borrowed, Evidence, CarrierRetention, PreservedCarrier, EvidenceSelection, EvidenceType, EvidenceTree),
    FieldBorrowedEvidenceDeclaredKindDeclaredEvidenceSelectionEvidenceTypeEvidenceTree => (Field, Borrowed, Evidence, DeclaredKind, Declared, EvidenceSelection, EvidenceType, EvidenceTree),
    FieldBorrowedEvidenceValueTypeValueEvidenceSelectionEvidenceTypeEvidenceTree => (Field, Borrowed, Evidence, ValueType, Value, EvidenceSelection, EvidenceType, EvidenceTree),
    FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree => (Field, Borrowed, Resolved, CarrierRetention, PreservedCarrier, Elaboration, InferenceType, ResolvedTree),
    FieldSharedEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree => (Field, Shared, Evidence, CarrierRetention, PreservedCarrier, EvidenceSelection, EvidenceType, EvidenceTree),
    FieldSharedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree => (Field, Shared, Transient, CarrierRetention, PreservedCarrier, EvidenceSelection, EvidenceType, EvidenceTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, CoreAdmission, CoreType, CoreTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, CoreValidation, CoreType, CoreTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, Elaboration, InferenceType, TypeTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeKindTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, Elaboration, InferenceType, KindTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTypeTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, EvidenceSelection, EvidenceType, TypeTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeResolvedTreeAndCheckedTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, EvidenceSelection, EvidenceType, ResolvedTreeAndCheckedTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeTypeTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, EvidenceValidation, EvidenceType, TypeTree),
    FieldBorrowedTransientInterfaceArgumentInterfaceParameterEvidenceSelectionEvidenceTypeTypeTree => (Field, Borrowed, Transient, InterfaceArgument, InterfaceParameter, EvidenceSelection, EvidenceType, TypeTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, InterfaceValidation, InterfaceType, CheckedTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeTypeTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, InterfaceValidation, InterfaceType, TypeTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, Resolution, ResolutionType, SummaryTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, Resolution, ResolutionType, SurfaceTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierPatternCoveragePatternCoverageTypeTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, PatternCoverage, PatternCoverage, TypeTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierPatternCoveragePatternCoverageCoreTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, PatternCoverage, PatternCoverage, CoreTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, TypeOperation, Type, TypeTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeRegistryTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, TypeOperation, Type, RegistryTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, TypeOperation, Kind, KindTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, ResolvedKind, ResolutionType, KindTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeResolvedTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, ResolvedKind, ResolutionType, ResolvedTree),
    FieldCanonicalApplicationStructureStructuralSubtreeTypeOperationTypeTypeTree => (Field, Owned, Canonical, ApplicationStructure, StructuralSubtree, TypeOperation, Type, TypeTree),
    FieldCanonicalKindStructureKindSubtreeTypeOperationKindKindTree => (Field, Owned, Canonical, KindStructure, KindSubtree, TypeOperation, Kind, KindTree),
    FieldCanonicalSchemeSchemeValueTypeOperationTypeTypeTree => (Field, Owned, Canonical, Scheme, SchemeValue, TypeOperation, Type, TypeTree),
    FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree => (Field, Owned, Checked, CarrierRetention, PreservedCarrier, Elaboration, InferenceType, CheckedTree),
    FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree => (Field, Owned, Checked, CarrierRetention, PreservedCarrier, InterfaceValidation, InterfaceType, CheckedTree),
    FieldCheckedDeclaredKindDeclaredInterfaceValidationInterfaceTypeCheckedTree => (Field, Owned, Checked, DeclaredKind, Declared, InterfaceValidation, InterfaceType, CheckedTree),
    FieldCheckedInterfaceArgumentInterfaceParameterInterfaceValidationInterfaceTypeCheckedTree => (Field, Owned, Checked, InterfaceArgument, InterfaceParameter, InterfaceValidation, InterfaceType, CheckedTree),
    FieldCheckedSchemeSchemeValueInterfaceValidationInterfaceTypeCheckedTree => (Field, Owned, Checked, Scheme, SchemeValue, InterfaceValidation, InterfaceType, CheckedTree),
    FieldCheckedValueTypeValueInterfaceValidationInterfaceTypeCheckedTree => (Field, Owned, Checked, ValueType, Value, InterfaceValidation, InterfaceType, CheckedTree),
    FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree => (Field, Owned, Core, CarrierRetention, PreservedCarrier, CoreAdmission, CoreType, CoreTree),
    FieldCoreCoreInstantiationInstantiationArgumentCoreAdmissionCoreTypeCoreTree => (Field, Owned, Core, CoreInstantiation, InstantiationArgument, CoreAdmission, CoreType, CoreTree),
    FieldCoreValueTypeValueCoreAdmissionCoreTypeCoreTree => (Field, Owned, Core, ValueType, Value, CoreAdmission, CoreType, CoreTree),
    FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree => (Field, Owned, Evidence, CarrierRetention, PreservedCarrier, EvidenceSelection, EvidenceType, EvidenceTree),
    FieldEvidenceCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeEvidenceTree => (Field, Owned, Evidence, CarrierRetention, PreservedCarrier, EvidenceValidation, EvidenceType, EvidenceTree),
    FieldEvidenceDeclaredKindDeclaredEvidenceSelectionEvidenceTypeEvidenceTree => (Field, Owned, Evidence, DeclaredKind, Declared, EvidenceSelection, EvidenceType, EvidenceTree),
    FieldEvidenceInterfaceArgumentInterfaceParameterEvidenceSelectionEvidenceTypeEvidenceTree => (Field, Owned, Evidence, InterfaceArgument, InterfaceParameter, EvidenceSelection, EvidenceType, EvidenceTree),
    FieldEvidenceSchemeSchemeValueEvidenceSelectionEvidenceTypeEvidenceTree => (Field, Owned, Evidence, Scheme, SchemeValue, EvidenceSelection, EvidenceType, EvidenceTree),
    FieldEvidenceValueTypeValueEvidenceSelectionEvidenceTypeEvidenceTree => (Field, Owned, Evidence, ValueType, Value, EvidenceSelection, EvidenceType, EvidenceTree),
    FieldRegistryCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeRegistryTree => (Field, Owned, Registry, CarrierRetention, PreservedCarrier, CoreAdmission, CoreType, RegistryTree),
    FieldRegistryCarrierRetentionPreservedCarrierElaborationInferenceTypeRegistryTree => (Field, Owned, Registry, CarrierRetention, PreservedCarrier, Elaboration, InferenceType, RegistryTree),
    FieldRegistryCarrierRetentionPreservedCarrierEvaluationEvaluationRegistryTree => (Field, Owned, Registry, CarrierRetention, PreservedCarrier, Evaluation, Evaluation, RegistryTree),
    FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree => (Field, Owned, Registry, CarrierRetention, PreservedCarrier, Resolution, ResolutionType, RegistryTree),
    FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree => (Field, Owned, Resolved, CarrierRetention, PreservedCarrier, Resolution, ResolutionType, ResolvedTree),
    FieldResolvedDeclaredKindDeclaredResolutionResolutionTypeResolvedTree => (Field, Owned, Resolved, DeclaredKind, Declared, Resolution, ResolutionType, ResolvedTree),
    FieldResolvedInterfaceArgumentInterfaceParameterResolutionResolutionTypeResolvedTree => (Field, Owned, Resolved, InterfaceArgument, InterfaceParameter, Resolution, ResolutionType, ResolvedTree),
    FieldResolvedValueTypeValueResolutionResolutionTypeResolvedTree => (Field, Owned, Resolved, ValueType, Value, Resolution, ResolutionType, ResolvedTree),
    FieldSummaryCarrierRetentionPreservedCarrierElaborationInferenceTypeSummaryTree => (Field, Owned, Summary, CarrierRetention, PreservedCarrier, Elaboration, InferenceType, SummaryTree),
    FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree => (Field, Owned, Summary, CarrierRetention, PreservedCarrier, Resolution, ResolutionType, SummaryTree),
    FieldSummarySchemeSchemeValueResolutionResolutionTypeSummaryTree => (Field, Owned, Summary, Scheme, SchemeValue, Resolution, ResolutionType, SummaryTree),
    FieldSummaryValueTypeValueResolutionResolutionTypeSummaryTree => (Field, Owned, Summary, ValueType, Value, Resolution, ResolutionType, SummaryTree),
    FieldSurfaceCarrierRetentionPreservedCarrierModuleStagingProjectionSurfaceTree => (Field, Owned, Surface, CarrierRetention, PreservedCarrier, ModuleStaging, Projection, SurfaceTree),
    FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree => (Field, Owned, Surface, CarrierRetention, PreservedCarrier, Projection, Projection, SurfaceTree),
    FieldSurfaceDeclaredKindDeclaredProjectionProjectionSurfaceTree => (Field, Owned, Surface, DeclaredKind, Declared, Projection, Projection, SurfaceTree),
    FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree => (Field, Owned, Surface, ProjectionOnly, DeferredProjection, Projection, Projection, SurfaceTree),
    FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork => (Field, Owned, Transient, CarrierRetention, PreservedCarrier, CoreAdmission, CoreType, TransientWork),
    FieldTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeTransientWork => (Field, Owned, Transient, CarrierRetention, PreservedCarrier, CoreValidation, CoreType, TransientWork),
    FieldTransientCarrierRetentionPreservedCarrierElaborationCoreTypeTransientWork => (Field, Owned, Transient, CarrierRetention, PreservedCarrier, Elaboration, CoreType, TransientWork),
    FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork => (Field, Owned, Transient, CarrierRetention, PreservedCarrier, Elaboration, InferenceType, TransientWork),
    FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState => (Field, Owned, Transient, CarrierRetention, PreservedCarrier, Evaluation, Evaluation, EvaluatorState),
    FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationTransientWork => (Field, Owned, Transient, CarrierRetention, PreservedCarrier, Evaluation, Evaluation, TransientWork),
    FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork => (Field, Owned, Transient, CarrierRetention, PreservedCarrier, EvidenceSelection, EvidenceType, TransientWork),
    FieldTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeTransientWork => (Field, Owned, Transient, CarrierRetention, PreservedCarrier, EvidenceValidation, EvidenceType, TransientWork),
    FieldTransientCarrierRetentionPreservedCarrierPipelineObservationPipelineTypeObservation => (Field, Owned, Transient, CarrierRetention, PreservedCarrier, PipelineObservation, PipelineType, Observation),
    FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork => (Field, Owned, Transient, CarrierRetention, PreservedCarrier, Resolution, ResolutionType, TransientWork),
    FieldTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree => (Field, Owned, Transient, CarrierRetention, PreservedCarrier, ResolvedKind, ResolutionType, KindTree),
    FieldTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeResolvedTree => (Field, Owned, Transient, CarrierRetention, PreservedCarrier, ResolvedKind, ResolutionType, ResolvedTree),
    FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork => (Field, Owned, Transient, CarrierRetention, PreservedCarrier, TypeOperation, Type, TransientWork),
    FieldTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree => (Field, Owned, Transient, CarrierRetention, PreservedCarrier, TypeOperation, Kind, KindTree),
    FieldTransientDeclaredKindDeclaredElaborationInferenceTypeTransientWork => (Field, Owned, Transient, DeclaredKind, Declared, Elaboration, InferenceType, TransientWork),
    FieldTransientDeclaredKindDeclaredElaborationInferenceTypeKindTree => (Field, Owned, Transient, DeclaredKind, Declared, Elaboration, InferenceType, KindTree),
    FieldTransientCarrierRetentionPreservedCarrierPatternCoveragePatternCoverageTransientWork => (Field, Owned, Transient, CarrierRetention, PreservedCarrier, PatternCoverage, PatternCoverage, TransientWork),
    FieldSharedTransientCarrierRetentionPreservedCarrierPatternCoveragePatternCoverageTransientWork => (Field, Shared, Transient, CarrierRetention, PreservedCarrier, PatternCoverage, PatternCoverage, TransientWork),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationInterfaceTypeTypeTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, TypeOperation, InterfaceType, TypeTree),
    FieldTransientInterfaceArgumentInterfaceParameterEvidenceValidationEvidenceTypeTransientWork => (Field, Owned, Transient, InterfaceArgument, InterfaceParameter, EvidenceValidation, EvidenceType, TransientWork),
    FieldTransientInterfaceArgumentInterfaceParameterEvidenceSelectionEvidenceTypeTransientWork => (Field, Owned, Transient, InterfaceArgument, InterfaceParameter, EvidenceSelection, EvidenceType, TransientWork),
    FieldTransientSchemeSchemeValueElaborationInferenceTypeTransientWork => (Field, Owned, Transient, Scheme, SchemeValue, Elaboration, InferenceType, TransientWork),
    FieldTransientValueTypeValueCoreAdmissionCoreTypeTransientWork => (Field, Owned, Transient, ValueType, Value, CoreAdmission, CoreType, TransientWork),
    FieldTransientValueTypeValueElaborationInferenceTypeTransientWork => (Field, Owned, Transient, ValueType, Value, Elaboration, InferenceType, TransientWork),
    FieldTransientValueTypeValuePipelineObservationPipelineTypeObservation => (Field, Owned, Transient, ValueType, Value, PipelineObservation, PipelineType, Observation),
    KindSiteCoreSchemeSchemeValueCoreAdmissionCoreTypeCoreTree => (KindSite, Owned, Core, Scheme, SchemeValue, CoreAdmission, CoreType, CoreTree),
    KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree => (KindSite, Owned, Core, ValueType, Value, CoreAdmission, CoreType, CoreTree),
    KindSiteResolvedInterfaceArgumentInterfaceParameterResolutionResolutionTypeResolvedTree => (KindSite, Owned, Resolved, InterfaceArgument, InterfaceParameter, Resolution, ResolutionType, ResolvedTree),
    KindSiteResolvedValueTypeValueResolutionResolutionTypeResolvedTree => (KindSite, Owned, Resolved, ValueType, Value, Resolution, ResolutionType, ResolvedTree),
    KindSiteBorrowedTransientInterfaceArgumentInterfaceParameterInterfaceValidationInterfaceTypeTypeTree => (KindSite, Borrowed, Transient, InterfaceArgument, InterfaceParameter, InterfaceValidation, InterfaceType, TypeTree),
    KindSiteBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree => (KindSite, Borrowed, Transient, CarrierRetention, PreservedCarrier, ResolvedKind, ResolutionType, KindTree),
    KindSiteBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeKindTree => (KindSite, Borrowed, Transient, CarrierRetention, PreservedCarrier, Elaboration, InferenceType, KindTree),
    KindSiteBorrowedTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeKindTree => (KindSite, Borrowed, Transient, CarrierRetention, PreservedCarrier, EvidenceValidation, EvidenceType, KindTree),
    KindSiteTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree => (KindSite, Owned, Transient, CarrierRetention, PreservedCarrier, ResolvedKind, ResolutionType, KindTree),
    KindSiteTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeKindTree => (KindSite, Owned, Transient, CarrierRetention, PreservedCarrier, Elaboration, InferenceType, KindTree),
    KindSiteTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeKindTree => (KindSite, Owned, Transient, CarrierRetention, PreservedCarrier, EvidenceValidation, EvidenceType, KindTree),
    KindSiteTransientSchemeSchemeValueElaborationInferenceTypeTransientWork => (KindSite, Owned, Transient, Scheme, SchemeValue, Elaboration, InferenceType, TransientWork),
    KindSiteTransientValueTypeValueElaborationInferenceTypeTransientWork => (KindSite, Owned, Transient, ValueType, Value, Elaboration, InferenceType, TransientWork),
    TransientResolvedApplicationStructureStructuralSubtreeResolutionResolutionTypeResolvedTree => (Transient, Owned, Resolved, ApplicationStructure, StructuralSubtree, Resolution, ResolutionType, ResolvedTree),
    TransientTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork => (Transient, Owned, Transient, CarrierRetention, PreservedCarrier, CoreAdmission, CoreType, TransientWork),
    TransientTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeTransientWork => (Transient, Owned, Transient, CarrierRetention, PreservedCarrier, CoreValidation, CoreType, TransientWork),
    TransientTransientCarrierRetentionPreservedCarrierElaborationCoreTypeTransientWork => (Transient, Owned, Transient, CarrierRetention, PreservedCarrier, Elaboration, CoreType, TransientWork),
    TransientTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork => (Transient, Owned, Transient, CarrierRetention, PreservedCarrier, Elaboration, InferenceType, TransientWork),
    TransientTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState => (Transient, Owned, Transient, CarrierRetention, PreservedCarrier, Evaluation, Evaluation, EvaluatorState),
    TransientTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork => (Transient, Owned, Transient, CarrierRetention, PreservedCarrier, EvidenceSelection, EvidenceType, TransientWork),
    TransientTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork => (Transient, Owned, Transient, CarrierRetention, PreservedCarrier, Resolution, ResolutionType, TransientWork),
    TransientBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree => (Transient, Borrowed, Transient, CarrierRetention, PreservedCarrier, TypeOperation, Kind, KindTree),
    TransientBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTreeAndKindTree => (Transient, Borrowed, Transient, CarrierRetention, PreservedCarrier, TypeOperation, Type, TypeTreeAndKindTree),
    TransientBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeResolvedTree => (Transient, Borrowed, Transient, CarrierRetention, PreservedCarrier, ResolvedKind, ResolutionType, ResolvedTree),
    TransientTransientCarrierRetentionPreservedCarrierTypeOperationKindTransientWork => (Transient, Owned, Transient, CarrierRetention, PreservedCarrier, TypeOperation, Kind, TransientWork),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct KindSite {
    key: &'static str,
    carrier: &'static str,
    profile: Option<ExactProfile>,
    scope: InventoryScope,
    retention: RetentionMode,
    environment: KindEnvironmentOwner,
    rule: KindRule,
    required_result: RequiredKindResult,
    failure_owner: FailureOwner,
    budget: BudgetOwner,
    disposal_owner: DisposalOwner,
}

macro_rules! kind_site {
    ($key:literal, $profile:ident) => {
        ProfileId::$profile.exact().expand($key, $key)
    };
    ($key:literal, $profile:ident, $retention:ident) => {
        ProfileId::$profile
            .with_retention(RetentionMode::$retention)
            .expand($key, $key)
    };
}

macro_rules! kind_site_for {
    ($key:literal, $carrier:literal, $profile:ident) => {
        ProfileId::$profile.exact().expand($key, $carrier)
    };
    ($key:literal, $carrier:literal, $profile:ident, $retention:ident) => {
        ProfileId::$profile
            .with_retention(RetentionMode::$retention)
            .expand($key, $carrier)
    };
}

const TASK_4_PHASE_CONSTRAINT: &str = "kind inference is intentionally absent only for this phase; declaration, transient inference, interface, and nominal kind entries remain fixed throughout the explicit-kinds increment";

#[rustfmt::skip]
const KIND_SITES: &[KindSite] = &[
    kind_site!("src/driver.rs::PipelineFailure.Kind.0", FieldTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_with_ledger::Continuation.ApplicationArgument.function", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_with_ledger::Continuation.ApplicationFunction.argument", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_with_ledger::Continuation.ApplicationFunction.argument_mirror", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_with_ledger::Continuation.FunctionDomain.codomain", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_with_ledger::Continuation.FunctionDomain.codomain_mirror", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_with_ledger::Continuation.Tuple.remaining", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_with_ledger::Continuation.Tuple.remaining_mirrors", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_with_ledger::State.Complete.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_with_ledger::State.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_with_ledger::State.Visit.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::BodyWork.Declaration.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeResolvedTree),
    kind_site!("src/kind.rs::BodyWork.Expression.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeResolvedTree),
    kind_site!("src/kind.rs::BodyWork.RecursiveMember.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeResolvedTree),
    kind_site!("src/kind.rs::InterfaceKindFact.kind", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site!("src/kind.rs::KindEnvironments.delta", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::KindEnvironments.iota", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site!("src/kind.rs::KindEnvironments.omega", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeKindTree),
    kind_site!("src/kind.rs::KindEnvironments.xi", FieldTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::KindError.expectation", FieldTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site!("src/kind.rs::KindError.found", FieldTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site!("src/kind.rs::KindExpectation.Exact.0", FieldTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site!("src/kind.rs::KindExpectation.Function.domain", FieldTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site!("src/kind.rs::KindFact.kind", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::KindFact.retained_mirrors", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::KindFailure.Source.0", FieldTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site!("src/kind.rs::NominalKindFact.kind", FieldTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::RetainedKindMirrors.Two.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::RetainedKindMirrors.Two.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/resolve.rs::ResolveModuleError.Kind.0", FieldTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site!("src/resolve.rs::ResolvedModuleAdmission.parts", FieldTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeResolvedTree, Mixed),
    kind_site!("src/core/binding.rs::BindingNode.binder", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/data.rs::$impl_CorePattern::$fn_discard_iteratively::Task.Sequence.0", FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/data.rs::$impl_CorePattern::$fn_discard_iteratively::Task.Visit.0", FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/data.rs::BinderTraversalTask.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/data.rs::BinderTraversalTask.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/data.rs::CoreMatchArm.pattern", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/data.rs::CorePattern.kind", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/data.rs::CorePattern.ty", FieldCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/data.rs::CorePatternBinderIter.work", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/data.rs::CorePatternKind.Binder.0", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/data.rs::CorePatternKind.Constructor.payload", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/data.rs::CorePatternKind.Tuple.0", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/data.rs::MatchNode.arms", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::CoreBuilder.nodes", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::CoreBuilder.method_evidence", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree, Shared),
    kind_site!("src/core/dialect.rs::CoreBuilder.method_evidence_anchors", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::CoreBuilder.registry", FieldRegistryCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeRegistryTree, Shared),
    kind_site!("src/core/dialect.rs::MethodEvidenceAdapter.head_arguments", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceAdapter.prerequisites", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceAdapterEdge.interface_argument", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceAdapterEdge.method_parameters", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceAdapterEdge.value_type", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceAnchor.interface_argument", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceCatalog.adapters", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceCatalog.domains", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceCatalog.implementation_owners", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceCatalog.methods", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceCatalog.occurrences", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree, Mixed),
    kind_site!("src/core/dialect.rs::MethodEvidenceDomain.interface_argument", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceImplementationOwner.interface_argument", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceImplementationOwner.source_parameters", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceMethod.parameters", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceMethod.value_type", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceOccurrence.checked_argument", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceOccurrence.checked_value_type", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceOccurrence.method_arguments", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceOccurrence.selection", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree, Shared),
    kind_site!("src/core/dialect.rs::PatternAdmissionTask.FinishConstructor.ty", FieldTransientValueTypeValueCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/dialect.rs::PatternAdmissionTask.FinishTuple.ty", FieldTransientValueTypeValueCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/dialect.rs::PatternAdmissionTask.Visit.0", FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/dialect.rs::PatternAdmissionTask.VisitSequence.0", FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/dialect.rs::PatternToken.Binder.0", FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/dialect.rs::PatternToken.Binder.2", FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/dialect.rs::PatternToken.Boolean.0", FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/dialect.rs::PatternToken.Constructor.0", FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/dialect.rs::PatternToken.Tuple.0", FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/dialect.rs::PatternToken.Unit.0", FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/dialect.rs::PatternToken.Wildcard.0", FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/dialect.rs::PureComputation.Bind.0", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::PureComputation.Match.0", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::PureComputation.RecursiveBind.0", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::PureComputation.TypeAbstraction.0", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::PureComputation.TypeApplication.0", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::PureExprKind.Computation.0", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::PureExprKind.Value.0", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::PureProgram.nodes", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::PureProgram.method_evidence", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree, Shared),
    kind_site!("src/core/dialect.rs::PureProgram.method_evidence_anchors", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::PureProgram.registry", FieldRegistryCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeRegistryTree, Shared),
    kind_site!("src/core/dialect.rs::PureValue.Function.0", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::StoredNode.kind", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::StoredNode.ty", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::TypeAdmissionTask.FinishForall.0", FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/dialect.rs::TypeAdmissionTask.Visit.0", FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/dialect.rs::TypeAdmissionTask.VisitSequence.0", FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/dialect.rs::TypeToken.Forall.0", FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/dialect.rs::TypedExpr.kind", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::TypedExpr.ty", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::UnvalidatedParts.$alias", FieldMixedCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTreeAndRegistryTree),
    kind_site!("src/core/dialect.rs::UnvalidatedProgram.nodes", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::UnvalidatedProgram.method_evidence", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree, Shared),
    kind_site!("src/core/dialect.rs::UnvalidatedProgram.method_evidence_anchors", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::UnvalidatedProgram.registry", FieldRegistryCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeRegistryTree, Shared),
    kind_site!("src/core/dialect.rs::ValidatedProgram.0", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree, Shared),
    kind_site!("src/core/function.rs::FunctionNode.parameter", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::CoreBuilder.$alias", FieldMixedCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTreeAndRegistryTree),
    kind_site!("src/core/mod.rs::CoreMatchArm.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::CorePattern.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::CorePatternKind.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::MatchNode.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::PureComputation.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::PureExprKind.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::PureProgram.$alias", FieldMixedCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTreeAndRegistryTree),
    kind_site!("src/core/mod.rs::PureValue.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::RecursiveBindingMember.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::RecursiveBindingNode.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::TypeAbstractionNode.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::TypeApplicationNode.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::TypedBinder.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::TypedExpr.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::UnvalidatedProgram.$alias", FieldMixedCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTreeAndRegistryTree),
    kind_site!("src/core/mod.rs::ValidatedProgram.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree, Shared),
    kind_site!("src/core/recursion.rs::RecursiveBindingMember.binder", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/recursion.rs::RecursiveBindingNode.members", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/type_ops.rs::TypeAbstractionNode.parameters", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/type_ops.rs::TypeApplicationNode.arguments", FieldCoreCoreInstantiationInstantiationArgumentCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/transform.rs::$fn_rebuild_pattern::Task.FinishConstructor.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/transform.rs::$fn_rebuild_pattern::Task.FinishTuple.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/transform.rs::$fn_rebuild_pattern::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/transform.rs::CorePatternBuffer.0", FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/transform.rs::CorePatternOwner.0", FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/transform.rs::IterativeTypeBuffer.0", FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_charge_pattern_type_structure::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_charge_pattern_type_structure::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_charge_type_structure::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_charge_type_structure::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_collect_free_type_variables::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_collect_free_type_variables::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_collect_pattern_type_variables::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_collect_pattern_type_variables::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_synthesize_monotype_kind::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_synthesize_monotype_kind::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_valid_registry_payload::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_valid_registry_payload::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_valid_type_with_scheme::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_valid_type_with_scheme::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_validate_pattern::Expected.Borrowed.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_validate_pattern::Expected.Owned.0", FieldTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeTransientWork),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_validate_pattern::Task.BorrowedTupleSequence.patterns", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_validate_pattern::Task.BorrowedTupleSequence.types", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_validate_pattern::Task.OwnedTupleSequence.patterns", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_validate_pattern::Task.OwnedTupleSequence.types", FieldTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeTransientWork),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_validate_pattern::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_validate_pattern::Task.Visit.1", FieldMixedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTreeAndTransientWork),
    kind_site!("src/core/validate.rs::CoreTypeBinders.$alias", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::MonotypeVariableKinds.Core.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::CorePatternMatrix.0", FieldTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeTransientWork),
    kind_site!("src/core/validate.rs::CorePatternRow.0", FieldTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeTransientWork),
    kind_site!("src/core/validate.rs::OwnedTypeSequence.0", FieldTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeTransientWork),
    kind_site!("src/core/validate.rs::TypeReplacementMap.0", FieldTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeTransientWork),
    kind_site!("src/core/validate.rs::Validator.binders", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::Validator.program", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/variable.rs::TypedBinder.ty", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/driver.rs::FileFailure.Pipeline.0", FieldTransientCarrierRetentionPreservedCarrierPipelineObservationPipelineTypeObservation),
    kind_site!("src/driver.rs::Observation._heap", FieldTransientCarrierRetentionPreservedCarrierPipelineObservationPipelineTypeObservation, Shared),
    kind_site!("src/driver.rs::Observation.ty", FieldTransientValueTypeValuePipelineObservationPipelineTypeObservation),
    kind_site!("src/driver.rs::Observation.value", FieldTransientCarrierRetentionPreservedCarrierPipelineObservationPipelineTypeObservation, Shared),
    kind_site!("src/driver.rs::ObservationParts.ty", FieldTransientValueTypeValuePipelineObservationPipelineTypeObservation),
    kind_site!("src/driver.rs::ObservationParts.value", FieldTransientCarrierRetentionPreservedCarrierPipelineObservationPipelineTypeObservation, Shared),
    kind_site!("src/driver.rs::ObservationValue._heap", FieldTransientCarrierRetentionPreservedCarrierPipelineObservationPipelineTypeObservation, Shared),
    kind_site!("src/driver.rs::ObservationValue.value", FieldTransientCarrierRetentionPreservedCarrierPipelineObservationPipelineTypeObservation, Shared),
    kind_site!("src/driver.rs::PipelineFailure.Typing.0", FieldTransientCarrierRetentionPreservedCarrierPipelineObservationPipelineTypeObservation),
    kind_site!("src/elaborate.rs::$fn_collect_unsolved_inference::Task.Slice.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_collect_unsolved_inference::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_compare_concrete_types::Task.Pair.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_compare_concrete_types::Task.Pair.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_compare_concrete_types::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_compare_concrete_types::Task.Sequence.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_type_contains_inference::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_type_contains_inference::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$impl_Elaborator::$fn_unify::Task.Pair.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$impl_Elaborator::$fn_unify::Task.Pair.1", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$impl_Elaborator::$fn_unify::Task.Sequence.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$impl_Elaborator::$fn_unify::Task.Sequence.1", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$impl_Elaborator::$fn_unify::Work.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$fn_validate_and_charge_public_monotype::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_validate_and_charge_public_monotype::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_zonk_type::Task.FinishForall.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$fn_zonk_type::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_zonk_type::Task.VisitSequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_zonk_type_with_status_and_inference::ChargeTask.Slice.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_zonk_type_with_status_and_inference::ChargeTask.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::ActiveEvidenceBinder.ty", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ActiveEvidenceBinder.interface_argument", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CheckedBodyBuffers.definitions", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork, Mixed),
    kind_site!("src/elaborate.rs::CheckedBodyBuffers.implementations", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork, Mixed),
    kind_site!("src/elaborate.rs::CheckedImplementationFactBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CheckedInterfaceMethodRef.Imported.0", FieldSummaryCarrierRetentionPreservedCarrierElaborationInferenceTypeSummaryTree, Borrowed),
    kind_site!("src/elaborate.rs::CheckedInterfaceMethodRef.Local.0", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::CheckedInterfaceRef.Imported.0", FieldSummaryCarrierRetentionPreservedCarrierElaborationInferenceTypeSummaryTree, Borrowed),
    kind_site!("src/elaborate.rs::CheckedInterfaceRef.Local.0", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::CheckedPattern.pattern", FieldTransientCarrierRetentionPreservedCarrierElaborationCoreTypeTransientWork),
    kind_site!("src/elaborate.rs::CheckedSchemeBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CoreRecursiveMemberBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CorePatternBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CorePatternMatrixBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CorePatternOwner.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CorePatternRowSequence.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CurrentImplementationMethod.method_arguments", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaboratedBinding.binder", FieldTransientCarrierRetentionPreservedCarrierElaborationCoreTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaboratedBindingBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaboratedDeclaration.Binding.binder", FieldTransientCarrierRetentionPreservedCarrierElaborationCoreTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaboratedDeclaration.PatternBinding.pattern", FieldTransientCarrierRetentionPreservedCarrierElaborationCoreTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaboratedDeclaration.Recursive.members", FieldTransientCarrierRetentionPreservedCarrierElaborationCoreTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaboratedDeclarationBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaboratedDeclarationOwner.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaboratedGroupBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.AfterApplicationFunction.argument", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::ElaborationTask.AfterLeft.right", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::ElaborationTask.AfterMatchScrutinee.expected", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.AfterMatchScrutinee.expression", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::ElaborationTask.AfterRight.left", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.BeginBinding.binding", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::ElaborationTask.BeginBinding.expected", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.BeginBinding.finish_expected", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.BeginRecursiveGroup.0", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::ElaborationTask.Check.expected", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.Check.expression", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::ElaborationTask.CheckBlock.block", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::ElaborationTask.CheckBlock.expected", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.CheckFunction.body", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::ElaborationTask.CheckFunction.codomain", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.CheckFunction.domain", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.CheckFunction.function_type", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.CheckRecursiveMember.0", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::ElaborationTask.FinishApplication.codomain", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.FinishApplication.function", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.FinishBinding.binding", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::ElaborationTask.FinishBinding.expected", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.FinishBlock.declarations", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::ElaborationTask.FinishCheck.expected", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.FinishFunction.binder", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.FinishFunction.domain", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.FinishFunction.pattern", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.FinishFunction.ty", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.FinishMatch.0", FieldMixedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTreeAndTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.FinishMatchArm.progress", FieldMixedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTreeAndTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.FinishMatchArm.row", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.FinishRecursiveGroup.group", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::ElaborationTask.Synthesize.expression", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::ElaborationTaskBuffer.0", FieldMixedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTreeAndTransientWork),
    kind_site!("src/elaborate.rs::Elaborator.base_context", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::Elaborator.current_implementation_method", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::Elaborator.builder", FieldMixedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeCoreTreeAndRegistryTree),
    kind_site!("src/elaborate.rs::Elaborator.evidence_lowering", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::Elaborator.generated_type_variables", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::Elaborator.inference_solutions", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::Elaborator.inference_variables", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::Elaborator.registry", FieldRegistryCarrierRetentionPreservedCarrierElaborationInferenceTypeRegistryTree, Shared),
    kind_site!("src/elaborate.rs::Elaborator.selection", FieldMixedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeEvidenceTreeAndTransientWork),
    kind_site!("src/elaborate.rs::EvidenceLowering.active_binders", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::EvidenceLowering.global_schemes", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::EvidenceLowering.implementation_methods", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::EvidenceLowering.interface_methods", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::EvidenceSpecificationBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::EvidenceSpecificationSequence.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::FunctionBody.Block.0", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::FunctionCheck.body", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::FunctionCheck.codomain", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::FunctionCheck.domain", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::FunctionCheck.function_type", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ImplementationHeadRef.Imported.0", FieldSummaryCarrierRetentionPreservedCarrierElaborationInferenceTypeSummaryTree, Borrowed),
    kind_site!("src/elaborate.rs::ImplementationHeadRef.Local.0", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::GeneratedTypeVariableFact.kind", FieldTransientDeclaredKindDeclaredElaborationInferenceTypeKindTree),
    kind_site!("src/elaborate.rs::GeneratedTypeVariableRegistry.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::InferenceSolutionMap.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::InferenceVariableFact.kind", FieldTransientDeclaredKindDeclaredElaborationInferenceTypeKindTree),
    kind_site!("src/elaborate.rs::InferenceVariableRegistry.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::KindedTypeParameters.$alias", FieldTransientDeclaredKindDeclaredElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredEvidenceMethod.ty", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredEvidenceMethod.adapter_interface_argument", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredImplementationMethod.interface_argument", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredImplementationMethod.scheme", FieldTransientSchemeSchemeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredInterfaceMethod.value_type", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredInterfaceMethod.type_parameters", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredRequirement.methods", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredRequirementMethod.ty", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredRequirementMethod.interface_argument", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredScheme.core_scheme", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredScheme.requirements", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredScheme.source_type_parameters", FieldTransientDeclaredKindDeclaredElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredScheme.type_parameters", FieldTransientDeclaredKindDeclaredElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredScheme.value_type", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::MatchProgress.expression", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::MatchProgress.matrix", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::MatchProgress.result_type", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::MatchProgress.scrutinee", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::MatchProgressOwner.0", FieldMixedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTreeAndTransientWork),
    kind_site!("src/elaborate.rs::ProvenancedTypeBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ProvenancedTypeOwner.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::OwnedTypeBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::PreparedGlobals.binders", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::PreparedGlobals.context", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::PreparedGlobals.globals", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::PreparedGlobals.quantifiers", FieldTransientDeclaredKindDeclaredElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ProvenancedType.ty", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ScopedEvidenceBinder.binder", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ScopedEvidenceBinder.interface_argument", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::TypeContext.binders", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::TypeError.Mismatch.0", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree),
    kind_site!("src/elaborate.rs::TypeFact.quantified", FieldTransientDeclaredKindDeclaredElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::TypeFact.ty", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::TypeFactOwner.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::TypeMismatch.expected", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::TypeMismatch.found", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::TypeReplacementBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::TypedNode.ty", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::TypedNodeOwner.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::TypedNodeBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/eval/machine.rs::Control.Evaluate.1", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Control.Return.0", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Environment.head", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::EnvironmentEntry.kind", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::EnvironmentEntry.parent", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::EnvironmentEntryKind.Binding.value", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Evaluation.heap", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Evaluation.value", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.ApplyArgument.function", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.ApplyFunction.caller_environment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.Bind.environment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.InitializeRecursive.environment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.Match.arms", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState),
    kind_site!("src/eval/machine.rs::Frame.Match.environment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.PrimitiveLeft.environment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.PrimitiveRight.left", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.Tuple.environment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.Tuple.values", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Machine.control", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Machine.frames", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Mixed),
    kind_site!("src/eval/machine.rs::Machine.heap", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Machine.program", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Transition.control", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Transition.frame", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Mixed),
    kind_site!("src/eval/mod.rs::Closure.$alias", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/mod.rs::Control.$alias", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/mod.rs::Environment.$alias", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/mod.rs::Evaluation.$alias", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/mod.rs::ObservedHeap.$alias", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/mod.rs::ObservedValue.$alias", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/mod.rs::Value.$alias", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/value.rs::$impl_ObservedValue::$fn_render::Task.Value.0", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationTransientWork, Shared),
    kind_site!("src/eval/value.rs::Closure.environment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/value.rs::Closure.program", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/value.rs::HeapCell.Constructor.1", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/value.rs::HeapCell.Tuple.0", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/value.rs::ObservedHeap.cells", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/value.rs::ObservedHeap.registry", FieldRegistryCarrierRetentionPreservedCarrierEvaluationEvaluationRegistryTree, Shared),
    kind_site!("src/eval/value.rs::ObservedValue.heap", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/value.rs::Value.Data.0", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/value.rs::Value.Function.0", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/evidence.rs::EvidenceSelector.abstracts", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::EvidenceSelector.implementations", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::EvidenceSelector.interfaces", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::EvidenceSelector.method_rigidities", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::EvidenceSelector.pending", FieldMixedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTreeAndTransientWork),
    kind_site!("src/evidence.rs::EvidenceSelector.selected", FieldMixedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTreeAndTransientWork),
    kind_site!("src/evidence.rs::EvidenceSelector.schemes", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::Goal.argument", FieldTransientInterfaceArgumentInterfaceParameterEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::ImplementationCandidateAuthentication.argument", FieldBorrowedTransientInterfaceArgumentInterfaceParameterEvidenceSelectionEvidenceTypeTypeTree),
    kind_site!("src/evidence.rs::ImplementationCandidateAuthentication.parameter_records", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeResolvedTreeAndCheckedTree),
    kind_site!("src/evidence.rs::ImplementationEntry.argument", FieldEvidenceInterfaceArgumentInterfaceParameterEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::ImplementationEntry.prerequisites", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::InterfaceEntry.parameter_kind", FieldEvidenceDeclaredKindDeclaredEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::InterfaceEntry.methods", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::MethodEntry.value_type", FieldEvidenceValueTypeValueEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::MethodEntry.type_parameters", FieldEvidenceDeclaredKindDeclaredEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::MethodObligationMetadata.method_arguments", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::MethodObligationMetadata.checked_value_type", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::MethodObligationMetadata.method_rigidity", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::MethodRigidityCheck.method_arguments", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTypeTree),
    kind_site!("src/evidence.rs::MethodRigidityCheck.rigid_arguments", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTypeTree),
    kind_site!("src/evidence.rs::MethodRigidityCondition.rigid_arguments", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::PendingEvidencePublication.occurrences", FieldMixedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTreeAndTransientWork),
    kind_site!("src/evidence.rs::PendingObligation.argument", FieldTransientInterfaceArgumentInterfaceParameterEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::PendingObligation.method_arguments", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::PendingObligation.checked_value_type", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::PendingObligation.method_rigidity", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::PendingObligation.slot", FieldSharedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::ReplacementMap.values", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::RequirementEntry.argument", FieldEvidenceInterfaceArgumentInterfaceParameterEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::SchemeEntry.scheme", FieldEvidenceSchemeSchemeValueEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::SelectedMethodRigidity.condition", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::SelectedOccurrence.checked_argument", FieldTransientInterfaceArgumentInterfaceParameterEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::SelectedOccurrence.checked_value_type", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::SelectedOccurrence.method_arguments", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::SelectedOccurrence.selection", FieldSharedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::SelectedOccurrence.slot", FieldSharedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::SelectionMethod.interface_parameter_kind", FieldBorrowedEvidenceDeclaredKindDeclaredEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::SelectionMethod.type_parameters", FieldBorrowedEvidenceDeclaredKindDeclaredEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::SelectionMethod.value_type", FieldBorrowedEvidenceValueTypeValueEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::SelectionSite.slot", FieldSharedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::SelectionTask.Finish.substitution", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::SelectionTask.Select.goal", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::SelectionWork.0", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence_validation.rs::PendingGoal.argument", FieldTransientInterfaceArgumentInterfaceParameterEvidenceValidationEvidenceTypeTransientWork),
    kind_site!("src/evidence_validation.rs::$fn_substitute_evidence_type::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeTypeTree),
    kind_site!("src/evidence_validation.rs::$fn_substitute_evidence_type::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeTypeTree),
    kind_site!("src/evidence_validation.rs::$fn_validate_type_with_application_policy::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeTypeTree),
    kind_site!("src/evidence_validation.rs::$fn_validate_type_with_application_policy::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeTypeTree),
    kind_site!("src/evidence_validation.rs::PendingGoals.0", FieldTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeTransientWork),
    kind_site!("src/evidence_validation.rs::TypeBuffer.0", FieldTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeTransientWork),
    kind_site!("src/evidence_validation.rs::ValidatedInterfaceProgram.source", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeEvidenceTree, Mixed),
    kind_site!("src/evidence_validation.rs::ValidatedInterfaceProgram.method_evidence", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeEvidenceTree, Shared),
    kind_site!("src/interface.rs::$impl_InterfaceConstraintBudget::$fn_charge_type::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationInterfaceTypeTypeTree),
    kind_site!("src/interface.rs::$impl_InterfaceConstraintBudget::$fn_charge_type::Task.Type.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationInterfaceTypeTypeTree),
    kind_site!("src/interface.rs::$impl_InterfaceConstraintBudget::$fn_charge_equal_types::Task.Compare.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationInterfaceTypeTypeTree),
    kind_site!("src/interface.rs::$impl_InterfaceConstraintBudget::$fn_charge_equal_types::Task.Compare.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationInterfaceTypeTypeTree),
    kind_site!("src/interface.rs::$impl_InterfaceConstraintBudget::$fn_charge_equal_types::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationInterfaceTypeTypeTree),
    kind_site!("src/interface.rs::$local.charge_equal_kinds.pending", TransientBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/interface.rs::CheckedRequirement.argument", FieldCheckedInterfaceArgumentInterfaceParameterInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/interface.rs::ConstrainedScheme.requirements", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/interface.rs::ConstrainedScheme.type_parameters", FieldCheckedDeclaredKindDeclaredInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/interface.rs::ConstrainedScheme.value_type", FieldCheckedValueTypeValueInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/interface.rs::EvidenceNode.Implementation.substitution", FieldBorrowedEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::EvidenceNodeData.Implementation.substitution", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::EvidencePlan.argument", FieldEvidenceInterfaceArgumentInterfaceParameterEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::EvidencePlan.nodes", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::EvidenceSelection.plan", FieldSharedEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::EvidenceSelectionBuilder.nodes", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/interface.rs::EvidenceSlot.filled", FieldSharedEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::EvidenceSlotHandle.filled", FieldSharedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::EvidenceSubstitution.argument", FieldEvidenceDeclaredKindDeclaredEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::FilledEvidenceSlot.checked_argument", FieldEvidenceInterfaceArgumentInterfaceParameterEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::FilledEvidenceSlot.checked_value_type", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::FilledEvidenceSlot.method_arguments", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::FilledEvidenceSlot.selection", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree, Shared),
    kind_site!("src/interface.rs::OverlapHead.ty", FieldBorrowedTransientCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeTypeTree),
    kind_site!("src/module.rs::LoadedModule.surface", FieldSurfaceCarrierRetentionPreservedCarrierModuleStagingProjectionSurfaceTree),
    kind_site!("src/module.rs::ModuleGraph.modules", FieldSurfaceCarrierRetentionPreservedCarrierModuleStagingProjectionSurfaceTree),
    kind_site!("src/module.rs::StagedModule.surface", FieldSurfaceCarrierRetentionPreservedCarrierModuleStagingProjectionSurfaceTree),
    kind_site!("src/parser/project.rs::ExpressionTask.FinishBlock.declarations", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/parser/project.rs::PendingBinding.annotation", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/parser/project.rs::PendingLocalDeclaration.Binding.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/parser/project.rs::PendingLocalDeclaration.Recursive.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/parser/project.rs::PendingRecursiveGroup.members", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/parser/project.rs::PendingRecursiveMember.annotation", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/pattern.rs::$fn_charge_types::Task.Slice.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierPatternCoveragePatternCoverageTypeTree),
    kind_site!("src/pattern.rs::$fn_charge_types::Task.Type.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierPatternCoveragePatternCoverageTypeTree),
    kind_site!("src/pattern.rs::$fn_shape::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierPatternCoveragePatternCoverageCoreTree),
    kind_site!("src/pattern.rs::Choice.child", FieldSharedTransientCarrierRetentionPreservedCarrierPatternCoveragePatternCoverageTransientWork),
    kind_site!("src/pattern.rs::Frame.Call.0", FieldSharedTransientCarrierRetentionPreservedCarrierPatternCoveragePatternCoverageTransientWork),
    kind_site!("src/pattern.rs::Frame.TryChoices.choices", FieldSharedTransientCarrierRetentionPreservedCarrierPatternCoveragePatternCoverageTransientWork),
    kind_site!("src/pattern.rs::Frame.TryChoices.state", FieldSharedTransientCarrierRetentionPreservedCarrierPatternCoveragePatternCoverageTransientWork),
    kind_site!("src/pattern.rs::OwnedTypeBuffer.0", FieldTransientCarrierRetentionPreservedCarrierPatternCoveragePatternCoverageTransientWork),
    kind_site!("src/pattern.rs::State.2", FieldTransientCarrierRetentionPreservedCarrierPatternCoveragePatternCoverageTransientWork),
    kind_site!("src/pattern.rs::TypeReplacementMap.0", FieldTransientCarrierRetentionPreservedCarrierPatternCoveragePatternCoverageTransientWork),
    kind_site!("src/resolve.rs::$fn_collect_free_type_names::Task.Slice.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::$fn_collect_free_type_names::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::$fn_surface_kind_to_kind::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::$impl_Resolver::$fn_clone_imported_payload_with_budget::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolve.rs::$impl_Resolver::$fn_clone_imported_payload_with_budget::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolve.rs::$impl_Resolver::$fn_resolve_type::Task.Application.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::$impl_Resolver::$fn_resolve_type::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::$impl_Resolver::$fn_resolve_type::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::$impl_Resolver::$fn_retain_type_nominals::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolve.rs::$impl_Resolver::$fn_retain_type_nominals::Task.Type.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolve.rs::DependencyExports.summary", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree, Borrowed),
    kind_site!("src/resolve.rs::ImportedConstructorFactBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ImportedTypeCloneBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ImportedTypeVariableBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::PendingInterfaceTypeParameters.methods", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::PendingInterfaceTypeParameters.parameter", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::PendingImplementation.head_parameters", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::PendingImplementation.prerequisite_only_parameters", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ResolveTaskBuffer.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::ResolvedConstructorOwnerBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ResolvedDeclarationBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ResolvedDefinitionBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ResolvedEquationBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ResolvedExpressionBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ResolvedExpressionOwner.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ResolvedImplementationBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ResolvedImplementationMethodGroupBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ResolvedInterfaceBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ResolvedInterfaceMethodBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ResolvedMatchArmBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ResolvedRequirementBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ResolvedTypedPatternBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ResolvedTypeOccurrenceBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ResolvedTypeOccurrenceOwner.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ResolveTask.FinishBinding.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::ResolveTask.FinishRecursiveGroup.group", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::ResolveTask.VisitBlock.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::ResolveTask.VisitExpr.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::ResolveTask.VisitRecursiveGroup.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::ResolvedDeclarations.definitions", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolve.rs::ResolvedDeclarations.implementations", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolve.rs::ResolvedDeclarations.interfaces", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolve.rs::ResolvedDeclarations.registry", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree, Shared),
    kind_site!("src/resolve.rs::ResolvedDeclarationParts.$alias", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolve.rs::ResolvedTypeBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::Resolver.imported", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolve.rs::ValidatedImportedConstructorRoute.exported", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::$impl_ResolvedRegistry::$fn_display_type_with_inference::Task.ApplicationSpine.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/resolved.rs::$impl_ResolvedRegistry::$fn_display_type_with_inference::Task.Type.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/resolved.rs::AuthorizedImplementationFact.fact", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::CanonicalNominalKind.Frozen.kind", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/resolved.rs::CanonicalNominalKind.Parameters.parameters", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeRegistryTree),
    kind_site!("src/resolved.rs::CheckedDefinition.source", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::CheckedGlobalScheme.scheme", FieldCheckedSchemeSchemeValueInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedImplementationBody.source", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::CheckedImplementationFact.argument", FieldCheckedInterfaceArgumentInterfaceParameterInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedImplementationFact.head_parameters", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedImplementationFact.methods", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedImplementationFact.prerequisites", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedImplementationMethodFact.scheme", FieldCheckedSchemeSchemeValueInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedInterfaceFact.methods", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedInterfaceFact.parameter", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedInterfaceMethodFact.method_binder_authority", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::CheckedInterfaceMethodFact.type_parameters", FieldCheckedDeclaredKindDeclaredInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedInterfaceMethodFact.value_type", FieldCheckedValueTypeValueInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedModule.definitions", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::CheckedModule.exports", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedModule.implementation_facts", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedModule.implementations", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::CheckedModule.interface_facts", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedModule.interfaces", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedModule.registry", FieldRegistryCarrierRetentionPreservedCarrierElaborationInferenceTypeRegistryTree, Shared),
    kind_site!("src/resolved.rs::CheckedModule.schemes", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedModuleParts.definitions", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::CheckedModuleParts.exports", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedModuleParts.implementation_facts", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedModuleParts.implementations", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::CheckedModuleParts.interface_facts", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedModuleParts.schemes", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::CombinedRegistryBuilder.canonical_variables", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::CombinedRegistryBuilder.constructors", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::CombinedRegistryBuilder.nominal_parameters", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::CombinedRegistryBuilder.parameter_rows", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::CombinedRegistryBuilder.type_variables", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::ExportSummary.constructors", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ExportSummary.hidden_constructors", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ExportSummary.hidden_interfaces", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ExportSummary.hidden_nominals", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ExportSummary.implementations", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ExportSummary.interfaces", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ExportSummary.nominals", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ExportSummary.terms", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ExportedConstructor.payload", FieldSummaryValueTypeValueResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ExportedConstructor.scheme", FieldSummarySchemeSchemeValueResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ExportedGlobal.scheme", FieldSummarySchemeSchemeValueResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ExportedHiddenType.parameters", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ExportedType.parameters", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ImportedConstructorFact.payload", FieldSummaryValueTypeValueResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ImportedConstructorFact.scheme", FieldSummarySchemeSchemeValueResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ImportedFacts.constructors", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ImportedFacts.globals", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ImportedFacts.implementations", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ImportedFacts.interfaces", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ImportedFacts.nominals", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ImportedGlobalScheme.scheme", FieldSummarySchemeSchemeValueResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ImportedImplementationFact.fact", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ImportedInterfaceFact.fact", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ImportedNominalFact.parameters", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ImportedNominalFactRef.parameters", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree, Borrowed),
    kind_site!("src/resolved.rs::NonMaterializedNominalKindFact.kind", FieldRegistryCarrierRetentionPreservedCarrierElaborationInferenceTypeRegistryTree),
    kind_site!("src/resolved.rs::PreparedImportedNominalAction.Insert.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::PreparedImportedNominalMerge.action", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::ResolvedApplicationExpr.argument", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedApplicationExpr.function", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedBinaryExpr.left", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedBinaryExpr.right", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedBinding.annotation", FieldResolvedValueTypeValueResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedBinding.initializer", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedBlock.declarations", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedBlock.result", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedConstructor.payload", FieldResolvedValueTypeValueResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedConstructorBuffer.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedDefinition.kind", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedDefinitionKind.Equational.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedDefinitionKind.InlineOperational.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedEquation.body", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedEquationalGlobal.equations", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedEquationalGlobal.interface", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedExpr.kind", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedExprKind.Add.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedExprKind.Apply.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedExprKind.Block.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedExprKind.Equal.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedExprKind.Function.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedExprKind.Match.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedExprKind.Multiply.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedExprKind.Occurrence.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Shared),
    kind_site!("src/resolved.rs::ResolvedExprKind.Tuple.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedExternalInterface.annotation", FieldResolvedValueTypeValueResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedExternalInterface.requirements", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedExternalInterface.type_parameters", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedFunctionExpr.body", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedImplementation.argument", FieldResolvedInterfaceArgumentInterfaceParameterResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedImplementation.head_parameters", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedImplementation.method_groups", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedImplementation.prerequisite_only_parameters", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedImplementation.prerequisites", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedImplementationMethodGroup.equations", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedInlineOperationalGlobal.body", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedInlineOperationalGlobal.header", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedInlineOperationalHeader.parameters", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedInlineOperationalHeader.requirements", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedInlineOperationalHeader.result_type", FieldResolvedValueTypeValueResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedInlineOperationalHeader.type_parameters", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedInterfaceDeclaration.methods", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedInterfaceDeclaration.parameter", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedInterfaceMethod.annotation", FieldResolvedValueTypeValueResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedInterfaceMethod.type_parameters", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedLocalDeclaration.Binding.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedLocalDeclaration.Recursive.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedMatchArm.body", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedMatchExpr.arms", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedMatchExpr.scrutinee", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModule.definitions", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModule.implementations", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModule.imported", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedModule.interfaces", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedModule.registry", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree, Shared),
    kind_site!("src/resolved.rs::ResolvedModuleGroup.definitions", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModuleGroup.implementation_facts", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::ResolvedModuleGroup.implementations", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModuleGroup.interface_facts", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::ResolvedModuleGroup.interfaces", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::ResolvedModuleGroup.schemes", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::ResolvedModuleParts.definitions", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModuleParts.implementations", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModuleParts.imported", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedModuleParts.interfaces", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedModuleParts.registry", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree, Shared),
    kind_site!("src/resolved.rs::ResolvedModuleProgram.groups", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModuleProgram.registry", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree, Shared),
    kind_site!("src/resolved.rs::ResolvedModuleProgram.result", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedNominalParameterBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::ResolvedNominalParameterVecBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::ResolvedOccurrence.evidence", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Shared),
    kind_site!("src/resolved.rs::ResolvedRecursiveGroup.members", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedRecursiveMember.annotation", FieldResolvedValueTypeValueResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedRecursiveMember.initializer", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedRegistry.abstract_nominal_kinds", FieldRegistryCarrierRetentionPreservedCarrierElaborationInferenceTypeRegistryTree),
    kind_site!("src/resolved.rs::ResolvedRegistry.constructors", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree),
    kind_site!("src/resolved.rs::ResolvedRegistry.nominal_parameters", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree),
    kind_site!("src/resolved.rs::ResolvedRegistry.type_variables", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree),
    kind_site!("src/resolved.rs::ResolvedRequirement.argument", FieldResolvedInterfaceArgumentInterfaceParameterResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedType.ty", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedTypeVariableBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::ResolvedTypeVariable.kind", FieldResolvedDeclaredKindDeclaredResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedTypedPattern.annotation", FieldResolvedValueTypeValueResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::SummaryRequirementIndex.by_interface", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ValidatedCheckedRegistries.modules", FieldBorrowedTransientCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::ValidatedImportedNominalMerge.candidate", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/surface.rs::ApplicationExpr.argument", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::ApplicationExpr.function", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::BinaryExpr.left", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::BinaryExpr.right", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::EquationalGlobal.equations", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::EquationalGlobal.interface", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::FunctionExpr.body", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::FunctionType.codomain", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::FunctionType.domain", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::InlineOperationalGlobal.body", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::InlineOperationalGlobal.header", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceBinding.annotation", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceBinding.initializer", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceBlock.declarations", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceBlock.result", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceConstructorDeclaration.fields", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceDefinition.kind", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceDefinitionKind.Equational.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceDefinitionKind.InlineOperational.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceEquation.body", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExpr.kind", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExprKind.Add.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExprKind.Apply.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExprKind.Block.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExprKind.Equal.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExprKind.Function.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExprKind.Match.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExprKind.Multiply.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExprKind.Tuple.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExternalInterface.annotation", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExternalInterface.requirements", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExternalInterface.type_parameters", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceImplementation.argument", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceImplementation.equations", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceImplementation.prerequisites", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceImplementation.type_parameters", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceInlineOperationalHeader.parameters", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceInlineOperationalHeader.requirements", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceInlineOperationalHeader.result_type", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceInlineOperationalHeader.type_parameters", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceInterfaceDeclaration.methods", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceInterfaceDeclaration.parameter", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceInterfaceMethod.annotation", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceInterfaceMethod.type_parameters", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceKind.kind", FieldSurfaceDeclaredKindDeclaredProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceKindKind.Function.codomain", FieldSurfaceDeclaredKindDeclaredProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceKindKind.Function.domain", FieldSurfaceDeclaredKindDeclaredProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceLocalDeclaration.Binding.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceLocalDeclaration.Recursive.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceMatchArm.body", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceMatchExpr.arms", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceMatchExpr.scrutinee", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceModule.definitions", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceModule.implementations", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceModule.interfaces", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceModule.type_declarations", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceRecursiveGroup.members", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceRecursiveMember.annotation", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceRecursiveMember.initializer", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceRequirement.argument", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceType.kind", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceTypeDeclaration.constructors", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceTypeDeclaration.parameters", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceTypeKind.Application.arguments", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceTypeKind.Function.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceTypeKind.Tuple.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceTypeParameter.kind", FieldSurfaceDeclaredKindDeclaredProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceTypedBinder.annotation", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceTypedPattern.annotation", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/types.rs::Kind.Arrow.0", FieldCanonicalKindStructureKindSubtreeTypeOperationKindKindTree),
    kind_site!("src/types.rs::Kind.Arrow.1", FieldCanonicalKindStructureKindSubtreeTypeOperationKindKindTree),
    kind_site!("src/types.rs::Type.Application.0", FieldCanonicalApplicationStructureStructuralSubtreeTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::Type.Application.1", FieldCanonicalApplicationStructureStructuralSubtreeTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::Type.Forall.0", FieldCanonicalSchemeSchemeValueTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::Type.Forall.1", FieldCanonicalApplicationStructureStructuralSubtreeTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::Type.Function.0", FieldCanonicalApplicationStructureStructuralSubtreeTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::Type.Function.1", FieldCanonicalApplicationStructureStructuralSubtreeTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::Type.Tuple.0", FieldCanonicalApplicationStructureStructuralSubtreeTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_charge_type_cells::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_charge_type_cells::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_clone_kind_with_budget::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/types.rs::$fn_clone_type_with_budget::Task.Forall.0", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork),
    kind_site!("src/types.rs::$fn_clone_type_with_budget::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_clone_type_with_budget::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_discard_type_iteratively::Task.Sequence.0", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork),
    kind_site!("src/types.rs::$fn_discard_type_iteratively::Task.Visit.0", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork),
    kind_site!("src/types.rs::$fn_hash_type::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_hash_type::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_render_kind_with_budget::RenderedKind.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/types.rs::$fn_same_type::Task.Compare.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_same_type::Task.Compare.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_same_type::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_same_type_with_budget::Task.Compare.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_same_type_with_budget::Task.Compare.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_same_type_with_budget::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_substitute_type_variables::Task.FinishForall.0", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork),
    kind_site!("src/types.rs::$fn_substitute_type_variables::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_substitute_type_variables::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_substitute_type_variables_with::ChargeTask.Slice.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_substitute_type_variables_with::ChargeTask.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_write_kind::Task.kind", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/types.rs::$fn_write_type::Task.ApplicationSpine.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_write_type::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_write_type::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::IterativeTypeOwner.0", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork),
    kind_site!("src/resolve.rs::$local.surface_kind_to_kind.rebuilt", TransientTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/types.rs::$local.Kind.drop.work", TransientTransientCarrierRetentionPreservedCarrierTypeOperationKindTransientWork),
    kind_site!("src/types.rs::$local.arrows_with_budget.retained_domains", TransientTransientCarrierRetentionPreservedCarrierTypeOperationKindTransientWork),
    kind_site!("src/types.rs::$local.charge_kind_nodes.work", TransientBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/types.rs::$local.clone_kinded_type_parameters_with_budget.cloned", TransientTransientCarrierRetentionPreservedCarrierTypeOperationKindTransientWork),
    kind_site!("src/types.rs::$local.clone_kind_with_budget.rebuilt", TransientTransientCarrierRetentionPreservedCarrierTypeOperationKindTransientWork),
    kind_site!("src/types.rs::$local.clone_kind_with_budget.work", TransientBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/types.rs::$local.hash_kind_with_budget.work", TransientBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/types.rs::$local.same_kind_with_charge.work", TransientBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/types.rs::$local.write_kind.work", TransientBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::$local.KindEnvironments.synthesize.work", TransientBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTreeAndKindTree),
    kind_site!("src/kind.rs::$local.check_expression_work.work", TransientBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeResolvedTree),
    kind_site_for!("src/kind.rs::$kind.resolution_delta", "src/kind.rs::KindEnvironments.delta", KindSiteBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site_for!("src/kind.rs::$kind.elaboration_delta", "src/kind.rs::KindEnvironments.delta", KindSiteBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeKindTree),
    kind_site_for!("src/kind.rs::$kind.evidence_validation_delta", "src/kind.rs::KindEnvironments.delta", KindSiteBorrowedTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeKindTree),
    kind_site_for!("src/kind.rs::$kind.elaboration_omega", "src/kind.rs::KindEnvironments.omega", KindSiteBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeKindTree),
    kind_site_for!("src/kind.rs::$kind.resolution_xi", "src/kind.rs::KindEnvironments.xi", KindSiteTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site_for!("src/kind.rs::$kind.elaboration_xi", "src/kind.rs::KindEnvironments.xi", KindSiteTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeKindTree),
    kind_site_for!("src/kind.rs::$kind.evidence_validation_xi", "src/kind.rs::KindEnvironments.xi", KindSiteTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeKindTree),
    kind_site_for!("src/kind.rs::$kind.resolution_iota", "src/kind.rs::KindEnvironments.iota", KindSiteBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site_for!("src/core/type_ops.rs::$kind.type_abstraction_parameters", "src/core/type_ops.rs::TypeAbstractionNode.parameters", KindSiteCoreSchemeSchemeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/dialect.rs::$kind.ordinary_result", "src/core/dialect.rs::StoredNode.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/dialect.rs::$kind.type_abstraction_scheme", "src/core/dialect.rs::StoredNode.ty", KindSiteCoreSchemeSchemeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/dialect.rs::$kind.type_application_result", "src/core/dialect.rs::StoredNode.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/dialect.rs::$kind.typed_expr_ordinary_result", "src/core/dialect.rs::TypedExpr.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/dialect.rs::$kind.typed_expr_type_abstraction_scheme", "src/core/dialect.rs::TypedExpr.ty", KindSiteCoreSchemeSchemeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/dialect.rs::$kind.typed_expr_type_application_result", "src/core/dialect.rs::TypedExpr.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/variable.rs::$kind.monomorphic_function_binder", "src/core/variable.rs::TypedBinder.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/variable.rs::$kind.pattern_binder", "src/core/variable.rs::TypedBinder.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/variable.rs::$kind.monomorphic_sequential_binder", "src/core/variable.rs::TypedBinder.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/variable.rs::$kind.monomorphic_generated_evidence_binder", "src/core/variable.rs::TypedBinder.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/variable.rs::$kind.monomorphic_global_binder", "src/core/variable.rs::TypedBinder.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/variable.rs::$kind.monomorphic_implementation_method_binder", "src/core/variable.rs::TypedBinder.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/variable.rs::$kind.polymorphic_sequential_binder", "src/core/variable.rs::TypedBinder.ty", KindSiteCoreSchemeSchemeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/variable.rs::$kind.polymorphic_global_binder", "src/core/variable.rs::TypedBinder.ty", KindSiteCoreSchemeSchemeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/variable.rs::$kind.polymorphic_implementation_method_binder", "src/core/variable.rs::TypedBinder.ty", KindSiteCoreSchemeSchemeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/variable.rs::$kind.monomorphic_recursive_binder", "src/core/variable.rs::TypedBinder.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/variable.rs::$kind.polymorphic_recursive_binder", "src/core/variable.rs::TypedBinder.ty", KindSiteCoreSchemeSchemeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/resolved.rs::$kind.value_annotation", "src/resolved.rs::ResolvedType.ty", KindSiteResolvedValueTypeValueResolutionResolutionTypeResolvedTree),
    kind_site_for!("src/resolved.rs::$kind.interface_argument", "src/resolved.rs::ResolvedType.ty", KindSiteResolvedInterfaceArgumentInterfaceParameterResolutionResolutionTypeResolvedTree),
    kind_site_for!("src/elaborate.rs::$kind.lowered_core_monotype", "src/elaborate.rs::LoweredScheme.core_scheme", KindSiteTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site_for!("src/elaborate.rs::$kind.lowered_core_scheme", "src/elaborate.rs::LoweredScheme.core_scheme", KindSiteTransientSchemeSchemeValueElaborationInferenceTypeTransientWork),
    kind_site_for!("src/elaborate.rs::$kind.typed_node_monotype", "src/elaborate.rs::TypedNode.ty", KindSiteTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site_for!("src/elaborate.rs::$kind.typed_node_scheme", "src/elaborate.rs::TypedNode.ty", KindSiteTransientSchemeSchemeValueElaborationInferenceTypeTransientWork),
    kind_site_for!("src/interface.rs::$kind.implementation_overlap_head", "src/interface.rs::OverlapHead.ty", KindSiteBorrowedTransientInterfaceArgumentInterfaceParameterInterfaceValidationInterfaceTypeTypeTree),
    kind_site!("src/resolve.rs::$local.Resolver.resolve_type.completed", TransientTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::$local.ResolvedTypeProvenance.application_fold", TransientResolvedApplicationStructureStructuralSubtreeResolutionResolutionTypeResolvedTree),
    kind_site!("src/elaborate.rs::$local.unify.work", TransientTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$local.candidate_kind_environment.work", TransientTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$local.expression.tasks_and_values", TransientTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$local.retain_method_occurrence_parameters.fact_parameters", TransientTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$local.retain_method_occurrence_parameters.scheme_parameters", TransientTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$local.module.groups", TransientTransientCarrierRetentionPreservedCarrierElaborationCoreTypeTransientWork),
    kind_site!("src/evidence.rs::$local.selection.pending_values", TransientTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/core/dialect.rs::$local.admission.work", TransientTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/validate.rs::$local.validation.work", TransientTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeTransientWork),
    kind_site!("src/core/transform.rs::$local.transform.work", TransientTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/eval/machine.rs::$local.observation", TransientTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState),
];

#[rustfmt::skip]
const EXPECTED_CONTEXTUAL_SITES: &[KindSite] = &[
    kind_site_for!("src/kind.rs::$kind.resolution_delta", "src/kind.rs::KindEnvironments.delta", KindSiteBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site_for!("src/kind.rs::$kind.elaboration_delta", "src/kind.rs::KindEnvironments.delta", KindSiteBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeKindTree),
    kind_site_for!("src/kind.rs::$kind.evidence_validation_delta", "src/kind.rs::KindEnvironments.delta", KindSiteBorrowedTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeKindTree),
    kind_site_for!("src/kind.rs::$kind.elaboration_omega", "src/kind.rs::KindEnvironments.omega", KindSiteBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeKindTree),
    kind_site_for!("src/kind.rs::$kind.resolution_xi", "src/kind.rs::KindEnvironments.xi", KindSiteTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site_for!("src/kind.rs::$kind.elaboration_xi", "src/kind.rs::KindEnvironments.xi", KindSiteTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeKindTree),
    kind_site_for!("src/kind.rs::$kind.evidence_validation_xi", "src/kind.rs::KindEnvironments.xi", KindSiteTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeKindTree),
    kind_site_for!("src/kind.rs::$kind.resolution_iota", "src/kind.rs::KindEnvironments.iota", KindSiteBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site_for!("src/core/type_ops.rs::$kind.type_abstraction_parameters", "src/core/type_ops.rs::TypeAbstractionNode.parameters", KindSiteCoreSchemeSchemeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/dialect.rs::$kind.ordinary_result", "src/core/dialect.rs::StoredNode.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/dialect.rs::$kind.type_abstraction_scheme", "src/core/dialect.rs::StoredNode.ty", KindSiteCoreSchemeSchemeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/dialect.rs::$kind.type_application_result", "src/core/dialect.rs::StoredNode.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/dialect.rs::$kind.typed_expr_ordinary_result", "src/core/dialect.rs::TypedExpr.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/dialect.rs::$kind.typed_expr_type_abstraction_scheme", "src/core/dialect.rs::TypedExpr.ty", KindSiteCoreSchemeSchemeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/dialect.rs::$kind.typed_expr_type_application_result", "src/core/dialect.rs::TypedExpr.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/variable.rs::$kind.monomorphic_function_binder", "src/core/variable.rs::TypedBinder.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/variable.rs::$kind.pattern_binder", "src/core/variable.rs::TypedBinder.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/variable.rs::$kind.monomorphic_sequential_binder", "src/core/variable.rs::TypedBinder.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/variable.rs::$kind.monomorphic_generated_evidence_binder", "src/core/variable.rs::TypedBinder.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/variable.rs::$kind.monomorphic_global_binder", "src/core/variable.rs::TypedBinder.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/variable.rs::$kind.monomorphic_implementation_method_binder", "src/core/variable.rs::TypedBinder.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/variable.rs::$kind.polymorphic_sequential_binder", "src/core/variable.rs::TypedBinder.ty", KindSiteCoreSchemeSchemeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/variable.rs::$kind.polymorphic_global_binder", "src/core/variable.rs::TypedBinder.ty", KindSiteCoreSchemeSchemeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/variable.rs::$kind.polymorphic_implementation_method_binder", "src/core/variable.rs::TypedBinder.ty", KindSiteCoreSchemeSchemeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/variable.rs::$kind.monomorphic_recursive_binder", "src/core/variable.rs::TypedBinder.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/variable.rs::$kind.polymorphic_recursive_binder", "src/core/variable.rs::TypedBinder.ty", KindSiteCoreSchemeSchemeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/resolved.rs::$kind.value_annotation", "src/resolved.rs::ResolvedType.ty", KindSiteResolvedValueTypeValueResolutionResolutionTypeResolvedTree),
    kind_site_for!("src/resolved.rs::$kind.interface_argument", "src/resolved.rs::ResolvedType.ty", KindSiteResolvedInterfaceArgumentInterfaceParameterResolutionResolutionTypeResolvedTree),
    kind_site_for!("src/elaborate.rs::$kind.lowered_core_monotype", "src/elaborate.rs::LoweredScheme.core_scheme", KindSiteTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site_for!("src/elaborate.rs::$kind.lowered_core_scheme", "src/elaborate.rs::LoweredScheme.core_scheme", KindSiteTransientSchemeSchemeValueElaborationInferenceTypeTransientWork),
    kind_site_for!("src/elaborate.rs::$kind.typed_node_monotype", "src/elaborate.rs::TypedNode.ty", KindSiteTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site_for!("src/elaborate.rs::$kind.typed_node_scheme", "src/elaborate.rs::TypedNode.ty", KindSiteTransientSchemeSchemeValueElaborationInferenceTypeTransientWork),
    kind_site_for!("src/interface.rs::$kind.implementation_overlap_head", "src/interface.rs::OverlapHead.ty", KindSiteBorrowedTransientInterfaceArgumentInterfaceParameterInterfaceValidationInterfaceTypeTypeTree),
];

const CONTEXTUAL_ROLE_SETS: &[(&str, &[&str])] = &[
    (
        "src/kind.rs::KindEnvironments.delta",
        &[
            "src/kind.rs::$kind.resolution_delta",
            "src/kind.rs::$kind.elaboration_delta",
            "src/kind.rs::$kind.evidence_validation_delta",
        ],
    ),
    (
        "src/kind.rs::KindEnvironments.omega",
        &["src/kind.rs::$kind.elaboration_omega"],
    ),
    (
        "src/kind.rs::KindEnvironments.xi",
        &[
            "src/kind.rs::$kind.resolution_xi",
            "src/kind.rs::$kind.elaboration_xi",
            "src/kind.rs::$kind.evidence_validation_xi",
        ],
    ),
    (
        "src/kind.rs::KindEnvironments.iota",
        &["src/kind.rs::$kind.resolution_iota"],
    ),
    (
        "src/core/type_ops.rs::TypeAbstractionNode.parameters",
        &["src/core/type_ops.rs::$kind.type_abstraction_parameters"],
    ),
    (
        "src/core/dialect.rs::StoredNode.ty",
        &[
            "src/core/dialect.rs::$kind.ordinary_result",
            "src/core/dialect.rs::$kind.type_abstraction_scheme",
            "src/core/dialect.rs::$kind.type_application_result",
        ],
    ),
    (
        "src/core/dialect.rs::TypedExpr.ty",
        &[
            "src/core/dialect.rs::$kind.typed_expr_ordinary_result",
            "src/core/dialect.rs::$kind.typed_expr_type_abstraction_scheme",
            "src/core/dialect.rs::$kind.typed_expr_type_application_result",
        ],
    ),
    (
        "src/core/variable.rs::TypedBinder.ty",
        &[
            "src/core/variable.rs::$kind.monomorphic_function_binder",
            "src/core/variable.rs::$kind.pattern_binder",
            "src/core/variable.rs::$kind.monomorphic_sequential_binder",
            "src/core/variable.rs::$kind.monomorphic_generated_evidence_binder",
            "src/core/variable.rs::$kind.monomorphic_global_binder",
            "src/core/variable.rs::$kind.monomorphic_implementation_method_binder",
            "src/core/variable.rs::$kind.polymorphic_sequential_binder",
            "src/core/variable.rs::$kind.polymorphic_global_binder",
            "src/core/variable.rs::$kind.polymorphic_implementation_method_binder",
            "src/core/variable.rs::$kind.monomorphic_recursive_binder",
            "src/core/variable.rs::$kind.polymorphic_recursive_binder",
        ],
    ),
    (
        "src/resolved.rs::ResolvedType.ty",
        &[
            "src/resolved.rs::$kind.interface_argument",
            "src/resolved.rs::$kind.value_annotation",
        ],
    ),
    (
        "src/elaborate.rs::LoweredScheme.core_scheme",
        &[
            "src/elaborate.rs::$kind.lowered_core_monotype",
            "src/elaborate.rs::$kind.lowered_core_scheme",
        ],
    ),
    (
        "src/elaborate.rs::TypedNode.ty",
        &[
            "src/elaborate.rs::$kind.typed_node_monotype",
            "src/elaborate.rs::$kind.typed_node_scheme",
        ],
    ),
    (
        "src/interface.rs::OverlapHead.ty",
        &["src/interface.rs::$kind.implementation_overlap_head"],
    ),
];

const TRANSIENT_SITE_SOURCE_ANCHORS: &[(&str, &str)] = &[
    (
        "src/resolve.rs::$local.surface_kind_to_kind.rebuilt",
        "surface_kind_to_kind",
    ),
    ("src/types.rs::$local.Kind.drop.work", "Kind"),
    (
        "src/types.rs::$local.arrows_with_budget.retained_domains",
        "arrows_with_budget",
    ),
    (
        "src/interface.rs::$local.charge_equal_kinds.pending",
        "charge_equal_kinds",
    ),
    (
        "src/types.rs::$local.charge_kind_nodes.work",
        "charge_kind_nodes",
    ),
    (
        "src/types.rs::$local.clone_kinded_type_parameters_with_budget.cloned",
        "clone_kinded_type_parameters_with_budget",
    ),
    (
        "src/types.rs::$local.clone_kind_with_budget.rebuilt",
        "clone_kind_with_budget",
    ),
    (
        "src/types.rs::$local.clone_kind_with_budget.work",
        "clone_kind_with_budget",
    ),
    (
        "src/types.rs::$local.hash_kind_with_budget.work",
        "hash_kind_with_budget",
    ),
    (
        "src/types.rs::$local.same_kind_with_charge.work",
        "same_kind_with_charge",
    ),
    ("src/types.rs::$local.write_kind.work", "write_kind"),
    (
        "src/kind.rs::$local.KindEnvironments.synthesize.work",
        "synthesize_with_ledger",
    ),
    (
        "src/kind.rs::$local.check_expression_work.work",
        "check_expression_work",
    ),
    (
        "src/resolve.rs::$local.Resolver.resolve_type.completed",
        "resolve_type",
    ),
    (
        "src/resolved.rs::$local.ResolvedTypeProvenance.application_fold",
        "ResolvedTypeProvenanceNode",
    ),
    ("src/elaborate.rs::$local.unify.work", "unify"),
    (
        "src/elaborate.rs::$local.candidate_kind_environment.work",
        "candidate_kind_environment",
    ),
    (
        "src/elaborate.rs::$local.expression.tasks_and_values",
        "ElaborationTaskBuffer",
    ),
    (
        "src/elaborate.rs::$local.retain_method_occurrence_parameters.fact_parameters",
        "retain_method_occurrence_parameters",
    ),
    (
        "src/elaborate.rs::$local.retain_method_occurrence_parameters.scheme_parameters",
        "retain_method_occurrence_parameters",
    ),
    (
        "src/elaborate.rs::$local.module.groups",
        "ElaboratedGroupBuffer",
    ),
    (
        "src/evidence.rs::$local.selection.pending_values",
        "EvidenceSelector",
    ),
    (
        "src/core/dialect.rs::$local.admission.work",
        "TypeAdmissionTask",
    ),
    ("src/core/validate.rs::$local.validation.work", "Validator"),
    (
        "src/core/transform.rs::$local.transform.work",
        "rebuild_node",
    ),
    ("src/eval/machine.rs::$local.observation", "Machine"),
];

#[rustfmt::skip]
const EXPECTED_SHARED_KIND_ENGINE_SITES: &[KindSite] = &[
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_with_ledger::Continuation.ApplicationArgument.function", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_with_ledger::Continuation.ApplicationFunction.argument", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_with_ledger::Continuation.ApplicationFunction.argument_mirror", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_with_ledger::Continuation.FunctionDomain.codomain", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_with_ledger::Continuation.FunctionDomain.codomain_mirror", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_with_ledger::Continuation.Tuple.remaining", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_with_ledger::Continuation.Tuple.remaining_mirrors", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_with_ledger::State.Complete.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_with_ledger::State.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_with_ledger::State.Visit.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::KindFact.kind", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::KindFact.retained_mirrors", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::NominalKindFact.kind", FieldTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::RetainedKindMirrors.Two.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::RetainedKindMirrors.Two.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::$local.KindEnvironments.synthesize.work", TransientBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTreeAndKindTree),
];

#[test]
fn canonical_nominal_kind_views_follow_ultimate_referents() {
    let site = |key| {
        KIND_SITES
            .iter()
            .find(|site| site.key == key)
            .copied()
            .unwrap_or_else(|| panic!("missing canonical nominal Kind view {key}"))
    };

    let parameters = site("src/resolved.rs::CanonicalNominalKind.Parameters.parameters");
    assert_eq!(
        (
            parameters.scope,
            parameters.retention,
            parameters.environment,
            parameters.rule,
            parameters.required_result,
            parameters.failure_owner,
            parameters.budget,
            parameters.disposal_owner,
        ),
        (
            InventoryScope::Field,
            RetentionMode::Borrowed,
            KindEnvironmentOwner::Transient,
            KindRule::CarrierRetention,
            RequiredKindResult::PreservedCarrier,
            FailureOwner::TypeOperation,
            BudgetOwner::Type,
            DisposalOwner::RegistryTree,
        ),
        "the shared borrowed parameter view is a phase-neutral type operation over registry-owned binder records",
    );

    let frozen = site("src/resolved.rs::CanonicalNominalKind.Frozen.kind");
    assert_eq!(
        (
            frozen.scope,
            frozen.retention,
            frozen.environment,
            frozen.rule,
            frozen.required_result,
            frozen.failure_owner,
            frozen.budget,
            frozen.disposal_owner,
        ),
        (
            InventoryScope::Field,
            RetentionMode::Borrowed,
            KindEnvironmentOwner::Transient,
            KindRule::CarrierRetention,
            RequiredKindResult::PreservedCarrier,
            FailureOwner::TypeOperation,
            BudgetOwner::Kind,
            DisposalOwner::KindTree,
        ),
        "the shared frozen view is a phase-neutral Kind operation borrowing its standalone Kind tree",
    );
}

#[test]
fn kind_inventory_is_closed() {
    fn exhaust_kind_variants(kind: &Kind) {
        match kind {
            Kind::Type | Kind::Arrow(_, _) => {}
        }
    }

    fn exhaust_type_variants(ty: &Type) {
        match ty {
            Type::Int
            | Type::Bool
            | Type::Unit
            | Type::Tuple(_)
            | Type::Nominal(_)
            | Type::Variable(_)
            | Type::Inference(_)
            | Type::Application(_, _)
            | Type::Forall(_, _)
            | Type::Function(_, _) => {}
        }
    }

    exhaust_kind_variants(&Kind::Type);
    exhaust_type_variants(&Type::Unit);
    let mut names = HashSet::new();
    for site in KIND_SITES {
        assert!(names.insert(site.key), "duplicate kind site {}", site.key);
        assert!(!site.key.is_empty());
        let profile = site
            .profile
            .unwrap_or_else(|| panic!("kind site {} has no exact named profile", site.key));
        assert_eq!(
            profile.expand(site.key, site.carrier),
            *site,
            "kind site {} drifted from its exact named profile",
            site.key,
        );
        let _ = (
            site.carrier,
            site.scope,
            site.retention,
            site.environment,
            site.rule,
            site.required_result,
            site.failure_owner,
            site.budget,
            site.disposal_owner,
        );
        assert!(
            matches!(
                (site.rule, site.required_result),
                (
                    KindRule::ProjectionOnly,
                    RequiredKindResult::DeferredProjection
                ) | (KindRule::ValueType, RequiredKindResult::Value)
                    | (
                        KindRule::InterfaceArgument,
                        RequiredKindResult::InterfaceParameter
                    )
                    | (KindRule::Scheme, RequiredKindResult::SchemeValue)
                    | (KindRule::DeclaredKind, RequiredKindResult::Declared)
                    | (
                        KindRule::ApplicationStructure,
                        RequiredKindResult::StructuralSubtree
                    )
                    | (KindRule::KindStructure, RequiredKindResult::KindSubtree)
                    | (
                        KindRule::CoreInstantiation,
                        RequiredKindResult::InstantiationArgument
                    )
                    | (
                        KindRule::CarrierRetention,
                        RequiredKindResult::PreservedCarrier
                    )
            ),
            "incoherent kind rule/result at {}",
            site.key
        );
    }
    let used_profiles = KIND_SITES
        .iter()
        .map(|site| site.profile.expect("every site has an exact profile").id)
        .collect::<HashSet<_>>();
    let declared_profiles = ALL_PROFILE_IDS.iter().copied().collect::<HashSet<_>>();
    assert_eq!(
        used_profiles, declared_profiles,
        "named kind-site profiles must be used exactly by the closed inventory",
    );
    let physical_carriers = KIND_SITES
        .iter()
        .filter(|site| site.scope == InventoryScope::Field)
        .map(|site| site.key)
        .collect::<HashSet<_>>();
    for site in KIND_SITES
        .iter()
        .filter(|site| site.key.contains("::$kind."))
    {
        assert!(
            physical_carriers.contains(site.carrier),
            "semantic kind site {} is detached from physical carrier {}",
            site.key,
            site.carrier,
        );
    }
    let contextual_sites = KIND_SITES
        .iter()
        .filter(|site| site.key.contains("::$kind."))
        .copied()
        .collect::<Vec<_>>();
    assert_eq!(
        contextual_sites, EXPECTED_CONTEXTUAL_SITES,
        "the complete contextual kind-site profile changed without updating its exact inventory",
    );
    for (carrier, expected_roles) in CONTEXTUAL_ROLE_SETS {
        let mut actual_roles = contextual_sites
            .iter()
            .filter(|site| site.carrier == *carrier)
            .map(|site| site.key)
            .collect::<Vec<_>>();
        actual_roles.sort_unstable();
        let mut expected_roles = expected_roles.to_vec();
        expected_roles.sort_unstable();
        assert_eq!(
            actual_roles, expected_roles,
            "contextual role set drifted for {carrier}",
        );
    }
    assert_eq!(
        contextual_sites.len(),
        CONTEXTUAL_ROLE_SETS
            .iter()
            .map(|(_, roles)| roles.len())
            .sum::<usize>(),
        "every contextual kind site must belong to one exact carrier role set",
    );
    assert!(TASK_4_PHASE_CONSTRAINT.contains("only for this phase"));
}

#[test]
fn physical_constructor_schemes_end_at_the_body_free_summary_boundary() {
    let constructor_scheme_sites = KIND_SITES
        .iter()
        .filter(|site| site.carrier.contains("Constructor") && site.rule == KindRule::Scheme)
        .collect::<Vec<_>>();
    assert_eq!(
        constructor_scheme_sites
            .iter()
            .map(|site| site.key)
            .collect::<Vec<_>>(),
        [
            "src/resolved.rs::ExportedConstructor.scheme",
            "src/resolved.rs::ImportedConstructorFact.scheme",
        ],
        "the physical constructor scheme must not survive into linked registry or program carriers",
    );
    for site in constructor_scheme_sites {
        assert_eq!(site.environment, KindEnvironmentOwner::Summary);
        assert_eq!(site.disposal_owner, DisposalOwner::SummaryTree);
    }
}

#[test]
fn transient_kind_site_owners_are_source_anchored() {
    let manifested = KIND_SITES
        .iter()
        .filter(|site| site.scope == InventoryScope::Transient)
        .map(|site| site.key)
        .collect::<BTreeSet<_>>();
    let anchored = TRANSIENT_SITE_SOURCE_ANCHORS
        .iter()
        .map(|(site, _)| *site)
        .collect::<BTreeSet<_>>();
    assert_eq!(
        manifested, anchored,
        "every transient semantic site must carry one live source anchor",
    );

    for (site, anchor) in TRANSIENT_SITE_SOURCE_ANCHORS {
        let (source, _) = site
            .split_once("::$local.")
            .unwrap_or_else(|| panic!("transient site {site} has no local-owner marker"));
        let source = fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join(source))
            .unwrap_or_else(|error| panic!("cannot read {source} for {site}: {error}"));
        assert!(
            rust_code_identifiers(&source).contains(anchor),
            "transient site {site} has no live source owner matching {anchor:?}",
        );
    }
}

#[test]
fn shared_kind_engine_sites_are_phase_neutral() {
    let expected_keys = EXPECTED_SHARED_KIND_ENGINE_SITES
        .iter()
        .map(|site| site.key)
        .collect::<BTreeSet<_>>();
    let actual = KIND_SITES
        .iter()
        .filter(|site| expected_keys.contains(site.key))
        .copied()
        .collect::<Vec<_>>();
    assert_eq!(
        actual, EXPECTED_SHARED_KIND_ENGINE_SITES,
        "shared synthesis storage must not claim one caller's failure or budget ownership",
    );
}

const DRIVER_SOURCE: &str = include_str!("../src/driver.rs");
const PARSER_EXPORTS: &str = include_str!("../src/parser/mod.rs");
const PARSER_GRAMMAR: &str = include_str!("../src/parser/grammar.rs");
const PARSER_PROJECTION: &str = include_str!("../src/parser/project.rs");
const CORE_SOURCES: &[(&str, &str)] = &[
    (
        "src/core/binding.rs",
        include_str!("../src/core/binding.rs"),
    ),
    ("src/core/data.rs", include_str!("../src/core/data.rs")),
    (
        "src/core/dialect.rs",
        include_str!("../src/core/dialect.rs"),
    ),
    (
        "src/core/function.rs",
        include_str!("../src/core/function.rs"),
    ),
    (
        "src/core/literal.rs",
        include_str!("../src/core/literal.rs"),
    ),
    ("src/core/mod.rs", include_str!("../src/core/mod.rs")),
    (
        "src/core/primitive.rs",
        include_str!("../src/core/primitive.rs"),
    ),
    (
        "src/core/recursion.rs",
        include_str!("../src/core/recursion.rs"),
    ),
    (
        "src/core/transform.rs",
        include_str!("../src/core/transform.rs"),
    ),
    (
        "src/core/type_ops.rs",
        include_str!("../src/core/type_ops.rs"),
    ),
    (
        "src/core/validate.rs",
        include_str!("../src/core/validate.rs"),
    ),
    (
        "src/core/variable.rs",
        include_str!("../src/core/variable.rs"),
    ),
];
const EVALUATOR_SOURCES: &[(&str, &str)] = &[
    (
        "src/eval/machine.rs",
        include_str!("../src/eval/machine.rs"),
    ),
    ("src/eval/mod.rs", include_str!("../src/eval/mod.rs")),
    ("src/eval/value.rs", include_str!("../src/eval/value.rs")),
];

#[test]
fn canonical_type_carrier_inventory_has_a_source_closed_fixed_point() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut sources = Vec::new();
    collect_production_rust_sources(&root, &mut sources);
    for source_path in sources {
        let path = source_path
            .strip_prefix(env!("CARGO_MANIFEST_DIR"))
            .expect("production source belongs to the crate")
            .to_string_lossy()
            .replace('\\', "/");
        let source =
            fs::read_to_string(source_path).expect("production Rust source should be readable");
        let identifiers = rust_code_identifiers(&source);
        assert!(
            !identifiers.contains(&"AppliedNominal"),
            "{path} retains the predecessor saturated nominal representation"
        );
        for forbidden in ["SaturatedNominal", "NominalApplication", "AppliedType"] {
            assert!(
                !identifiers.contains(&forbidden),
                "{path} introduces a second canonical application form {forbidden}"
            );
        }
    }
    assert!(
        rust_code_identifiers(include_str!("../src/types.rs")).contains(&"Application"),
        "Type must retain the one canonical unary Application variant"
    );
    assert!(
        rust_code_identifiers(include_str!("../src/core/type_ops.rs"))
            .contains(&"TypeApplicationNode"),
        "Core erased scheme application remains a distinct simultaneous n-ary node"
    );
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ProductionField {
    source: String,
    carrier: String,
    field: String,
    references: BTreeSet<String>,
    reference_retentions: BTreeMap<String, RetentionSet>,
    aliases: BTreeMap<String, String>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct CarrierId {
    source: String,
    name: String,
}

impl ProductionField {
    fn key(&self) -> String {
        format!("{}::{}.{}", self.source, self.carrier, self.field)
    }
}

#[test]
fn every_production_type_field_is_manifested_bidirectionally() {
    let fields = production_fields();
    let owning_carriers = transitive_type_owners(&fields);
    let declarations = declaration_index(&fields);
    let actual = fields
        .iter()
        .filter(|field| {
            field.references.iter().any(|reference| {
                reference_reaches_owner_with_aliases(
                    &field.source,
                    &field.carrier,
                    reference,
                    &field.aliases,
                    &declarations,
                    &owning_carriers,
                )
            })
        })
        .map(ProductionField::key)
        .collect::<BTreeSet<_>>();
    let manifested = KIND_SITES
        .iter()
        .filter(|site| site.scope == InventoryScope::Field)
        .map(|site| site.key.to_owned())
        .collect::<BTreeSet<_>>();

    let missing = actual.difference(&manifested).cloned().collect::<Vec<_>>();
    let stale = manifested.difference(&actual).cloned().collect::<Vec<_>>();
    assert!(
        missing.is_empty() && stale.is_empty(),
        "type-field manifest is not a bidirectional fixed point\nactual:\n{}\nmissing:\n{}\nstale:\n{}",
        actual.iter().cloned().collect::<Vec<_>>().join("\n"),
        missing.join("\n"),
        stale.join("\n"),
    );
    let retention_modes = transitive_type_retention_sets(&fields);
    let retention_mismatches = fields
        .iter()
        .filter_map(|field| {
            let key = field.key();
            if !actual.contains(&key) {
                return None;
            }
            let derived = field_type_retention(field, &declarations, &retention_modes)
                .expect("a type-bearing field has derived retention");
            let manifested = KIND_SITES
                .iter()
                .find(|site| site.scope == InventoryScope::Field && site.key == key)
                .expect("bidirectional closure already proved the physical site exists")
                .retention;
            (derived != manifested)
                .then(|| format!("{key}: source={derived:?}, manifest={manifested:?}"))
        })
        .collect::<Vec<_>>();
    assert!(
        retention_mismatches.is_empty(),
        "physical retention profiles drifted from source ownership:\n{}",
        retention_mismatches.join("\n"),
    );
}

#[test]
fn carrier_scanner_derives_owned_borrowed_shared_and_mixed_retention() {
    let mut fields = parse_top_level_fields("src/types.rs", "struct Type;");
    fields.extend(parse_top_level_fields(
        "src/shapes.rs",
        "use std::sync::Arc as SharedPtr; \
         use std::slice::Iter as SliceIter; \
         struct Owned(crate::types::Type); \
         struct Borrowed<'a>(&'a crate::types::Type); \
         struct Shared(std::sync::Arc<crate::types::Type>); \
         enum Mixed<'a> { Owned(crate::types::Type), Borrowed(&'a crate::types::Type) } \
         struct MixedBuffer(Vec<Mixed<'static>>); \
         struct FieldMixed<'a> { pair: (&'a crate::types::Type, crate::types::Type) } \
         struct OwnedWithUnrelatedBorrow<'a> { pair: (crate::types::Type, &'a str) } \
         struct BorrowedTwice<'a> { pair: (&'a crate::types::Type, &'a crate::types::Type) } \
         struct MixedSameField { pair: (crate::types::Type, std::sync::Arc<crate::types::Type>) } \
         struct SharedWithUnrelatedBorrow<'a> { pair: (&'a u32, std::sync::Arc<crate::types::Type>) } \
         type SharedAlias = std::sync::Arc<crate::types::Type>; \
         struct AliasedShared(SharedAlias); \
         struct ImportAliasedShared(SharedPtr<crate::types::Type>); \
         struct ImportAliasedBorrowed<'a>(SliceIter<'a, crate::types::Type>); \
         struct Arc<T>(T); \
         struct LocalArc(Arc<crate::types::Type>); \
         struct Iter<T>(T); \
         struct LocalIter(Iter<crate::types::Type>); \
         struct RawPointer(*const crate::types::Type); \
         struct OwnedAndShared { owned: crate::types::Type, shared: Shared } \
         struct SharedOwnedAndShared(std::sync::Arc<OwnedAndShared>); \
         struct SharedOwnedAndBorrowed(std::sync::Arc<FieldMixed<'static>>);",
    ));
    let modes = transitive_type_retention(&fields);
    for (carrier, expected) in [
        ("Owned", RetentionMode::Owned),
        ("Borrowed", RetentionMode::Borrowed),
        ("Shared", RetentionMode::Shared),
        ("Mixed", RetentionMode::Mixed),
        ("MixedBuffer", RetentionMode::Mixed),
        ("FieldMixed", RetentionMode::Mixed),
        ("OwnedWithUnrelatedBorrow", RetentionMode::Owned),
        ("BorrowedTwice", RetentionMode::Borrowed),
        ("MixedSameField", RetentionMode::Mixed),
        ("SharedWithUnrelatedBorrow", RetentionMode::Shared),
        ("SharedAlias", RetentionMode::Shared),
        ("AliasedShared", RetentionMode::Shared),
        ("ImportAliasedShared", RetentionMode::Shared),
        ("ImportAliasedBorrowed", RetentionMode::Borrowed),
        ("LocalArc", RetentionMode::Owned),
        ("LocalIter", RetentionMode::Owned),
        ("RawPointer", RetentionMode::Borrowed),
        ("OwnedAndShared", RetentionMode::Mixed),
        ("SharedOwnedAndShared", RetentionMode::Shared),
        ("SharedOwnedAndBorrowed", RetentionMode::Mixed),
    ] {
        assert_eq!(
            modes.get(&CarrierId {
                source: "src/shapes.rs".to_owned(),
                name: carrier.to_owned(),
            }),
            Some(&expected),
            "incorrect derived retention for {carrier}",
        );
    }
}

fn production_fields() -> Vec<ProductionField> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut sources = Vec::new();
    collect_production_rust_sources(&root, &mut sources);
    sources.sort();
    let mut fields = Vec::new();
    for path in sources {
        let relative = path
            .strip_prefix(env!("CARGO_MANIFEST_DIR"))
            .expect("production source belongs to the crate")
            .to_string_lossy()
            .replace('\\', "/");
        let source = fs::read_to_string(&path).expect("production Rust source should be readable");
        fields.extend(parse_top_level_fields(&relative, &source));
    }
    fields
}

fn collect_production_rust_sources(directory: &Path, output: &mut Vec<PathBuf>) {
    let mut entries = fs::read_dir(directory)
        .expect("production source directory should be readable")
        .map(|entry| {
            entry
                .expect("production source entry should be readable")
                .path()
        })
        .collect::<Vec<_>>();
    entries.sort();
    for path in entries {
        if path.is_dir() {
            collect_production_rust_sources(&path, output);
        } else if path.extension().is_some_and(|extension| extension == "rs")
            && !path
                .file_name()
                .is_some_and(|name| name.to_string_lossy().ends_with("_tests.rs"))
        {
            output.push(path);
        }
    }
}

fn transitive_type_owners(fields: &[ProductionField]) -> BTreeSet<CarrierId> {
    let by_name = declaration_index(fields);
    let mut owners = [
        ("src/types.rs", "Type"),
        ("src/types.rs", "Kind"),
        ("src/surface.rs", "SurfaceType"),
        ("src/surface.rs", "SurfaceKind"),
    ]
    .into_iter()
    .map(|(source, name)| CarrierId {
        source: source.to_owned(),
        name: name.to_owned(),
    })
    .collect::<BTreeSet<_>>();
    loop {
        let discovered = fields
            .iter()
            .filter(|field| {
                field.references.iter().any(|reference| {
                    reference_reaches_owner_with_aliases(
                        &field.source,
                        &field.carrier,
                        reference,
                        &field.aliases,
                        &by_name,
                        &owners,
                    )
                })
            })
            .map(|field| CarrierId {
                source: field.source.clone(),
                name: field.carrier.clone(),
            })
            .collect::<Vec<_>>();
        let previous = owners.len();
        owners.extend(discovered);
        if owners.len() == previous {
            return owners;
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct RetentionSet(u8);

impl RetentionSet {
    const OWNED: u8 = 1;
    const SHARED: u8 = 2;
    const BORROWED: u8 = 4;

    const fn owned() -> Self {
        Self(Self::OWNED)
    }

    const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    const fn collapse(self) -> RetentionMode {
        match self.0 {
            Self::OWNED => RetentionMode::Owned,
            Self::SHARED => RetentionMode::Shared,
            Self::BORROWED => RetentionMode::Borrowed,
            _ => RetentionMode::Mixed,
        }
    }
}

fn transform_retention(direct: RetentionSet, referenced: RetentionSet) -> RetentionSet {
    let mut transformed = RetentionSet(0);
    if direct.0 & RetentionSet::OWNED != 0 {
        transformed = transformed.union(referenced);
    }
    if direct.0 & RetentionSet::SHARED != 0 {
        let mut shared = 0;
        if referenced.0 & (RetentionSet::OWNED | RetentionSet::SHARED) != 0 {
            shared |= RetentionSet::SHARED;
        }
        if referenced.0 & RetentionSet::BORROWED != 0 {
            shared |= RetentionSet::BORROWED;
        }
        transformed = transformed.union(RetentionSet(shared));
    }
    if direct.0 & RetentionSet::BORROWED != 0 && referenced.0 != 0 {
        transformed = transformed.union(RetentionSet(RetentionSet::BORROWED));
    }
    transformed
}

fn field_type_retention(
    field: &ProductionField,
    declarations: &BTreeMap<String, Vec<CarrierId>>,
    carrier_modes: &BTreeMap<CarrierId, RetentionSet>,
) -> Option<RetentionMode> {
    field_type_retention_set(field, declarations, carrier_modes).map(RetentionSet::collapse)
}

fn field_type_retention_set(
    field: &ProductionField,
    declarations: &BTreeMap<String, Vec<CarrierId>>,
    carrier_modes: &BTreeMap<CarrierId, RetentionSet>,
) -> Option<RetentionSet> {
    let mut result = None;
    for reference in &field.references {
        let terminal = reference.rsplit("::").next().unwrap_or(reference);
        let has_known_candidate = if reference == "Self" {
            carrier_modes.contains_key(&CarrierId {
                source: field.source.clone(),
                name: field.carrier.clone(),
            })
        } else {
            declarations.get(terminal).is_some_and(|candidates| {
                candidates
                    .iter()
                    .any(|candidate| carrier_modes.contains_key(candidate))
            })
        };
        if !has_known_candidate {
            continue;
        }
        let mut referenced = RetentionSet(0);
        for bit in [
            RetentionSet::OWNED,
            RetentionSet::SHARED,
            RetentionSet::BORROWED,
        ] {
            let owners = carrier_modes
                .iter()
                .filter_map(|(carrier, mode)| (mode.0 & bit != 0).then_some(carrier.clone()))
                .collect::<BTreeSet<_>>();
            if reference_reaches_owner_with_aliases(
                &field.source,
                &field.carrier,
                reference,
                &field.aliases,
                declarations,
                &owners,
            ) {
                referenced.0 |= bit;
            }
        }
        if referenced.0 != 0 {
            let direct = field
                .reference_retentions
                .get(reference)
                .expect("every parsed reference has a direct retention mode");
            let mode = transform_retention(*direct, referenced);
            result = Some(result.map_or(mode, |current: RetentionSet| current.union(mode)));
        }
    }
    result
}

fn transitive_type_retention(fields: &[ProductionField]) -> BTreeMap<CarrierId, RetentionMode> {
    transitive_type_retention_sets(fields)
        .into_iter()
        .map(|(carrier, retention)| (carrier, retention.collapse()))
        .collect()
}

fn transitive_type_retention_sets(fields: &[ProductionField]) -> BTreeMap<CarrierId, RetentionSet> {
    transitive_retention_sets_with_roots(
        fields,
        &[
            ("src/types.rs", "Type"),
            ("src/types.rs", "Kind"),
            ("src/surface.rs", "SurfaceType"),
            ("src/surface.rs", "SurfaceKind"),
        ],
    )
}

fn transitive_retention_sets_with_roots(
    fields: &[ProductionField],
    roots: &[(&str, &str)],
) -> BTreeMap<CarrierId, RetentionSet> {
    let declarations = declaration_index(fields);
    let mut modes = roots
        .iter()
        .copied()
        .map(|(source, name)| {
            (
                CarrierId {
                    source: source.to_owned(),
                    name: name.to_owned(),
                },
                RetentionSet::owned(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    loop {
        let mut discovered = BTreeMap::<CarrierId, RetentionSet>::new();
        for field in fields {
            let Some(retention) = field_type_retention_set(field, &declarations, &modes) else {
                continue;
            };
            let carrier = CarrierId {
                source: field.source.clone(),
                name: field.carrier.clone(),
            };
            discovered
                .entry(carrier)
                .and_modify(|current| *current = current.union(retention))
                .or_insert(retention);
        }
        let mut changed = false;
        for (carrier, retention) in discovered {
            match modes.get_mut(&carrier) {
                Some(current) => {
                    let combined = current.union(retention);
                    if combined != *current {
                        *current = combined;
                        changed = true;
                    }
                }
                None => {
                    modes.insert(carrier, retention);
                    changed = true;
                }
            }
        }
        if !changed {
            return modes;
        }
    }
}

fn declaration_index(fields: &[ProductionField]) -> BTreeMap<String, Vec<CarrierId>> {
    fields.iter().fold(
        BTreeMap::<String, Vec<CarrierId>>::new(),
        |mut index, field| {
            let declaration = CarrierId {
                source: field.source.clone(),
                name: field.carrier.clone(),
            };
            let name = field
                .carrier
                .rsplit("::")
                .next()
                .unwrap_or(&field.carrier)
                .to_owned();
            let candidates = index.entry(name).or_default();
            if !candidates.contains(&declaration) {
                candidates.push(declaration);
            }
            index
        },
    )
}

fn reference_reaches_owner(
    source: &str,
    carrier: &str,
    reference: &str,
    declarations: &BTreeMap<String, Vec<CarrierId>>,
    owners: &BTreeSet<CarrierId>,
) -> bool {
    reference_reaches_owner_with_aliases(
        source,
        carrier,
        reference,
        &BTreeMap::new(),
        declarations,
        owners,
    )
}

fn reference_reaches_owner_with_aliases(
    source: &str,
    carrier: &str,
    reference: &str,
    aliases: &BTreeMap<String, String>,
    declarations: &BTreeMap<String, Vec<CarrierId>>,
    owners: &BTreeSet<CarrierId>,
) -> bool {
    fn resolved_ownership(candidates: &[&CarrierId], owners: &BTreeSet<CarrierId>) -> bool {
        assert_eq!(
            candidates.len(),
            1,
            "carrier reference must resolve to exactly one declaration: {candidates:?}",
        );
        owners.contains(candidates[0])
    }

    fn resolve(
        current: &CarrierId,
        reference: &str,
        aliases: &BTreeMap<String, String>,
        declarations: &BTreeMap<String, Vec<CarrierId>>,
        owners: &BTreeSet<CarrierId>,
        visited: &mut BTreeSet<String>,
        selected: bool,
    ) -> bool {
        if reference == "Self" {
            assert!(
                declarations
                    .values()
                    .flatten()
                    .any(|candidate| candidate == current),
                "Self carrier reference has no enclosing declaration {current:?}",
            );
            return owners.contains(current);
        }
        if aliases
            .get(reference)
            .is_some_and(|target| target == "$generic")
        {
            return false;
        }
        if let Some((prefix, suffix)) = reference.split_once("::")
            && !matches!(prefix, "crate" | "self" | "super")
            && let Some(target) = aliases.get(prefix)
        {
            assert_ne!(
                target, "$generic",
                "a generic parameter cannot be a path prefix"
            );
            let expanded = format!("{target}::{suffix}");
            assert!(
                visited.insert(reference.to_owned()),
                "cyclic import alias while resolving {reference}",
            );
            return resolve(
                current,
                &expanded,
                aliases,
                declarations,
                owners,
                visited,
                matches!(target.split("::").next(), Some("crate" | "self" | "super")),
            );
        }
        let terminal = reference.rsplit("::").next().unwrap_or(reference);
        let Some(candidates) = declarations.get(terminal) else {
            if let Some(target) = aliases.get(reference) {
                assert!(
                    visited.insert(reference.to_owned()),
                    "cyclic import alias while resolving {reference}",
                );
                return resolve(
                    current,
                    target,
                    aliases,
                    declarations,
                    owners,
                    visited,
                    matches!(target.split("::").next(), Some("crate" | "self" | "super")),
                );
            }
            assert!(
                !aliases.contains_key("*"),
                "a visible glob import can bind unresolved carrier reference {reference}",
            );
            assert!(
                !selected,
                "selected carrier reference {reference} does not resolve",
            );
            return false;
        };
        if reference.contains("::")
            && !reference.starts_with("crate::")
            && !reference.starts_with("self::")
            && !reference.starts_with("super::")
        {
            let relative = qualified_reference_crate_path(
                &current.source,
                &current.name,
                &format!("self::{reference}"),
            )
            .expect("a self-qualified path is crate-relative");
            let exact = candidates
                .iter()
                .filter(|candidate| {
                    let path = carrier_crate_path(candidate);
                    path == relative || path == reference
                })
                .collect::<Vec<_>>();
            return if exact.is_empty() {
                false
            } else {
                resolved_ownership(&exact, owners)
            };
        }
        if let Some(expected) =
            qualified_reference_crate_path(&current.source, &current.name, reference)
        {
            let exact = candidates
                .iter()
                .filter(|candidate| carrier_crate_path(candidate) == expected)
                .collect::<Vec<_>>();
            if !exact.is_empty() {
                return resolved_ownership(&exact, owners);
            }
            assert!(
                !exact.is_empty(),
                "qualified carrier reference {reference} does not resolve"
            );
            unreachable!("the exact qualified carrier was returned above");
        }
        let carrier_module = current
            .name
            .rsplit_once("::")
            .map_or("", |(module, _)| module);
        let mut local = candidates
            .iter()
            .filter(|candidate| {
                let candidate_module = candidate
                    .name
                    .rsplit_once("::")
                    .map_or("", |(module, _)| module);
                candidate.source == current.source
                    && (candidate_module.is_empty()
                        || candidate_module == carrier_module
                        || (!candidate_module.is_empty()
                            && carrier_module.starts_with(&format!("{candidate_module}::"))))
            })
            .collect::<Vec<_>>();
        if !local.is_empty() {
            let nearest = local
                .iter()
                .map(|candidate| candidate.name.matches("::").count())
                .max()
                .expect("a local candidate exists");
            local.retain(|candidate| candidate.name.matches("::").count() == nearest);
            return resolved_ownership(&local, owners);
        }
        if let Some(target) = aliases.get(reference) {
            assert!(
                visited.insert(reference.to_owned()),
                "cyclic import alias while resolving {reference}",
            );
            return resolve(
                current,
                target,
                aliases,
                declarations,
                owners,
                visited,
                matches!(target.split("::").next(), Some("crate" | "self" | "super")),
            );
        }
        assert!(
            !aliases.contains_key("*"),
            "a visible glob import can bind ambiguous carrier reference {reference}",
        );
        assert!(
            !candidates.iter().any(|candidate| {
                candidate.source == current.source
                    && candidate.name.contains("$fn_")
                    && current.name.contains("$fn_")
            }),
            "lexically scoped carrier reference {reference} is not visible from {}",
            current.name,
        );
        assert_eq!(
            candidates.len(),
            1,
            "ambiguous carrier reference {reference} from {}::{}; visible aliases: {aliases:?}",
            current.source,
            current.name,
        );
        resolved_ownership(&candidates.iter().collect::<Vec<_>>(), owners)
    }

    let selected = reference.starts_with("crate::")
        || reference.starts_with("self::")
        || reference.starts_with("super::")
        || aliases.contains_key(reference);
    let current = CarrierId {
        source: source.to_owned(),
        name: carrier.to_owned(),
    };
    resolve(
        &current,
        reference,
        aliases,
        declarations,
        owners,
        &mut BTreeSet::new(),
        selected,
    )
}

fn carrier_crate_path(carrier: &CarrierId) -> String {
    let source = carrier
        .source
        .strip_prefix("src/")
        .unwrap_or(&carrier.source);
    let module = source
        .strip_suffix("/mod.rs")
        .or_else(|| source.strip_suffix(".rs"))
        .unwrap_or(source);
    let module = if module == "lib" { "" } else { module };
    let module = module.replace('/', "::");
    if module.is_empty() {
        carrier.name.clone()
    } else {
        format!("{module}::{}", carrier.name)
    }
}

fn qualified_reference_crate_path(source: &str, carrier: &str, reference: &str) -> Option<String> {
    if let Some(reference) = reference.strip_prefix("crate::") {
        return Some(reference.to_owned());
    }
    let mut reference = reference;
    let mut module = source
        .strip_prefix("src/")
        .unwrap_or(source)
        .strip_suffix("/mod.rs")
        .or_else(|| {
            source
                .strip_prefix("src/")
                .unwrap_or(source)
                .strip_suffix(".rs")
        })
        .unwrap_or(source)
        .split('/')
        .filter(|segment| !segment.is_empty() && *segment != "lib")
        .collect::<Vec<_>>();
    if let Some((carrier_module, _)) = carrier.rsplit_once("::") {
        module.extend(
            carrier_module
                .split("::")
                .filter(|segment| !segment.starts_with('$')),
        );
    }
    if let Some(rest) = reference.strip_prefix("self::") {
        reference = rest;
    } else if reference.starts_with("super::") {
        while let Some(rest) = reference.strip_prefix("super::") {
            assert!(
                module.pop().is_some(),
                "qualified carrier reference {reference} escapes the crate root",
            );
            reference = rest;
        }
    } else {
        return None;
    }
    module.extend(reference.split("::"));
    Some(module.join("::"))
}

#[test]
fn carrier_scanner_includes_aliases_and_does_not_conflate_ambiguous_names() {
    let aliases = parse_top_level_fields(
        "src/alias.rs",
        "type TypeBucket = std::collections::HashMap<u32, Type>;",
    );
    assert_eq!(aliases.len(), 1);
    assert_eq!(aliases[0].key(), "src/alias.rs::TypeBucket.$alias");
    assert!(aliases[0].references.contains("Type"));

    let bounded = parse_top_level_fields(
        "src/bounded.rs",
        "struct Tuple<F: Fn(Type)>(F); struct Named<F> where F: Fn(Type) { retained: Type, plain: F }",
    );
    assert_eq!(
        bounded.iter().map(ProductionField::key).collect::<Vec<_>>(),
        [
            "src/bounded.rs::Tuple.0",
            "src/bounded.rs::Named.retained",
            "src/bounded.rs::Named.plain",
        ]
    );
    assert!(!bounded[0].references.contains("Type"));
    assert!(bounded[1].references.contains("Type"));

    let candidates = BTreeMap::from([(
        "Task".to_owned(),
        vec![
            CarrierId {
                source: "src/owned.rs".to_owned(),
                name: "Task".to_owned(),
            },
            CarrierId {
                source: "src/plain.rs".to_owned(),
                name: "Task".to_owned(),
            },
        ],
    )]);
    let owners = BTreeSet::from([CarrierId {
        source: "src/owned.rs".to_owned(),
        name: "Task".to_owned(),
    }]);
    assert!(reference_reaches_owner(
        "src/owned.rs",
        "Task",
        "Task",
        &candidates,
        &owners,
    ));
    assert!(!reference_reaches_owner(
        "src/plain.rs",
        "Task",
        "Task",
        &candidates,
        &owners,
    ));
    assert!(
        std::panic::catch_unwind(|| reference_reaches_owner(
            "src/external.rs",
            "External",
            "Task",
            &candidates,
            &owners,
        ))
        .is_err(),
        "mixed unqualified candidates must fail closed",
    );
    let uniformly_owned = BTreeMap::from([(
        "Task".to_owned(),
        vec![
            CarrierId {
                source: "src/owned_one.rs".to_owned(),
                name: "Task".to_owned(),
            },
            CarrierId {
                source: "src/owned_two.rs".to_owned(),
                name: "Task".to_owned(),
            },
        ],
    )]);
    let uniformly_owned_set = uniformly_owned["Task"].iter().cloned().collect();
    assert!(
        std::panic::catch_unwind(|| reference_reaches_owner(
            "src/external.rs",
            "External",
            "Task",
            &uniformly_owned,
            &uniformly_owned_set,
        ))
        .is_err(),
        "multiple owning terminal candidates must remain ambiguous",
    );
    let uniformly_plain = BTreeMap::from([(
        "Task".to_owned(),
        vec![
            CarrierId {
                source: "src/plain_one.rs".to_owned(),
                name: "Task".to_owned(),
            },
            CarrierId {
                source: "src/plain_two.rs".to_owned(),
                name: "Task".to_owned(),
            },
        ],
    )]);
    assert!(
        std::panic::catch_unwind(|| reference_reaches_owner(
            "src/external.rs",
            "External",
            "Task",
            &uniformly_plain,
            &BTreeSet::new(),
        ))
        .is_err(),
        "multiple plain terminal candidates must remain ambiguous",
    );
    assert!(reference_reaches_owner(
        "src/external.rs",
        "External",
        "crate::owned::Task",
        &candidates,
        &owners,
    ));
    assert!(!reference_reaches_owner(
        "src/external.rs",
        "External",
        "crate::plain::Task",
        &candidates,
        &owners,
    ));

    let inline_candidates = BTreeMap::from([(
        "Task".to_owned(),
        vec![
            CarrierId {
                source: "src/container.rs".to_owned(),
                name: "owned::Task".to_owned(),
            },
            CarrierId {
                source: "src/container.rs".to_owned(),
                name: "plain::Task".to_owned(),
            },
        ],
    )]);
    let inline_owners = BTreeSet::from([CarrierId {
        source: "src/container.rs".to_owned(),
        name: "owned::Task".to_owned(),
    }]);
    assert!(reference_reaches_owner(
        "src/container.rs",
        "owned::Holder",
        "Task",
        &inline_candidates,
        &inline_owners,
    ));
    assert!(!reference_reaches_owner(
        "src/container.rs",
        "plain::Holder",
        "Task",
        &inline_candidates,
        &inline_owners,
    ));

    let qualified = parse_top_level_fields(
        "src/external.rs",
        "struct Qualified { owned: crate::owned::Task, plain: crate::plain::Task }",
    );
    assert!(qualified[0].references.contains("crate::owned::Task"));
    assert!(!qualified[0].references.contains("Task"));
    assert!(qualified[1].references.contains("crate::plain::Task"));
    assert!(!qualified[1].references.contains("Task"));

    let imported_aliases = parse_top_level_fields(
        "src/external.rs",
        "use crate::owned::Task as OwnedTask; \
         use crate::plain::Task as PlainTask; \
         struct Holder { owned: OwnedTask, plain: PlainTask }",
    );
    assert!(imported_aliases[0].references.contains("OwnedTask"));
    assert!(imported_aliases[1].references.contains("PlainTask"));
    assert!(reference_reaches_owner_with_aliases(
        "src/external.rs",
        "Holder",
        imported_aliases[0]
            .references
            .first()
            .expect("the owned alias should resolve"),
        &imported_aliases[0].aliases,
        &candidates,
        &owners,
    ));
    assert!(!reference_reaches_owner_with_aliases(
        "src/external.rs",
        "Holder",
        imported_aliases[1]
            .references
            .first()
            .expect("the plain alias should resolve"),
        &imported_aliases[1].aliases,
        &candidates,
        &owners,
    ));
    assert!(
        std::panic::catch_unwind(|| reference_reaches_owner(
            "src/external.rs",
            "Holder",
            "crate::missing::Task",
            &candidates,
            &owners,
        ))
        .is_err(),
        "a selected missing alias target must fail closed",
    );
    assert!(
        std::panic::catch_unwind(|| reference_reaches_owner_with_aliases(
            "src/external.rs",
            "Holder",
            "MissingAlias",
            &BTreeMap::from([("MissingAlias".to_owned(), "crate::absent::Ghost".to_owned(),)]),
            &candidates,
            &owners,
        ))
        .is_err(),
        "an alias whose selected terminal is absent must fail closed",
    );
    assert!(
        std::panic::catch_unwind(|| {
            resolve_import_alias(
                "OwnedTask",
                &BTreeMap::from([
                    ("OwnedTask".to_owned(), "OtherTask".to_owned()),
                    ("OtherTask".to_owned(), "OwnedTask".to_owned()),
                ]),
            )
        })
        .is_err(),
        "cyclic aliases must fail closed",
    );

    let inline = parse_top_level_fields(
        "src/container.rs",
        "mod nested { struct Holder(crate::owned::Task); type Bucket = crate::plain::Task; }",
    );
    assert_eq!(
        inline.iter().map(ProductionField::key).collect::<Vec<_>>(),
        [
            "src/container.rs::nested::Holder.0",
            "src/container.rs::nested::Bucket.$alias",
        ]
    );
    assert!(inline[0].references.contains("crate::owned::Task"));
    assert!(inline[1].references.contains("crate::plain::Task"));

    let scoped = parse_top_level_fields(
        "src/lib.rs",
        "mod owned { struct Alias(Type); struct Holder(Alias); } \
         mod plain { struct Task(u32); use crate::plain::Task as Alias; struct Holder(Alias); }",
    );
    let scoped_declarations = declaration_index(&scoped);
    let scoped_owners = BTreeSet::from([CarrierId {
        source: "src/lib.rs".to_owned(),
        name: "owned::Alias".to_owned(),
    }]);
    let owned_holder = scoped
        .iter()
        .find(|field| field.key() == "src/lib.rs::owned::Holder.0")
        .expect("the owning holder should be discovered");
    let plain_holder = scoped
        .iter()
        .find(|field| field.key() == "src/lib.rs::plain::Holder.0")
        .expect("the plain holder should be discovered");
    assert!(reference_reaches_owner_with_aliases(
        &owned_holder.source,
        &owned_holder.carrier,
        "Alias",
        &owned_holder.aliases,
        &scoped_declarations,
        &scoped_owners,
    ));
    assert!(!reference_reaches_owner_with_aliases(
        &plain_holder.source,
        &plain_holder.carrier,
        "Alias",
        &plain_holder.aliases,
        &scoped_declarations,
        &scoped_owners,
    ));

    let grouped = parse_top_level_fields(
        "src/lib.rs",
        "mod owned { struct Task(Type); } \
         mod plain { struct Task(u32); } \
         mod external { \
             use crate::{owned::Task as OwnedTask, plain::{Task as PlainTask}}; \
             struct Holder { owned: OwnedTask, plain: PlainTask } \
         }",
    );
    let grouped_declarations = declaration_index(&grouped);
    let grouped_owners = BTreeSet::from([CarrierId {
        source: "src/lib.rs".to_owned(),
        name: "owned::Task".to_owned(),
    }]);
    let grouped_owned = grouped
        .iter()
        .find(|field| field.key() == "src/lib.rs::external::Holder.owned")
        .expect("the grouped owned alias should be discovered");
    let grouped_plain = grouped
        .iter()
        .find(|field| field.key() == "src/lib.rs::external::Holder.plain")
        .expect("the grouped plain alias should be discovered");
    assert!(reference_reaches_owner_with_aliases(
        &grouped_owned.source,
        &grouped_owned.carrier,
        "OwnedTask",
        &grouped_owned.aliases,
        &grouped_declarations,
        &grouped_owners,
    ));
    assert!(!reference_reaches_owner_with_aliases(
        &grouped_plain.source,
        &grouped_plain.carrier,
        "PlainTask",
        &grouped_plain.aliases,
        &grouped_declarations,
        &grouped_owners,
    ));

    let relative = parse_top_level_fields(
        "src/lib.rs",
        "mod owned { \
             struct Task(Type); \
             mod nested { use super::Task as Alias; struct Holder(Alias); } \
         }",
    );
    let relative_declarations = declaration_index(&relative);
    let relative_owners = BTreeSet::from([CarrierId {
        source: "src/lib.rs".to_owned(),
        name: "owned::Task".to_owned(),
    }]);
    let relative_holder = relative
        .iter()
        .find(|field| field.key() == "src/lib.rs::owned::nested::Holder.0")
        .expect("the relative alias holder should be discovered");
    assert!(reference_reaches_owner_with_aliases(
        &relative_holder.source,
        &relative_holder.carrier,
        "Alias",
        &relative_holder.aliases,
        &relative_declarations,
        &relative_owners,
    ));

    let glob = parse_top_level_fields("src/glob.rs", "use crate::owned::*; struct Holder(Task);");
    assert!(
        std::panic::catch_unwind(|| reference_reaches_owner_with_aliases(
            &glob[0].source,
            &glob[0].carrier,
            "Task",
            &glob[0].aliases,
            &candidates,
            &owners,
        ))
        .is_err(),
        "a visible unsupported glob that could bind a carrier must fail closed",
    );

    let local_over_import = parse_top_level_fields(
        "src/lib.rs",
        "mod plain { struct Task(u32); } \
         use crate::plain::Task as Alias; \
         fn retain_local() { struct Alias(Type); struct Holder(Alias); }",
    );
    let local_declarations = declaration_index(&local_over_import);
    let local_owners = BTreeSet::from([CarrierId {
        source: "src/lib.rs".to_owned(),
        name: "$fn_retain_local::Alias".to_owned(),
    }]);
    let local_holder = local_over_import
        .iter()
        .find(|field| field.key() == "src/lib.rs::$fn_retain_local::Holder.0")
        .expect("the local holder should be discovered");
    assert!(reference_reaches_owner_with_aliases(
        &local_holder.source,
        &local_holder.carrier,
        "Alias",
        &local_holder.aliases,
        &local_declarations,
        &local_owners,
    ));

    let production_tests_module = parse_top_level_fields(
        "src/container.rs",
        "mod tests { struct Production(crate::owned::Task); }",
    );
    assert_eq!(
        production_tests_module[0].key(),
        "src/container.rs::tests::Production.0"
    );
    let cfg_test_module = parse_top_level_fields(
        "src/container.rs",
        "#[cfg(test)] mod checks { struct Fixture(crate::owned::Task); }",
    );
    assert!(cfg_test_module.is_empty());

    let associated = parse_top_level_fields(
        "src/associated.rs",
        "impl Owned { fn discard_iteratively() { struct Task(Type); } } \
         impl Plain { fn discard_iteratively() { struct Task(u32); } }",
    );
    assert_eq!(
        associated
            .iter()
            .map(ProductionField::key)
            .collect::<Vec<_>>(),
        [
            "src/associated.rs::$impl_Owned::$fn_discard_iteratively::Task.0",
            "src/associated.rs::$impl_Plain::$fn_discard_iteratively::Task.0",
        ],
    );

    let sibling_shadows = parse_top_level_fields(
        "src/shadow.rs",
        "fn inspect() { if true { struct Task(Type); } if false { struct Task(u32); } }",
    );
    assert_eq!(sibling_shadows.len(), 2);
    assert_ne!(sibling_shadows[0].carrier, sibling_shadows[1].carrier);

    let sibling_blocks = parse_top_level_fields(
        "src/sibling.rs",
        "fn inspect() { if true { struct Task(Type); } if false { struct Holder(Task); } }",
    );
    let sibling_declarations = declaration_index(&sibling_blocks);
    let sibling_owners = BTreeSet::from([CarrierId {
        source: "src/sibling.rs".to_owned(),
        name: "$fn_inspect::Task".to_owned(),
    }]);
    let sibling_holder = sibling_blocks
        .iter()
        .find(|field| field.field == "0" && field.carrier.ends_with("Holder"))
        .expect("the sibling holder should be discovered");
    assert!(
        std::panic::catch_unwind(|| reference_reaches_owner_with_aliases(
            &sibling_holder.source,
            &sibling_holder.carrier,
            "Task",
            &sibling_holder.aliases,
            &sibling_declarations,
            &sibling_owners,
        ))
        .is_err(),
        "a declaration in one sibling block must not resolve in another sibling block",
    );

    let generic_shadow =
        parse_top_level_fields("src/generic.rs", "struct T(Type); struct Holder<T>(T);");
    let generic_declarations = declaration_index(&generic_shadow);
    let generic_owners = BTreeSet::from([CarrierId {
        source: "src/generic.rs".to_owned(),
        name: "T".to_owned(),
    }]);
    let generic_holder = generic_shadow
        .iter()
        .find(|field| field.carrier == "Holder")
        .expect("the generic holder should be discovered");
    assert!(
        !reference_reaches_owner_with_aliases(
            &generic_holder.source,
            &generic_holder.carrier,
            "T",
            &generic_holder.aliases,
            &generic_declarations,
            &generic_owners,
        ),
        "a declaration generic must shadow a same-named owning carrier",
    );

    let prefix_alias = parse_top_level_fields(
        "src/lib.rs",
        "mod owned { struct Task(Type); } mod plain { struct Task(u32); } \
         mod selected { use crate::owned as chosen; struct Holder(chosen::Task); }",
    );
    let prefix_declarations = declaration_index(&prefix_alias);
    let prefix_owners = BTreeSet::from([CarrierId {
        source: "src/lib.rs".to_owned(),
        name: "owned::Task".to_owned(),
    }]);
    let prefix_holder = prefix_alias
        .iter()
        .find(|field| field.key() == "src/lib.rs::selected::Holder.0")
        .expect("the prefix-alias holder should be discovered");
    assert!(reference_reaches_owner_with_aliases(
        &prefix_holder.source,
        &prefix_holder.carrier,
        "chosen::Task",
        &prefix_holder.aliases,
        &prefix_declarations,
        &prefix_owners,
    ));

    let absent_reexport = parse_top_level_fields(
        "src/lib.rs",
        "mod foo { mod nested { struct Task(Type); } struct Holder(crate::foo::Task); }",
    );
    let absent_declarations = declaration_index(&absent_reexport);
    let absent_owners = BTreeSet::from([CarrierId {
        source: "src/lib.rs".to_owned(),
        name: "foo::nested::Task".to_owned(),
    }]);
    let absent_holder = absent_reexport
        .iter()
        .find(|field| field.key() == "src/lib.rs::foo::Holder.0")
        .expect("the absent-reexport holder should be discovered");
    assert!(
        std::panic::catch_unwind(|| reference_reaches_owner_with_aliases(
            &absent_holder.source,
            &absent_holder.carrier,
            "crate::foo::Task",
            &absent_holder.aliases,
            &absent_declarations,
            &absent_owners,
        ))
        .is_err(),
        "a descendant declaration must not masquerade as an absent exact reexport",
    );

    let root_group = parse_top_level_fields(
        "src/lib.rs",
        "mod owned { struct Task(Type); } \
         use { crate::owned::Task as Alias }; struct Holder(Alias);",
    );
    let root_group_declarations = declaration_index(&root_group);
    let root_group_owners = BTreeSet::from([CarrierId {
        source: "src/lib.rs".to_owned(),
        name: "owned::Task".to_owned(),
    }]);
    let root_group_holder = root_group
        .iter()
        .find(|field| field.carrier == "Holder")
        .expect("the root-group holder should be discovered");
    assert!(reference_reaches_owner_with_aliases(
        &root_group_holder.source,
        &root_group_holder.carrier,
        "Alias",
        &root_group_holder.aliases,
        &root_group_declarations,
        &root_group_owners,
    ));

    let external = parse_top_level_fields(
        "src/lib.rs",
        "mod internal { struct Task(Type); } struct Holder(external::Task);",
    );
    let external_declarations = declaration_index(&external);
    let external_owners = BTreeSet::from([CarrierId {
        source: "src/lib.rs".to_owned(),
        name: "internal::Task".to_owned(),
    }]);
    let external_holder = external
        .iter()
        .find(|field| field.carrier == "Holder")
        .expect("the external holder should be discovered");
    assert!(!reference_reaches_owner_with_aliases(
        &external_holder.source,
        &external_holder.carrier,
        "external::Task",
        &external_holder.aliases,
        &external_declarations,
        &external_owners,
    ));
}

fn parse_top_level_fields(path: &str, source: &str) -> Vec<ProductionField> {
    let tokens = rust_code_tokens(source);
    let fields = parse_declaration_fields(path, &tokens, "");
    let mut keys = BTreeSet::new();
    for field in &fields {
        assert!(
            keys.insert(field.key()),
            "ambiguous lexical carrier identity {}",
            field.key(),
        );
    }
    fields
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ScopedImportAlias {
    scope: Vec<usize>,
    alias: String,
    target: String,
    exported: bool,
}

fn token_scope_paths(tokens: &[&str]) -> Vec<Vec<usize>> {
    let mut paths = Vec::with_capacity(tokens.len());
    let mut path = Vec::new();
    let mut child_counts = vec![0usize];
    for token in tokens {
        paths.push(path.clone());
        match *token {
            "{" => {
                let child = child_counts
                    .last_mut()
                    .expect("the root token scope remains available");
                let child = *child;
                *child_counts
                    .last_mut()
                    .expect("the root token scope remains available") += 1;
                path.push(child);
                child_counts.push(0);
            }
            "}" => {
                assert!(path.pop().is_some(), "unbalanced Rust token scope");
                child_counts.pop();
            }
            _ => {}
        }
    }
    assert!(path.is_empty(), "unbalanced Rust token scope at EOF");
    paths
}

fn scoped_import_aliases(tokens: &[&str], scopes: &[Vec<usize>]) -> Vec<ScopedImportAlias> {
    fn collect_use_tree(
        tree: &[&str],
        prefix: &[String],
        scope: &[usize],
        exported: bool,
        aliases: &mut Vec<ScopedImportAlias>,
    ) {
        if tree.is_empty() {
            return;
        }
        if tree.contains(&"*") {
            aliases.push(ScopedImportAlias {
                scope: scope.to_vec(),
                alias: "*".to_owned(),
                target: "$unsupported_glob".to_owned(),
                exported,
            });
            return;
        }
        if let Some(open) = top_level_position(tree, "{") {
            let close = matching_token(tree, open, "{", "}");
            let mut nested_prefix = prefix.to_vec();
            nested_prefix.extend(
                tree[..open]
                    .iter()
                    .copied()
                    .filter(|token| is_rust_identifier(token) && *token != "as")
                    .map(str::to_owned),
            );
            for child in split_top_level(&tree[open + 1..close], ",") {
                collect_use_tree(child, &nested_prefix, scope, exported, aliases);
            }
            return;
        }

        let alias_position = tree.iter().position(|token| *token == "as");
        let path_tokens = alias_position.map_or(tree, |index| &tree[..index]);
        let mut segments = prefix.to_vec();
        let leaf = path_tokens
            .iter()
            .copied()
            .filter(|token| is_rust_identifier(token))
            .collect::<Vec<_>>();
        if leaf == ["self"] && !segments.is_empty() {
            // A grouped `self` imports the accumulated path itself.
        } else {
            segments.extend(leaf.iter().map(|segment| (*segment).to_owned()));
        }
        let Some(default_alias) = segments.last().cloned() else {
            return;
        };
        let alias = alias_position
            .and_then(|index| tree.get(index + 1).copied())
            .filter(|alias| is_rust_identifier(alias))
            .map_or(default_alias, str::to_owned);
        aliases.push(ScopedImportAlias {
            scope: scope.to_vec(),
            alias,
            target: segments.join("::"),
            exported,
        });
    }

    let mut aliases = Vec::new();
    let mut cursor = 0usize;
    while cursor < tokens.len() {
        if tokens[cursor] != "use" {
            cursor += 1;
            continue;
        }
        let Some(end_offset) = tokens[cursor + 1..].iter().position(|token| *token == ";") else {
            break;
        };
        let declaration = &tokens[cursor + 1..cursor + 1 + end_offset];
        let scope = scopes[cursor].clone();
        let declaration_start = (0..cursor)
            .rev()
            .find(|index| matches!(tokens[*index], ";" | "{" | "}"))
            .map_or(0, |index| index + 1);
        let exported = tokens[declaration_start..cursor].contains(&"pub");
        cursor += end_offset + 2;
        if declaration.is_empty() {
            continue;
        }
        collect_use_tree(declaration, &[], &scope, exported, &mut aliases);
    }
    aliases
}

fn visible_import_aliases(
    aliases: &[ScopedImportAlias],
    scope: &[usize],
) -> BTreeMap<String, String> {
    let mut visible = BTreeMap::<String, (usize, String)>::new();
    for imported in aliases
        .iter()
        .filter(|imported| scope.starts_with(&imported.scope))
    {
        match visible.get(&imported.alias) {
            Some((depth, target)) if *depth == imported.scope.len() => assert_eq!(
                target, &imported.target,
                "duplicate import alias {} has incompatible targets",
                imported.alias,
            ),
            Some((depth, _)) if *depth > imported.scope.len() => {}
            _ => {
                visible.insert(
                    imported.alias.clone(),
                    (imported.scope.len(), imported.target.clone()),
                );
            }
        }
    }
    visible
        .into_iter()
        .map(|(alias, (_, target))| (alias, target))
        .collect()
}

fn resolve_import_alias(reference: &str, aliases: &BTreeMap<String, String>) -> String {
    if reference.contains("::") {
        return reference.to_owned();
    }
    let mut current = reference.to_owned();
    let mut visited = BTreeSet::new();
    while let Some(target) = aliases.get(&current) {
        assert!(
            visited.insert(current.clone()),
            "cyclic import alias while resolving {reference}",
        );
        current = target.clone();
    }
    current
}

fn parse_declaration_fields(
    path: &str,
    tokens: &[&str],
    module_prefix: &str,
) -> Vec<ProductionField> {
    let scopes = token_scope_paths(tokens);
    let imports = scoped_import_aliases(tokens, &scopes);
    let mut fields = Vec::new();
    for imported in imports.iter().filter(|imported| {
        imported.exported
            && imported.scope.is_empty()
            && imported.alias != "*"
            && imported
                .alias
                .as_bytes()
                .first()
                .is_some_and(u8::is_ascii_uppercase)
            && imported.alias.bytes().any(|byte| byte.is_ascii_lowercase())
    }) {
        fields.push(ProductionField {
            source: path.to_owned(),
            carrier: qualify_declaration(module_prefix, &imported.alias),
            field: "$alias".to_owned(),
            references: BTreeSet::from([imported.target.clone()]),
            reference_retentions: BTreeMap::from([(
                imported.target.clone(),
                RetentionSet::owned(),
            )]),
            aliases: BTreeMap::new(),
        });
    }
    let mut cursor = 0usize;
    let mut lexical_scopes = Vec::new();
    while cursor < tokens.len() {
        match tokens[cursor] {
            "{" => {
                lexical_scopes.push(classify_lexical_scope(
                    tokens,
                    cursor,
                    scopes.get(cursor + 1).map_or(&[][..], Vec::as_slice),
                ));
                cursor += 1;
            }
            "}" => {
                lexical_scopes.pop();
                cursor += 1;
            }
            "struct" | "enum" => {
                let family = tokens[cursor];
                let Some(name) = tokens.get(cursor + 1).copied() else {
                    break;
                };
                let carrier = qualify_lexical_declaration(module_prefix, &lexical_scopes, name);
                let mut aliases = visible_import_aliases(&imports, &scopes[cursor]);
                let Some((open, delimiter)) = declaration_delimiter(tokens, cursor + 2) else {
                    break;
                };
                for generic in declaration_generic_parameters(&tokens[cursor + 2..open]) {
                    aliases.insert(generic, "$generic".to_owned());
                }
                match (family, delimiter) {
                    (_, ";") => {
                        fields.push(ProductionField {
                            source: path.to_owned(),
                            carrier,
                            field: "$declaration".to_owned(),
                            references: BTreeSet::new(),
                            reference_retentions: BTreeMap::new(),
                            aliases,
                        });
                        cursor = open + 1;
                    }
                    ("struct", "{") => {
                        let close = matching_token(tokens, open, "{", "}");
                        fields.extend(parse_named_fields(
                            path,
                            &carrier,
                            "",
                            &tokens[open + 1..close],
                            &aliases,
                        ));
                        cursor = close + 1;
                    }
                    ("struct", "(") => {
                        let close = matching_token(tokens, open, "(", ")");
                        fields.extend(parse_tuple_fields(
                            path,
                            &carrier,
                            "",
                            &tokens[open + 1..close],
                            &aliases,
                        ));
                        cursor = close + 1;
                    }
                    ("enum", "{") => {
                        let close = matching_token(tokens, open, "{", "}");
                        let parsed =
                            parse_enum_fields(path, &carrier, &tokens[open + 1..close], &aliases);
                        if parsed.is_empty() {
                            fields.push(ProductionField {
                                source: path.to_owned(),
                                carrier,
                                field: "$declaration".to_owned(),
                                references: BTreeSet::new(),
                                reference_retentions: BTreeMap::new(),
                                aliases,
                            });
                        } else {
                            fields.extend(parsed);
                        }
                        cursor = close + 1;
                    }
                    _ => cursor = open + 1,
                }
            }
            "type" => {
                let Some(name) = tokens.get(cursor + 1).copied() else {
                    break;
                };
                let carrier = qualify_lexical_declaration(module_prefix, &lexical_scopes, name);
                let aliases = visible_import_aliases(&imports, &scopes[cursor]);
                let tail = &tokens[cursor + 2..];
                let Some(semicolon_offset) = top_level_position(tail, ";") else {
                    break;
                };
                let declaration = &tail[..semicolon_offset];
                if !in_associated_item_scope(&lexical_scopes)
                    && let Some(equals) = top_level_position(declaration, "=")
                {
                    let reference_retentions =
                        type_reference_retentions(&declaration[equals + 1..], &aliases);
                    fields.push(ProductionField {
                        source: path.to_owned(),
                        carrier,
                        field: "$alias".to_owned(),
                        references: reference_retentions.keys().cloned().collect(),
                        reference_retentions,
                        aliases,
                    });
                }
                cursor += semicolon_offset + 3;
            }
            "mod" => {
                let Some(name) = tokens.get(cursor + 1).copied() else {
                    break;
                };
                let Some(open_offset) = tokens[cursor + 2..]
                    .iter()
                    .position(|token| *token == "{" || *token == ";")
                else {
                    break;
                };
                let open = cursor + 2 + open_offset;
                if tokens[open] == ";" {
                    cursor = open + 1;
                    continue;
                }
                let close = matching_token(tokens, open, "{", "}");
                if has_direct_cfg_test_attribute(tokens, cursor) {
                    cursor = close + 1;
                    continue;
                }
                let nested_prefix =
                    qualify_lexical_declaration(module_prefix, &lexical_scopes, name);
                fields.extend(parse_declaration_fields(
                    path,
                    &tokens[open + 1..close],
                    &nested_prefix,
                ));
                cursor = close + 1;
            }
            _ => cursor += 1,
        }
    }
    fields
}

fn qualify_lexical_declaration(
    module_prefix: &str,
    lexical_scopes: &[LexicalScope],
    name: &str,
) -> String {
    let mut prefix = module_prefix.to_owned();
    for scope in lexical_scopes {
        match scope {
            LexicalScope::Function(function) => {
                prefix = qualify_declaration(&prefix, &format!("$fn_{function}"));
            }
            LexicalScope::Associated(owner) => {
                prefix = qualify_declaration(&prefix, owner);
            }
            LexicalScope::Other(identity) => {
                prefix = qualify_declaration(&prefix, &format!("$block_{identity}"));
            }
        }
    }
    qualify_declaration(&prefix, name)
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum LexicalScope {
    Function(String),
    Associated(String),
    Other(String),
}

fn classify_lexical_scope(tokens: &[&str], open: usize, identity: &[usize]) -> LexicalScope {
    let start = (0..open)
        .rev()
        .find(|index| matches!(tokens[*index], "{" | "}" | ";"))
        .map_or(0, |index| index + 1);
    let header = &tokens[start..open];
    if let Some(function) = header
        .iter()
        .position(|token| *token == "fn")
        .and_then(|index| header.get(index + 1))
        .filter(|name| is_rust_identifier(name))
    {
        LexicalScope::Function((*function).to_owned())
    } else if let Some(index) = header.iter().position(|token| *token == "trait") {
        let owner = header
            .get(index + 1)
            .filter(|name| is_rust_identifier(name))
            .copied()
            .unwrap_or("unknown");
        LexicalScope::Associated(format!("$trait_{owner}"))
    } else if let Some(index) = header.iter().position(|token| *token == "impl") {
        let mut tail = &header[index + 1..];
        if tail.first() == Some(&"<") {
            let close = matching_token(tail, 0, "<", ">");
            tail = &tail[close + 1..];
        }
        let mut angle_depth = 0usize;
        let mut owner_parts = Vec::new();
        for token in tail.iter().copied() {
            match token {
                "<" => angle_depth += 1,
                ">" => angle_depth = angle_depth.saturating_sub(1),
                "where" if angle_depth == 0 => break,
                _ if angle_depth == 0 && is_rust_identifier(token) => owner_parts.push(token),
                _ => {}
            }
        }
        let owner = owner_parts.join("_");
        LexicalScope::Associated(format!(
            "$impl_{}",
            if owner.is_empty() { "unknown" } else { &owner }
        ))
    } else {
        LexicalScope::Other(
            identity
                .iter()
                .map(usize::to_string)
                .collect::<Vec<_>>()
                .join("_"),
        )
    }
}

fn declaration_generic_parameters(tokens: &[&str]) -> BTreeSet<String> {
    if tokens.first() != Some(&"<") {
        return BTreeSet::new();
    }
    let close = matching_token(tokens, 0, "<", ">");
    split_top_level(&tokens[1..close], ",")
        .into_iter()
        .filter_map(|parameter| {
            parameter
                .iter()
                .copied()
                .find(|token| is_rust_identifier(token) && !matches!(*token, "const"))
                .map(str::to_owned)
        })
        .collect()
}

fn in_associated_item_scope(scopes: &[LexicalScope]) -> bool {
    scopes
        .iter()
        .rev()
        .find(|scope| {
            matches!(
                scope,
                LexicalScope::Function(_) | LexicalScope::Associated(_)
            )
        })
        .is_some_and(|scope| matches!(scope, LexicalScope::Associated(_)))
}

fn qualify_declaration(module_prefix: &str, name: &str) -> String {
    if module_prefix.is_empty() {
        name.to_owned()
    } else {
        format!("{module_prefix}::{name}")
    }
}

fn has_direct_cfg_test_attribute(tokens: &[&str], declaration: usize) -> bool {
    const ATTRIBUTE: [&str; 7] = ["#", "[", "cfg", "(", "test", ")", "]"];
    declaration >= ATTRIBUTE.len()
        && tokens[declaration - ATTRIBUTE.len()..declaration] == ATTRIBUTE
}

fn type_reference_retentions(
    tokens: &[&str],
    aliases: &BTreeMap<String, String>,
) -> BTreeMap<String, RetentionSet> {
    fn compose(outer: RetentionMode, wrapper: RetentionMode) -> RetentionMode {
        match (outer, wrapper) {
            (RetentionMode::Borrowed, _) | (_, RetentionMode::Borrowed) => RetentionMode::Borrowed,
            (RetentionMode::Shared, _) | (_, RetentionMode::Shared) => RetentionMode::Shared,
            _ => RetentionMode::Owned,
        }
    }

    fn singleton(mode: RetentionMode) -> RetentionSet {
        match mode {
            RetentionMode::Owned => RetentionSet(RetentionSet::OWNED),
            RetentionMode::Shared => RetentionSet(RetentionSet::SHARED),
            RetentionMode::Borrowed => RetentionSet(RetentionSet::BORROWED),
            RetentionMode::Mixed => unreachable!("a single syntax path has one retention mode"),
        }
    }

    fn wrapper_mode(path: &str, aliases: &BTreeMap<String, String>) -> RetentionMode {
        let first = path.split("::").next().unwrap_or(path);
        let resolved = aliases.get(first).map_or_else(
            || path.to_owned(),
            |target| {
                path.strip_prefix(first)
                    .map_or_else(|| target.clone(), |suffix| format!("{target}{suffix}"))
            },
        );
        if matches!(
            resolved.as_str(),
            "std::sync::Arc" | "alloc::sync::Arc" | "std::rc::Rc" | "alloc::rc::Rc"
        ) {
            RetentionMode::Shared
        } else if [
            "std::slice::",
            "core::slice::",
            "std::collections::hash_map::",
            "std::collections::hash_set::",
            "std::collections::btree_map::",
            "std::collections::btree_set::",
            "alloc::collections::btree_map::",
            "alloc::collections::btree_set::",
        ]
        .iter()
        .any(|prefix| resolved.starts_with(prefix))
            && matches!(
                resolved.rsplit("::").next(),
                Some("Iter" | "IterMut" | "Keys" | "Values" | "ValuesMut")
            )
        {
            RetentionMode::Borrowed
        } else {
            RetentionMode::Owned
        }
    }

    fn merge(
        references: &mut BTreeMap<String, RetentionSet>,
        reference: String,
        mode: RetentionMode,
    ) {
        let mode = singleton(mode);
        references
            .entry(reference)
            .and_modify(|current| *current = current.union(mode))
            .or_insert(mode);
    }

    fn collect(
        mut tokens: &[&str],
        inherited: RetentionMode,
        aliases: &BTreeMap<String, String>,
        references: &mut BTreeMap<String, RetentionSet>,
    ) {
        if tokens.first() == Some(&"pub") {
            tokens = &tokens[1..];
            if tokens.first() == Some(&"(") && tokens.get(1) == Some(&"crate") {
                let close = matching_token(tokens, 0, "(", ")");
                tokens = &tokens[close + 1..];
            }
        }
        if tokens.first() == Some(&"mut") {
            tokens = &tokens[1..];
        }
        if tokens.is_empty() {
            return;
        }

        if let Some(equals) = top_level_position(tokens, "=") {
            collect(&tokens[equals + 1..], inherited, aliases, references);
            return;
        }
        let comma_parts = split_top_level(tokens, ",");
        if comma_parts.len() > 1 {
            for part in comma_parts {
                collect(part, inherited, aliases, references);
            }
            return;
        }
        if tokens[0] == "(" {
            let close = matching_token(tokens, 0, "(", ")");
            if close == tokens.len() - 1 {
                for part in split_top_level(&tokens[1..close], ",") {
                    collect(part, inherited, aliases, references);
                }
                return;
            }
        }
        if tokens[0] == "[" {
            let close = matching_token(tokens, 0, "[", "]");
            if close == tokens.len() - 1 {
                let element_end = top_level_position(&tokens[1..close], ";")
                    .map_or(close - 1, |position| position);
                collect(&tokens[1..1 + element_end], inherited, aliases, references);
                return;
            }
        }
        if tokens[0] == "&" {
            let mut start = 1;
            if tokens.get(start) == Some(&"'") {
                start += 2;
            }
            if tokens.get(start) == Some(&"mut") {
                start += 1;
            }
            collect(
                &tokens[start..],
                compose(inherited, RetentionMode::Borrowed),
                aliases,
                references,
            );
            return;
        }
        if tokens[0] == "*" {
            let start = usize::from(matches!(tokens.get(1), Some(&"const" | &"mut"))) + 1;
            collect(
                &tokens[start..],
                compose(inherited, RetentionMode::Borrowed),
                aliases,
                references,
            );
            return;
        }
        if matches!(tokens[0], "dyn" | "impl") {
            for bound in split_top_level(&tokens[1..], "+") {
                collect(bound, inherited, aliases, references);
            }
            return;
        }
        if tokens[0] == "fn" || (tokens[0] == "for" && tokens.contains(&"fn")) {
            // A function pointer stores a signature, not values of the mentioned types.
            return;
        }

        let Some(mut cursor) = tokens.iter().position(|token| is_rust_identifier(token)) else {
            return;
        };
        if tokens[cursor] == "'" {
            cursor += 2;
        }
        let Some(first) = tokens.get(cursor).copied() else {
            return;
        };
        let mut path = first.to_owned();
        let mut end = cursor;
        while end + 3 < tokens.len()
            && tokens[end + 1] == ":"
            && tokens[end + 2] == ":"
            && is_rust_identifier(tokens[end + 3])
        {
            path.push_str("::");
            path.push_str(tokens[end + 3]);
            end += 3;
        }
        if !matches!(path.as_str(), "pub" | "mut" | "const") {
            merge(references, path.clone(), inherited);
        }

        if tokens.get(end + 1) == Some(&"<") {
            let open = end + 1;
            let close = matching_token(tokens, open, "<", ">");
            let child_mode = compose(inherited, wrapper_mode(&path, aliases));
            for argument in split_top_level(&tokens[open + 1..close], ",") {
                collect(argument, child_mode, aliases, references);
            }
            if close + 1 < tokens.len() {
                collect(&tokens[close + 1..], inherited, aliases, references);
            }
        } else if end + 1 < tokens.len() {
            collect(&tokens[end + 1..], inherited, aliases, references);
        }
    }

    let mut references = BTreeMap::new();
    collect(tokens, RetentionMode::Owned, aliases, &mut references);
    references
}

fn declaration_delimiter<'a>(tokens: &[&'a str], start: usize) -> Option<(usize, &'a str)> {
    let mut angle_depth = 0usize;
    let mut in_where_clause = false;
    for (index, token) in tokens.iter().enumerate().skip(start) {
        match *token {
            "<" => angle_depth += 1,
            ">" => angle_depth = angle_depth.saturating_sub(1),
            "where" if angle_depth == 0 => in_where_clause = true,
            "{" | ";" if angle_depth == 0 => return Some((index, token)),
            "(" if angle_depth == 0 && !in_where_clause => return Some((index, token)),
            _ => {}
        }
    }
    None
}

fn parse_enum_fields(
    path: &str,
    carrier: &str,
    body: &[&str],
    aliases: &BTreeMap<String, String>,
) -> Vec<ProductionField> {
    let mut fields = Vec::new();
    for variant in split_top_level(body, ",") {
        let Some(name) = variant
            .iter()
            .copied()
            .find(|token| is_rust_identifier(token))
        else {
            continue;
        };
        if let Some(open) = variant.iter().position(|token| *token == "{") {
            let close = matching_token(variant, open, "{", "}");
            fields.extend(parse_named_fields(
                path,
                carrier,
                &format!("{name}."),
                &variant[open + 1..close],
                aliases,
            ));
        } else if let Some(open) = variant.iter().position(|token| *token == "(") {
            let close = matching_token(variant, open, "(", ")");
            fields.extend(parse_tuple_fields(
                path,
                carrier,
                &format!("{name}."),
                &variant[open + 1..close],
                aliases,
            ));
        }
    }
    fields
}

fn parse_named_fields(
    path: &str,
    carrier: &str,
    prefix: &str,
    body: &[&str],
    aliases: &BTreeMap<String, String>,
) -> Vec<ProductionField> {
    split_top_level(body, ",")
        .into_iter()
        .filter_map(|field| {
            let colon = top_level_position(field, ":")?;
            let name =
                field[..colon].iter().rev().copied().find(|token| {
                    is_rust_identifier(token) && !matches!(*token, "pub" | "crate")
                })?;
            let reference_retentions = type_reference_retentions(&field[colon + 1..], aliases);
            Some(ProductionField {
                source: path.to_owned(),
                carrier: carrier.to_owned(),
                field: format!("{prefix}{name}"),
                references: reference_retentions.keys().cloned().collect(),
                reference_retentions,
                aliases: aliases.clone(),
            })
        })
        .collect()
}

fn parse_tuple_fields(
    path: &str,
    carrier: &str,
    prefix: &str,
    body: &[&str],
    aliases: &BTreeMap<String, String>,
) -> Vec<ProductionField> {
    split_top_level(body, ",")
        .into_iter()
        .enumerate()
        .filter(|(_, field)| !field.is_empty())
        .map(|(index, field)| {
            let reference_retentions = type_reference_retentions(field, aliases);
            ProductionField {
                source: path.to_owned(),
                carrier: carrier.to_owned(),
                field: format!("{prefix}{index}"),
                references: reference_retentions.keys().cloned().collect(),
                reference_retentions,
                aliases: aliases.clone(),
            }
        })
        .collect()
}

fn split_top_level<'a>(tokens: &'a [&'a str], separator: &str) -> Vec<&'a [&'a str]> {
    let mut pieces = Vec::new();
    let mut start = 0usize;
    let mut depths = [0usize; 4];
    for (index, token) in tokens.iter().enumerate() {
        update_delimiter_depths(token, &mut depths);
        if *token == separator && depths.iter().all(|depth| *depth == 0) {
            pieces.push(&tokens[start..index]);
            start = index + 1;
        }
    }
    pieces.push(&tokens[start..]);
    pieces
}

fn top_level_position(tokens: &[&str], needle: &str) -> Option<usize> {
    let mut depths = [0usize; 4];
    for (index, token) in tokens.iter().enumerate() {
        if *token == needle && depths.iter().all(|depth| *depth == 0) {
            return Some(index);
        }
        update_delimiter_depths(token, &mut depths);
    }
    None
}

fn update_delimiter_depths(token: &str, depths: &mut [usize; 4]) {
    let (slot, opening) = match token {
        "(" => (0, true),
        ")" => (0, false),
        "[" => (1, true),
        "]" => (1, false),
        "{" => (2, true),
        "}" => (2, false),
        "<" => (3, true),
        ">" => (3, false),
        _ => return,
    };
    if opening {
        depths[slot] += 1;
    } else {
        depths[slot] = depths[slot].saturating_sub(1);
    }
}

fn matching_token(tokens: &[&str], open: usize, opening: &str, closing: &str) -> usize {
    let mut depth = 0usize;
    for (index, token) in tokens.iter().enumerate().skip(open) {
        if *token == opening {
            depth += 1;
        } else if *token == closing {
            depth -= 1;
            if depth == 0 {
                return index;
            }
        }
    }
    panic!("unbalanced Rust token sequence after {opening}")
}

fn is_rust_identifier(token: &str) -> bool {
    token
        .as_bytes()
        .first()
        .is_some_and(|first| first.is_ascii_alphabetic() || *first == b'_')
}

#[test]
fn current_source_exposes_only_one_source_pipeline() {
    assert!(
        !DRIVER_SOURCE.contains("run_source("),
        "the current driver must not retain the historical file-result pipeline"
    );
    let projection_exports = PARSER_EXPORTS
        .lines()
        .find(|line| line.trim_start().starts_with("pub use project::{"))
        .expect("the parser should publish its modular projection boundary");
    assert!(
        !projection_exports
            .trim_start_matches("pub use project::{")
            .trim_end_matches("};")
            .split(',')
            .any(|export| export.trim() == "project"),
        "the current parser must not export the historical program projection"
    );
    assert!(
        !PARSER_EXPORTS.contains("Program,")
            && !PARSER_PROJECTION.contains("SurfaceProgram")
            && !PARSER_PROJECTION.contains("pub fn project(")
            && !PARSER_PROJECTION.contains("fn project_program("),
        "the current parser must not retain a historical file-result root"
    );
    assert!(
        PARSER_EXPORTS.contains("grammar::module(&mut parser);"),
        "the public parser must enter the declarations-only module grammar"
    );
    assert!(
        PARSER_GRAMMAR.contains("&CURRENT_ASH_DIALECT"),
        "the selected grammar must be current Ash"
    );
    assert!(
        !PARSER_GRAMMAR.contains("MINI_ASH_DIALECT"),
        "the current parser must not retain a Mini-Ash grammar selector"
    );
}

#[test]
fn resolved_modules_have_one_production_kind_gate_before_construction() {
    const CONSTRUCTION: [&str; 5] = ["ResolvedModule", ":", ":", "new", "("];
    const KIND_GATE: [&str; 2] = ["check_resolved_module_with_budget", "("];
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut paths = Vec::new();
    collect_production_rust_sources(&root, &mut paths);
    paths.sort();
    let mut constructors = Vec::new();
    let mut resolve_tokens = None;
    for path in paths {
        let relative = path
            .strip_prefix(env!("CARGO_MANIFEST_DIR"))
            .expect("production source belongs to the crate")
            .to_string_lossy()
            .replace('\\', "/");
        let source = fs::read_to_string(&path).expect("production source should be readable");
        let tokens = production_rust_code_tokens(&source);
        for (index, window) in tokens.windows(CONSTRUCTION.len()).enumerate() {
            if window == CONSTRUCTION {
                constructors.push((relative.clone(), index));
            }
        }
        if relative == "src/resolve.rs" {
            resolve_tokens = Some(tokens.into_iter().map(str::to_owned).collect::<Vec<_>>());
        }
    }
    assert_eq!(
        constructors.len(),
        1,
        "production ResolvedModule construction must remain a single fail-closed gate: {constructors:?}",
    );
    assert_eq!(constructors[0].0, "src/resolve.rs");
    let tokens = resolve_tokens.expect("resolution production source should be scanned");
    let kind_gates = tokens
        .windows(KIND_GATE.len())
        .enumerate()
        .filter_map(|(index, window)| (window == KIND_GATE).then_some(index))
        .collect::<Vec<_>>();
    assert_eq!(
        kind_gates.len(),
        1,
        "resolution must invoke total resolved kind checking exactly once: {kind_gates:?}",
    );
    let construction = tokens
        .windows(CONSTRUCTION.len())
        .position(|window| window == CONSTRUCTION)
        .expect("resolution must publish the checked module once");
    assert!(
        kind_gates[0] < construction,
        "resolved kind checking must complete before ResolvedModule construction",
    );
}

#[test]
fn abstract_nominal_kind_publication_transfers_the_reserved_allocation() {
    const FUNCTION: [&str; 3] = ["fn", "with_abstract_nominal_facts", "("];
    const WHOLE_MAP_TRANSFER: [&str; 16] = [
        "std",
        ":",
        ":",
        "mem",
        ":",
        ":",
        "replace",
        "(",
        "&",
        "mut",
        "self",
        ".",
        "abstract_nominal_kinds",
        ",",
        "kinds",
        ")",
    ];
    const PER_ENTRY_INSERT: [&str; 6] = ["self", ".", "abstract_nominal_kinds", ".", "insert", "("];
    const DISPLACED_VALUES: [&str; 5] = ["displaced", ".", "into_values", "(", ")"];
    const ITERATIVE_DISCARD: [&str; 4] = [
        "discard_non_materialized_nominal_kind_fact",
        "(",
        "fact",
        ")",
    ];

    let source = fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("src/resolved.rs"))
        .expect("resolved source should be readable");
    let tokens = production_rust_code_tokens(&source);
    let function = tokens
        .windows(FUNCTION.len())
        .position(|window| window == FUNCTION)
        .expect("the checker-view publication helper should exist");
    let body_open = tokens[function..]
        .iter()
        .position(|token| *token == "{")
        .map(|offset| function + offset)
        .expect("the publication helper should have a body");
    let body_close = matching_token(&tokens, body_open, "{", "}");
    let body = &tokens[body_open + 1..body_close];

    assert!(
        body.windows(WHOLE_MAP_TRANSFER.len())
            .any(|window| window == WHOLE_MAP_TRANSFER),
        "checker-view publication must transfer the already-reserved Kind map allocation whole",
    );
    assert!(
        !body
            .windows(PER_ENTRY_INSERT.len())
            .any(|window| window == PER_ENTRY_INSERT),
        "checker-view publication must not reinsert retained Kind facts into an unreserved map",
    );
    assert!(
        body.windows(DISPLACED_VALUES.len())
            .any(|window| window == DISPLACED_VALUES)
            && body
                .windows(ITERATIVE_DISCARD.len())
                .any(|window| window == ITERATIVE_DISCARD),
        "every displaced old sidecar fact must be dismantled explicitly",
    );
}

#[test]
fn core_and_evaluator_keep_interface_evidence_outside_their_closed_inventories() {
    for (path, source) in EVALUATOR_SOURCES {
        for identifier in production_rust_code_tokens(source)
            .into_iter()
            .filter(|token| is_rust_identifier(token))
        {
            assert!(
                !is_forbidden_interface_identifier(identifier),
                "{path} must not gain the {identifier} interface runtime mechanism"
            );
        }
    }
    for (path, source) in CORE_SOURCES {
        for identifier in production_rust_code_tokens(source)
            .into_iter()
            .filter(|token| is_rust_identifier(token))
        {
            assert!(
                !is_forbidden_interface_identifier(identifier)
                    || is_allowed_private_core_method_evidence_identifier(path, identifier),
                "{path} must not gain the {identifier} interface runtime mechanism"
            );
        }
    }
}

fn is_allowed_private_core_method_evidence_identifier(path: &str, identifier: &str) -> bool {
    let shared = matches!(
        identifier,
        "EvidenceNode"
            | "EvidenceNodeId"
            | "EvidenceSelection"
            | "Implementation"
            | "ImplementationOwner"
            | "Impl"
            | "ImplMethodId"
            | "RequirementId"
            | "actual_interface"
            | "expected_anchor_interface"
            | "expected_interface"
            | "interface_argument"
            | "interface_parameter"
            | "interface_replacement"
            | "interface"
            | "implementation"
            | "implementation_owner"
            | "implementation_owners"
            | "implementation_replacements"
            | "requirement"
            | "requirements"
            | "selection_contains_implementation_method"
            | "selected_interface"
    );
    shared && matches!(path, "src/core/dialect.rs" | "src/core/validate.rs")
        || match path {
            "src/core/dialect.rs" => matches!(
                identifier,
                "MethodEvidenceAdapter"
                    | "MethodEvidenceAdapterEdge"
                    | "MethodEvidenceAnchor"
                    | "MethodEvidenceAnchorRole"
                    | "MethodEvidenceCatalog"
                    | "MethodEvidenceCatalogMutationForTest"
                    | "MethodEvidenceDomain"
                    | "MethodEvidenceExpectation"
                    | "MethodEvidenceExpectedProducer"
                    | "MethodEvidenceExpectedRole"
                    | "MethodEvidenceImplementationOwner"
                    | "MethodEvidenceMethod"
                    | "MethodEvidenceOccurrence"
                    | "MethodEvidenceOwner"
                    | "MethodEvidenceProducer"
                    | "WrongRequirementPosition"
                    | "authenticate_method_evidence"
                    | "consumed_method_evidence"
                    | "empty_method_evidence"
                    | "implementation_owner_count"
                    | "method_evidence"
                    | "method_evidence_adapter_interface_matches"
                    | "method_evidence_anchor_matches_expectation"
                    | "method_evidence_anchors"
                    | "method_evidence_expected_producer_matches"
                    | "method_evidence_producer_matches"
                    | "requires_method_evidence_implementation_owner"
                    | "requirement_position"
                    | "target_requirement"
                    | "with_registry_and_method_evidence"
            ),
            "src/core/validate.rs" => matches!(
                identifier,
                "MethodEvidenceAnchor"
                    | "MethodEvidenceAnchorRole"
                    | "MethodEvidenceCatalog"
                    | "MethodEvidenceCatalogMutationForTest"
                    | "MethodEvidenceExpectedProducer"
                    | "MethodEvidenceExpectedRole"
                    | "MethodEvidenceOwner"
                    | "MethodEvidenceProducer"
                    | "authenticated_method_evidence"
                    | "implementation_replacements"
                    | "method_evidence"
                    | "method_evidence_anchor_matches_expectation"
                    | "method_evidence_anchors"
                    | "method_evidence_producer_matches"
                    | "validate_implementation_owner_anchor"
                    | "validate_method_evidence_authority"
                    | "validate_method_evidence_carrier_incoming"
                    | "validate_method_evidence_domain"
                    | "validate_method_evidence_domain_order"
                    | "validate_method_evidence_owner_envelopes"
                    | "validate_method_evidence_type_owners"
            ),
            "src/core/transform.rs" => matches!(
                identifier,
                "authenticate_method_evidence"
                    | "interface_argument"
                    | "method_evidence"
                    | "method_evidence_anchors"
                    | "requirement"
                    | "with_registry_and_method_evidence"
            ),
            _ => false,
        }
}

fn custom_drop_owner_names(tokens: &[&str]) -> BTreeSet<String> {
    tokens
        .windows(3)
        .filter(|window| window[0] == "Drop" && window[1] == "for")
        .filter(|window| is_rust_identifier(window[2]))
        .map(|window| window[2].to_owned())
        .collect()
}

fn production_rust_code_tokens(source: &str) -> Vec<&str> {
    const CFG_TEST: [&str; 7] = ["#", "[", "cfg", "(", "test", ")", "]"];

    let tokens = rust_code_tokens(source);
    let mut production = Vec::with_capacity(tokens.len());
    let mut cursor = 0usize;
    while cursor < tokens.len() {
        if tokens[cursor..].starts_with(&CFG_TEST)
            && tokens.get(cursor + CFG_TEST.len()) == Some(&"mod")
            && let Some(open_offset) = tokens[cursor + CFG_TEST.len() + 1..]
                .iter()
                .position(|token| *token == "{")
        {
            let open = cursor + CFG_TEST.len() + 1 + open_offset;
            cursor = matching_token(&tokens, open, "{", "}") + 1;
            continue;
        }
        production.push(tokens[cursor]);
        cursor += 1;
    }
    production
}

fn recursively_unsafe_backing_fields(
    fields: &[ProductionField],
    sources: &[(&str, &str)],
) -> BTreeMap<(String, String), BTreeSet<String>> {
    let declarations = declaration_index(fields);
    let drops = sources
        .iter()
        .map(|(path, source)| {
            (
                (*path).to_owned(),
                custom_drop_owner_names(&production_rust_code_tokens(source)),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut unsafe_carriers = [
        ("src/types.rs", "Type"),
        ("src/types.rs", "Kind"),
        ("src/source.rs", "Origin"),
        ("src/surface.rs", "SurfaceType"),
        ("src/surface.rs", "SurfaceKind"),
    ]
    .into_iter()
    .map(|(source, name)| CarrierId {
        source: source.to_owned(),
        name: name.to_owned(),
    })
    .collect::<BTreeSet<_>>();
    let mut backing = BTreeMap::<(String, String), BTreeSet<String>>::new();
    loop {
        let mut changed = false;
        for field in fields {
            let owns_unsafe = field.references.iter().any(|reference| {
                let direct = field
                    .reference_retentions
                    .get(reference)
                    .expect("every reference has a direct retention set");
                direct.0 & (RetentionSet::OWNED | RetentionSet::SHARED) != 0
                    && reference_reaches_owner_with_aliases(
                        &field.source,
                        &field.carrier,
                        reference,
                        &field.aliases,
                        &declarations,
                        &unsafe_carriers,
                    )
            });
            if !owns_unsafe {
                continue;
            }
            changed |= backing
                .entry((field.source.clone(), field.carrier.clone()))
                .or_default()
                .insert(field.field.clone());
            let terminal = field.carrier.rsplit("::").next().unwrap_or(&field.carrier);
            let has_iterative_drop = drops
                .get(&field.source)
                .is_some_and(|owners| owners.contains(terminal));
            if !has_iterative_drop {
                changed |= unsafe_carriers.insert(CarrierId {
                    source: field.source.clone(),
                    name: field.carrier.clone(),
                });
            }
        }
        if !changed {
            return backing;
        }
    }
}

fn owner_backing_fields(tokens: &[&str], owner: &str) -> BTreeSet<String> {
    let mut fields = BTreeSet::new();
    for declaration in tokens
        .windows(2)
        .enumerate()
        .filter_map(|(index, window)| (window == ["struct", owner]).then_some(index))
    {
        let Some((open, delimiter)) = declaration_delimiter(tokens, declaration + 2) else {
            continue;
        };
        match delimiter {
            "(" => {
                let close = matching_token(tokens, open, "(", ")");
                fields.extend(
                    split_top_level(&tokens[open + 1..close], ",")
                        .into_iter()
                        .enumerate()
                        .filter(|(_, field)| !field.is_empty())
                        .map(|(index, _)| index.to_string()),
                );
            }
            "{" => {
                let close = matching_token(tokens, open, "{", "}");
                for field in split_top_level(&tokens[open + 1..close], ",") {
                    let Some(colon) = top_level_position(field, ":") else {
                        continue;
                    };
                    if let Some(name) = field[..colon].iter().rev().copied().find(|token| {
                        is_rust_identifier(token) && !matches!(*token, "pub" | "crate")
                    }) {
                        fields.insert(name.to_owned());
                    }
                }
            }
            ";" => {}
            _ => unreachable!("a struct declaration has one closed delimiter"),
        }
    }
    fields
}

#[derive(Clone, Debug)]
struct OwnerBinding {
    name: String,
    scope: Vec<usize>,
    declared_at: usize,
    owns: bool,
}

fn binding_owns_at(
    bindings: &[OwnerBinding],
    scopes: &[Vec<usize>],
    name: &str,
    at: usize,
) -> bool {
    bindings
        .iter()
        .filter(|binding| {
            binding.name == name
                && binding.declared_at <= at
                && scopes[at].starts_with(&binding.scope)
        })
        .max_by_key(|binding| (binding.scope.len(), binding.declared_at))
        .is_some_and(|binding| binding.owns)
}

fn impl_body_ranges(tokens: &[&str], owner: &str) -> Vec<(usize, usize, bool)> {
    let mut ranges = Vec::new();
    let mut cursor = 0usize;
    while cursor < tokens.len() {
        if tokens[cursor] != "impl" {
            cursor += 1;
            continue;
        }
        let Some((open, delimiter)) = declaration_delimiter(tokens, cursor + 1) else {
            break;
        };
        if delimiter != "{" {
            cursor = open + 1;
            continue;
        }
        let close = matching_token(tokens, open, "{", "}");
        let header = &tokens[cursor + 1..open];
        if header.contains(&owner) {
            ranges.push((
                open,
                close,
                header.contains(&"Drop") && header.contains(&"for"),
            ));
        }
        cursor = close + 1;
    }
    ranges
}

fn drop_teardown_ranges(tokens: &[&str], owner: &str) -> Vec<(usize, usize)> {
    let impls = impl_body_ranges(tokens, owner);
    let mut ranges = impls
        .iter()
        .filter(|(_, _, is_drop)| *is_drop)
        .map(|(open, close, _)| (*open, *close))
        .collect::<Vec<_>>();
    let mut methods = BTreeSet::new();
    loop {
        let mut changed = false;
        for (open, close) in &ranges {
            for window in tokens[*open + 1..*close].windows(4) {
                if window[0] == "self"
                    && window[1] == "."
                    && is_rust_identifier(window[2])
                    && window[3] == "("
                {
                    changed |= methods.insert(window[2].to_owned());
                }
            }
        }
        for (impl_open, impl_close, _) in &impls {
            let mut cursor = impl_open + 1;
            while cursor < *impl_close {
                if tokens[cursor] != "fn"
                    || !tokens
                        .get(cursor + 1)
                        .is_some_and(|name| methods.contains(*name))
                {
                    cursor += 1;
                    continue;
                }
                let Some(parameter_open) = tokens[cursor + 2..*impl_close]
                    .iter()
                    .position(|token| *token == "(")
                    .map(|offset| cursor + 2 + offset)
                else {
                    break;
                };
                let parameter_close = matching_token(tokens, parameter_open, "(", ")");
                let Some((body_open, delimiter)) =
                    declaration_delimiter(tokens, parameter_close + 1)
                else {
                    break;
                };
                if delimiter != "{" {
                    cursor = body_open + 1;
                    continue;
                }
                let body_close = matching_token(tokens, body_open, "{", "}");
                if !ranges.contains(&(body_open, body_close)) {
                    ranges.push((body_open, body_close));
                    changed = true;
                }
                cursor = body_close + 1;
            }
        }
        if !changed {
            return ranges;
        }
    }
}

fn owner_bindings(tokens: &[&str], owner: &str) -> Vec<OwnerBinding> {
    let scopes = token_scope_paths(tokens);
    let owner_impls = impl_body_ranges(tokens, owner);
    let mut bindings = Vec::new();
    let mut cursor = 0usize;
    while cursor < tokens.len() {
        if tokens[cursor] == "fn"
            && let Some(open_offset) = tokens[cursor + 1..].iter().position(|token| *token == "(")
        {
            let open = cursor + 1 + open_offset;
            let close = matching_token(tokens, open, "(", ")");
            let Some((body_open, delimiter)) = declaration_delimiter(tokens, close + 1) else {
                break;
            };
            if delimiter != "{" {
                cursor = body_open + 1;
                continue;
            }
            let body_close = matching_token(tokens, body_open, "{", "}");
            let scope = scopes
                .get(body_open + 1)
                .cloned()
                .unwrap_or_else(|| scopes[body_open].clone());
            let in_owner_impl = owner_impls
                .iter()
                .any(|(impl_open, impl_close, _)| *impl_open < cursor && body_close < *impl_close);
            for parameter in split_top_level(&tokens[open + 1..close], ",") {
                let colon = top_level_position(parameter, ":");
                let name_tokens = colon.map_or(parameter, |colon| &parameter[..colon]);
                if let Some(name) = name_tokens
                    .iter()
                    .rev()
                    .copied()
                    .find(|token| is_rust_identifier(token) && *token != "mut")
                {
                    let owns = colon.is_some_and(|colon| parameter[colon + 1..].contains(&owner))
                        || (name == "self" && in_owner_impl);
                    bindings.push(OwnerBinding {
                        name: name.to_owned(),
                        scope: scope.clone(),
                        declared_at: body_open,
                        owns,
                    });
                }
            }
            cursor = body_open + 1;
            continue;
        }
        cursor += 1;
    }

    let mut cursor = 0usize;
    while cursor < tokens.len() {
        if tokens[cursor] != "let" {
            cursor += 1;
            continue;
        }
        let end = tokens[cursor + 1..]
            .iter()
            .position(|token| *token == ";")
            .map_or(tokens.len(), |offset| cursor + 1 + offset);
        let Some(equals) = tokens[cursor + 1..end]
            .iter()
            .position(|token| *token == "=")
            .map(|offset| cursor + 1 + offset)
        else {
            cursor = end.saturating_add(1);
            continue;
        };
        let Some(name) = tokens[cursor + 1..equals]
            .iter()
            .copied()
            .find(|token| is_rust_identifier(token) && *token != "mut")
        else {
            cursor = end.saturating_add(1);
            continue;
        };
        let initializer = &tokens[equals + 1..end];
        let alias = initializer
            .iter()
            .enumerate()
            .find(|(_, token)| is_rust_identifier(token))
            .filter(|(index, _)| {
                initializer[..*index]
                    .iter()
                    .all(|token| matches!(*token, "&" | "mut" | "("))
                    && initializer[*index + 1..]
                        .iter()
                        .all(|token| matches!(*token, ")"))
            })
            .map(|(_, token)| *token);
        let explicitly_typed = tokens[cursor + 1..equals].contains(&owner);
        let directly_constructed = initializer.contains(&owner);
        let owns = explicitly_typed
            || directly_constructed
            || alias.is_some_and(|alias| {
                binding_owns_at(&bindings, &scopes, alias, equals.saturating_sub(1))
            });
        bindings.push(OwnerBinding {
            name: name.to_owned(),
            scope: scopes[cursor].clone(),
            declared_at: end,
            owns,
        });
        cursor = end.saturating_add(1);
    }
    bindings
}

fn assert_no_destructive_backing_field_bypass(
    path: &str,
    tokens: &[&str],
    owner: &str,
    fields: &BTreeSet<String>,
    unsafe_terminals: &BTreeSet<String>,
    custom_drop_owners: &BTreeSet<String>,
) {
    fn enclosing_struct_literal<'a>(tokens: &'a [&str], at: usize) -> Option<&'a str> {
        let mut depth = 0usize;
        for cursor in (0..at).rev() {
            match tokens[cursor] {
                "}" => depth += 1,
                "{" if depth > 0 => depth -= 1,
                "{" => {
                    return cursor.checked_sub(1).and_then(|owner| {
                        is_rust_identifier(tokens[owner]).then_some(tokens[owner])
                    });
                }
                _ => {}
            }
        }
        None
    }

    fn enclosing_impl_owner<'a>(tokens: &'a [&str], at: usize) -> Option<&'a str> {
        let mut cursor = 0usize;
        while cursor < at {
            if tokens[cursor] != "impl" {
                cursor += 1;
                continue;
            }
            let (open, delimiter) = declaration_delimiter(tokens, cursor + 1)?;
            if delimiter != "{" {
                cursor = open + 1;
                continue;
            }
            let close = matching_token(tokens, open, "{", "}");
            if open < at && at < close {
                let header = &tokens[cursor + 1..open];
                let mut tail = header
                    .iter()
                    .rposition(|token| *token == "for")
                    .map_or(header, |for_index| &header[for_index + 1..]);
                if tail.first() == Some(&"<") {
                    let close = matching_token(tail, 0, "<", ">");
                    tail = &tail[close + 1..];
                }
                return tail
                    .iter()
                    .copied()
                    .find(|token| is_rust_identifier(token) && !matches!(*token, "where"));
            }
            cursor = close + 1;
        }
        None
    }

    fn enclosing_single_argument_owner<'a>(
        tokens: &'a [&str],
        at: usize,
        owners: &BTreeSet<String>,
    ) -> Option<&'a str> {
        let mut depth = 0usize;
        for cursor in (0..at).rev() {
            match tokens[cursor] {
                ")" => depth += 1,
                "(" if depth > 0 => depth -= 1,
                "(" => {
                    let Some(mut owner) = cursor.checked_sub(1).map(|owner| tokens[owner]) else {
                        continue;
                    };
                    if owner == "new"
                        && cursor >= 4
                        && tokens[cursor - 2] == ":"
                        && tokens[cursor - 3] == ":"
                    {
                        owner = tokens[cursor - 4];
                    }
                    if owners.contains(owner) {
                        let close = matching_token(tokens, cursor, "(", ")");
                        if split_top_level(&tokens[cursor + 1..close], ",").len() == 1 {
                            return Some(owner);
                        }
                    }
                }
                ";" | "{" | "}" if depth == 0 => return None,
                _ => {}
            }
        }
        None
    }

    fn has_assignment_before_statement_end(tokens: &[&str]) -> bool {
        let mut depths = [0usize; 4];
        for (index, token) in tokens.iter().enumerate() {
            if depths.iter().all(|depth| *depth == 0) && matches!(*token, ";" | "," | "{" | "}") {
                return false;
            }
            if depths.iter().all(|depth| *depth == 0)
                && matches!(*token, "&" | "|")
                && tokens.get(index + 1) == Some(token)
            {
                return false;
            }
            if *token == "="
                && depths.iter().all(|depth| *depth == 0)
                && !matches!(
                    tokens.get(index.wrapping_sub(1)),
                    Some(&("=" | "!" | "<" | ">"))
                )
                && tokens.get(index + 1) != Some(&"=")
                && tokens.get(index + 1) != Some(&">")
            {
                return true;
            }
            update_delimiter_depths(token, &mut depths);
        }
        false
    }

    fn terminal_mutated_field<'a>(root: &'a str, tail: &[&'a str]) -> &'a str {
        let mut terminal = root;
        let mut cursor = 0usize;
        while cursor + 1 < tail.len() {
            if matches!(tail[cursor], "=" | ";" | ",") {
                break;
            }
            if tail[cursor] == "."
                && is_rust_identifier(tail[cursor + 1])
                && tail.get(cursor + 2) != Some(&"(")
            {
                terminal = tail[cursor + 1];
            }
            cursor += 1;
        }
        terminal
    }

    fn mutable_alias_is_assigned(tokens: &[&str], at: usize) -> bool {
        let prefix = &tokens[at.saturating_sub(16)..at];
        let Some(alias) = prefix.windows(6).rev().find_map(|window| {
            (window[0] == "if"
                && window[1] == "let"
                && window[2] == "Some"
                && window[3] == "("
                && is_rust_identifier(window[4])
                && window[5] == ")")
                .then_some(window[4])
        }) else {
            return false;
        };
        let Some(body_open) = tokens[at..]
            .iter()
            .position(|token| *token == "{")
            .map(|offset| at + offset)
        else {
            return false;
        };
        let body_close = matching_token(tokens, body_open, "{", "}");
        tokens[body_open + 1..body_close]
            .windows(3)
            .any(|window| window == ["*", alias, "="])
    }

    fn is_infallible_consuming_transfer(tokens: &[&str], owner: &str, at: usize) -> bool {
        for (impl_open, impl_close, is_drop) in impl_body_ranges(tokens, owner) {
            if is_drop || !(impl_open < at && at < impl_close) {
                continue;
            }
            let mut cursor = impl_open + 1;
            while cursor < impl_close {
                if tokens[cursor] != "fn" {
                    cursor += 1;
                    continue;
                }
                let Some(parameter_open) = tokens[cursor + 1..impl_close]
                    .iter()
                    .position(|token| *token == "(")
                    .map(|offset| cursor + 1 + offset)
                else {
                    break;
                };
                let parameter_close = matching_token(tokens, parameter_open, "(", ")");
                let Some((body_open, delimiter)) =
                    declaration_delimiter(tokens, parameter_close + 1)
                else {
                    break;
                };
                if delimiter != "{" {
                    cursor = body_open + 1;
                    continue;
                }
                let body_close = matching_token(tokens, body_open, "{", "}");
                if !(body_open < at && at < body_close) {
                    cursor = body_close + 1;
                    continue;
                }
                let consumes_self =
                    split_top_level(&tokens[parameter_open + 1..parameter_close], ",")
                        .into_iter()
                        .any(|parameter| parameter.contains(&"self") && !parameter.contains(&"&"));
                let result = &tokens[parameter_close + 1..body_open];
                let body = &tokens[body_open + 1..body_close];
                if !consumes_self
                    || result
                        .iter()
                        .any(|token| matches!(*token, "Result" | "Option"))
                    || body
                        .iter()
                        .any(|token| matches!(*token, "?" | "return" | "Err"))
                {
                    return false;
                }

                let next_semicolon = tokens[at..body_close]
                    .iter()
                    .position(|token| *token == ";")
                    .map(|offset| at + offset);
                if next_semicolon.is_none() {
                    return true;
                }
                let statement_start = tokens[body_open + 1..at]
                    .iter()
                    .rposition(|token| matches!(*token, ";" | "{" | "}"))
                    .map_or(body_open + 1, |offset| body_open + 2 + offset);
                let statement = &tokens[statement_start..next_semicolon.expect("checked above")];
                let Some(local) = statement
                    .windows(2)
                    .find(|window| window[0] == "let" && is_rust_identifier(window[1]))
                    .map(|window| window[1])
                else {
                    return false;
                };
                let last_statement = tokens[body_open + 1..body_close]
                    .iter()
                    .rposition(|token| *token == ";")
                    .map_or(body_open + 1, |offset| body_open + 2 + offset);
                return tokens[last_statement..body_close].contains(&local);
            }
        }
        false
    }

    fn displaced_result_is_discarded(tokens: &[&str], at: usize, method: &str) -> bool {
        if !matches!(method, "insert" | "remove" | "swap_remove" | "replace") {
            return false;
        }
        let prefix = &tokens[at.saturating_sub(16)..at];
        let inline_displaced = prefix.windows(6).rev().find_map(|window| {
            (window[0] == "if"
                && window[1] == "let"
                && window[2] == "Some"
                && window[3] == "("
                && is_rust_identifier(window[4])
                && window[5] == ")")
                .then_some(window[4])
        });
        let Some(method_at) = tokens[at..]
            .windows(3)
            .position(|window| window[0] == "." && window[1] == method && window[2] == "(")
            .map(|offset| at + offset + 1)
        else {
            return false;
        };
        let call_close = matching_token(tokens, method_at + 1, "(", ")");
        let let_else_displaced = prefix.windows(6).rev().find_map(|window| {
            (window[0] == "let"
                && window[1] == "Some"
                && window[2] == "("
                && is_rust_identifier(window[3])
                && window[4] == ")"
                && window[5] == "=")
                .then_some(window[3])
        });
        if let Some(displaced) = let_else_displaced
            && tokens.get(call_close + 1) == Some(&"else")
            && tokens.get(call_close + 2) == Some(&"{")
        {
            let else_close = matching_token(tokens, call_close + 2, "{", "}");
            let diverges = tokens[call_close + 3..else_close]
                .iter()
                .any(|token| matches!(*token, "return" | "break" | "continue" | "panic"));
            if diverges
                && tokens[else_close + 1..].windows(5).take(2).any(|window| {
                    window[0] == ";"
                        && window[1].starts_with("discard_")
                        && window[2] == "("
                        && window[3] == displaced
                        && window[4] == ")"
                })
            {
                return true;
            }
        }
        let captured_local = prefix.windows(3).rev().find_map(|window| {
            (window[0] == "let" && is_rust_identifier(window[1]) && window[2] == "=")
                .then_some(window[1])
        });
        let deferred_displaced = captured_local.and_then(|captured| {
            tokens[call_close + 1..]
                .windows(9)
                .take(16)
                .find_map(|window| {
                    (window[0] == ";"
                        && window[1] == "if"
                        && window[2] == "let"
                        && window[3] == "Some"
                        && window[4] == "("
                        && is_rust_identifier(window[5])
                        && window[6] == ")"
                        && window[7] == "="
                        && window[8] == captured)
                        .then_some(window[5])
                })
        });
        let Some(displaced) = inline_displaced.or(deferred_displaced) else {
            return false;
        };
        let Some(body_open) = tokens[call_close + 1..]
            .iter()
            .position(|token| *token == "{")
            .map(|offset| call_close + 1 + offset)
        else {
            return false;
        };
        let body_close = matching_token(tokens, body_open, "{", "}");
        let body = &tokens[body_open + 1..body_close];
        body.windows(4).any(|window| {
            window[0].starts_with("discard_")
                && window[1] == "("
                && window[2] == displaced
                && window[3] == ")"
        }) || body.windows(5).any(|window| {
            window[0] == displaced
                && window[1] == "."
                && window[2] == "discard_iteratively"
                && window[3] == "("
                && window[4] == ")"
        }) || body.windows(6).any(|window| {
            window[0].starts_with("discard_")
                && window[1] == "("
                && window[2] == displaced
                && window[3] == "."
                && is_rust_identifier(window[4])
                && window[5] == ")"
        }) || body.windows(7).any(|window| {
            window[0] == "for"
                && is_rust_identifier(window[1])
                && window[2] == "in"
                && window[3] == displaced
                && window[4] == "."
                && window[5] == "into_vec"
                && window[6] == "("
                && body.windows(4).any(|discard| {
                    discard[0].starts_with("discard_")
                        && discard[1] == "("
                        && discard[2] == window[1]
                })
        })
    }

    let scopes = token_scope_paths(tokens);
    let bindings = owner_bindings(tokens, owner);
    let teardown_ranges = drop_teardown_ranges(tokens, owner);
    for index in 0..tokens.len().saturating_sub(2) {
        if !binding_owns_at(&bindings, &scopes, tokens[index], index)
            || tokens[index + 1] != "."
            || !fields.contains(tokens[index + 2])
            || teardown_ranges
                .iter()
                .any(|(open, close)| *open < index && index < *close)
        {
            continue;
        }
        let tail = &tokens[index + 3..];
        if !unsafe_terminals.contains(terminal_mutated_field(tokens[index + 2], tail)) {
            continue;
        }
        if mutable_alias_is_assigned(tokens, index) {
            panic!(
                "{path} must not assign through a mutable alias into {owner} backing storage via {}.{}",
                tokens[index],
                tokens[index + 2],
            );
        }
        if has_assignment_before_statement_end(tail) {
            panic!(
                "{path} must not assign through raw or nested {owner} backing storage via {}.{} near {:?}",
                tokens[index],
                tokens[index + 2],
                &tail[..tail.len().min(24)],
            );
        }
        if tail.first() == Some(&".")
            && let Some(method) = tail.get(1).copied()
            && matches!(
                method,
                "clear"
                    | "truncate"
                    | "remove"
                    | "swap_remove"
                    | "insert"
                    | "drain"
                    | "retain"
                    | "resize"
                    | "resize_with"
            )
            && !displaced_result_is_discarded(tokens, index, method)
        {
            panic!(
                "{path} must not invoke destructive mutation through raw {owner} backing storage via {}.{}.{}",
                tokens[index],
                tokens[index + 2],
                tail[1],
            );
        }
        let prefix = &tokens[index.saturating_sub(12)..index];
        let immediately_discarded = prefix
            .windows(2)
            .any(|window| window[0].starts_with("discard_") && window[1] == "(")
            && (!prefix.contains(&"replace")
                || tail.starts_with(&[",", "Type", ":", ":", "Unit", ")"]));
        if prefix.ends_with(&["(", "&", "mut"])
            && prefix
                .iter()
                .any(|token| matches!(*token, "take" | "replace" | "swap"))
            && !immediately_discarded
            && !enclosing_struct_literal(tokens, index).is_some_and(|destination| {
                let destination = if destination == "Self" {
                    enclosing_impl_owner(tokens, index).unwrap_or(destination)
                } else {
                    destination
                };
                custom_drop_owners.contains(destination)
            })
            && enclosing_single_argument_owner(tokens, index, custom_drop_owners).is_none()
            && !is_infallible_consuming_transfer(tokens, owner, index)
        {
            panic!(
                "{path} must not move or replace raw {owner} backing storage through {}.{} near {prefix:?}",
                tokens[index],
                tokens[index + 2],
            );
        }
    }
}

fn assert_automatic_iterative_owner_apis_are_narrow(sources: &[(&str, &str)], owners: &[&str]) {
    let mut fields = Vec::new();
    if !sources.iter().any(|(path, _)| *path == "src/types.rs") {
        fields.extend(parse_top_level_fields(
            "src/types.rs",
            "struct Type(Box<Type>);",
        ));
    }
    if !sources.iter().any(|(path, _)| *path == "src/source.rs") {
        fields.extend(parse_top_level_fields(
            "src/source.rs",
            "struct Origin(Box<Origin>);",
        ));
    }
    for (path, source) in sources {
        fields.extend(parse_top_level_fields(path, source));
    }
    let recursive_fields = recursively_unsafe_backing_fields(&fields, sources);
    let custom_drop_owners = sources
        .iter()
        .flat_map(|(_, source)| custom_drop_owner_names(&production_rust_code_tokens(source)))
        .collect::<BTreeSet<_>>();

    for (path, source) in sources {
        let tokens = production_rust_code_tokens(source);
        let mut guarded = owners
            .iter()
            .map(|owner| (*owner).to_owned())
            .collect::<BTreeSet<_>>();
        guarded.extend(custom_drop_owners.iter().cloned());
        let unsafe_terminals = recursive_fields
            .iter()
            .filter(|((owner_path, _), _)| owner_path == path)
            .flat_map(|(_, fields)| fields)
            .map(|field| field.rsplit('.').next().unwrap_or(field).to_owned())
            .collect::<BTreeSet<_>>();
        for owner in guarded {
            let physical_fields = owner_backing_fields(&tokens, &owner);
            let owner_fields = recursive_fields
                .iter()
                .filter(|((owner_path, carrier), _)| {
                    owner_path == path && carrier.rsplit("::").next().unwrap_or(carrier) == owner
                })
                .flat_map(|(_, fields)| fields.iter().cloned())
                .filter(|field| physical_fields.contains(field))
                .collect::<BTreeSet<_>>();
            if owner_fields.is_empty() {
                continue;
            }
            assert!(
                !tokens.windows(3).any(|window| {
                    window[0] == "DerefMut" && window[1] == "for" && window[2] == owner
                }),
                "{path} must not expose broad DerefMut for automatic owner {owner}",
            );
            assert_no_destructive_backing_field_bypass(
                path,
                &tokens,
                &owner,
                &owner_fields,
                &unsafe_terminals,
                &custom_drop_owners,
            );
        }
    }
}

#[test]
fn automatic_iterative_owners_expose_only_narrow_mutation_apis() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut paths = Vec::new();
    collect_production_rust_sources(&root, &mut paths);
    paths.sort();
    let owned_sources = paths
        .into_iter()
        .map(|path| {
            let relative = path
                .strip_prefix(env!("CARGO_MANIFEST_DIR"))
                .expect("an owner source belongs to the crate")
                .to_string_lossy()
                .replace('\\', "/");
            let source = fs::read_to_string(path).expect("an owner source should be readable");
            (relative, source)
        })
        .collect::<Vec<_>>();
    let sources = owned_sources
        .iter()
        .map(|(path, source)| (path.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let owners = [
        "IterativeTypeOwner",
        "InferenceSolutionMap",
        "ElaborationTaskBuffer",
        "TypedNodeBuffer",
        "ElaboratedDeclarationBuffer",
        "OwnedTypeBuffer",
        "CorePatternBuffer",
        "CorePatternOwner",
        "IterativeTypeBuffer",
        "CorePatternMatrixBuffer",
        "ProvenancedTypeBuffer",
        "EvidenceSpecificationBuffer",
        "ResolvedTypeBuffer",
        "ImportedTypeVariableBuffer",
        "ResolvedTypeVariableBuffer",
        "ResolvedExpressionBuffer",
        "ResolvedDeclarationBuffer",
        "ResolveTaskBuffer",
        "ProvenancedTypeOwner",
        "TypedNodeOwner",
        "MatchProgressOwner",
        "TypeReplacementBuffer",
        "TypeReplacementMap",
        "ReplacementMap",
        "PendingGoals",
        "TypeBuffer",
        "CorePatternMatrix",
        "CorePatternRow",
        "OwnedTypeSequence",
        "OwnedTypeBuffer",
    ];
    assert_automatic_iterative_owner_apis_are_narrow(&sources, &owners);
}

#[test]
fn narrow_owner_guard_rejects_lexical_raw_member_bypasses() {
    let fixtures = [
        (
            "multiline named-field clear",
            "src/evidence.rs",
            "struct ReplacementMap { values: Vec<Type> } \
             impl Drop for ReplacementMap { fn drop(&mut self) {} } \
             fn bypass(map: &mut ReplacementMap) { map \
                 .values \
                 .clear(); }",
            &["ReplacementMap"][..],
        ),
        (
            "tuple-field indexing and mem::take",
            "src/pattern.rs",
            "struct TypeReplacementMap(Vec<Type>); \
             impl Drop for TypeReplacementMap { fn drop(&mut self) {} } \
             fn bypass(map: &mut TypeReplacementMap) { \
                 map.0[0] = Type::Unit; \
                 let _ = std::mem::take(&mut map.0); \
             }",
            &["TypeReplacementMap"][..],
        ),
        (
            "alias-bound named-field clear",
            "src/evidence.rs",
            "struct ReplacementMap { values: Vec<Type> } \
             impl Drop for ReplacementMap { fn drop(&mut self) {} } \
             fn bypass(map: &mut ReplacementMap) { \
                 let alias = map; \
                 alias.values.clear(); \
             }",
            &["ReplacementMap"][..],
        ),
        (
            "mutable element reference escape",
            "src/pattern.rs",
            "struct TypeReplacementMap(Vec<Type>); \
             impl Drop for TypeReplacementMap { fn drop(&mut self) {} } \
             fn bypass(map: &mut TypeReplacementMap) { \
                 *map.0.get_mut(0).unwrap() = Type::Unit; \
             }",
            &["TypeReplacementMap"][..],
        ),
        (
            "mutable element alias assignment",
            "src/resolved.rs",
            "struct ImportedFacts { globals: HashMap<u32, Type> } \
             impl Drop for ImportedFacts { fn drop(&mut self) {} } \
             fn bypass(facts: &mut ImportedFacts) { \
                 if let Some(existing) = facts.globals.get_mut(&0) { \
                     *existing = Type::Unit; \
                 } \
             }",
            &["ImportedFacts"][..],
        ),
        (
            "unlisted custom-Drop recursive owner",
            "src/custom.rs",
            "struct ForgottenBuffer(Vec<Type>); \
             impl Drop for ForgottenBuffer { fn drop(&mut self) {} } \
             impl DerefMut for ForgottenBuffer { \
                 fn deref_mut(&mut self) -> &mut Vec<Type> { &mut self.0 } \
             }",
            &[][..],
        ),
    ];
    let mut missed = Vec::new();
    for (label, path, source, owners) in fixtures {
        if std::panic::catch_unwind(|| {
            assert_automatic_iterative_owner_apis_are_narrow(&[(path, source)], owners);
        })
        .is_ok()
        {
            missed.push(label);
        }
    }
    assert!(
        missed.is_empty(),
        "the narrow-owner guard missed adversarial bypasses: {missed:?}",
    );
}

#[test]
fn narrow_owner_guard_accepts_immediate_displaced_value_disposal() {
    let source = "
        struct TypeFact { ty: Type }
        struct TypeContext { binders: HashMap<u32, TypeFact> }
        impl Drop for TypeContext { fn drop(&mut self) {} }
        impl TypeContext {
            fn inline(&mut self, fact: TypeFact) {
                if let Some(displaced) = self.binders.insert(0, fact) {
                    discard_type_fact(displaced);
                }
            }
            fn deferred(&mut self, fact: TypeFact) {
                let displaced = self.binders.insert(0, fact);
                if let Some(displaced) = displaced {
                    discard_type_fact(displaced);
                } else {}
            }
            fn let_else(&mut self) -> bool {
                let Some(fact) = self.binders.remove(&0) else {
                    return false;
                };
                discard_type_fact(fact);
                true
            }
            fn compares(&self, other: &Self) -> bool {
                self.binders.len() != other.binders.len()
                    || self.binders.len() == other.binders.len()
                    || self.binders.len() <= other.binders.len()
                    || self.binders.len() >= other.binders.len()
            }
        }";
    assert_automatic_iterative_owner_apis_are_narrow(
        &[("src/elaborate.rs", source)],
        &["TypeContext"],
    );
}

#[test]
fn synthesis_block_exit_releases_original_state_after_macro_shadow_drop() {
    struct DropProbe<'a>(&'a Cell<bool>);

    impl Drop for DropProbe<'_> {
        fn drop(&mut self) {
            self.0.set(true);
        }
    }

    macro_rules! shadow {
        ($name:ident, $probe:expr) => {
            let $name = $probe;
        };
    }

    let original_dropped = Cell::new(false);
    let shadow_dropped = Cell::new(false);
    {
        let validated_interfaces = DropProbe(&original_dropped);
        assert!(!validated_interfaces.0.get());
        shadow!(validated_interfaces, DropProbe(&shadow_dropped));
        ::std::mem::drop(validated_interfaces);
        assert!(shadow_dropped.get());
        assert!(!original_dropped.get());
    }

    let simulate_core_validation = || {
        assert!(
            original_dropped.get(),
            "block exit must release the original state before Core validation"
        );
    };
    simulate_core_validation();
}

fn is_forbidden_interface_identifier(identifier: &str) -> bool {
    let names_interface_abstraction = has_identifier_component(identifier, "Impl", "impl")
        || has_camel_component(identifier, "Requirement");
    let identifier = identifier.to_ascii_lowercase();
    let carries_interface_vocabulary = ["interface", "evidence", "dictionary", "implementation"]
        .iter()
        .any(|term| identifier.contains(term));
    let combines_runtime_or_method_dispatch = ["runtime", "method"]
        .iter()
        .any(|qualifier| identifier.contains(qualifier))
        && ["registry", "lookup", "dispatch"]
            .iter()
            .any(|mechanism| identifier.contains(mechanism));
    let combines_authorization_route =
        identifier.contains("authorization") && identifier.contains("route");
    let combines_requirement_mechanism = identifier
        .split('_')
        .any(|component| component == "requirement")
        && [
            "interface",
            "impl",
            "evidence",
            "dictionary",
            "registry",
            "lookup",
            "dispatch",
            "method",
        ]
        .iter()
        .any(|mechanism| identifier.contains(mechanism));

    names_interface_abstraction
        || carries_interface_vocabulary
        || combines_runtime_or_method_dispatch
        || combines_authorization_route
        || combines_requirement_mechanism
}

fn has_identifier_component(identifier: &str, camel: &str, snake: &str) -> bool {
    let snake_component = identifier != snake
        && identifier
            .split('_')
            .any(|component| component.eq_ignore_ascii_case(snake));

    has_camel_component(identifier, camel) || snake_component
}

fn has_camel_component(identifier: &str, camel: &str) -> bool {
    identifier.match_indices(camel).any(|(start, _)| {
        let end = start + camel.len();
        identifier
            .as_bytes()
            .get(end)
            .is_none_or(|next| !next.is_ascii_lowercase())
    })
}

fn rust_code_identifiers(source: &str) -> Vec<&str> {
    rust_code_tokens(source)
        .into_iter()
        .filter(|token| {
            token
                .as_bytes()
                .first()
                .is_some_and(|first| first.is_ascii_alphabetic() || *first == b'_')
        })
        .collect()
}

fn rust_code_tokens(source: &str) -> Vec<&str> {
    let bytes = source.as_bytes();
    let mut tokens = Vec::new();
    let mut cursor = 0;

    while cursor < bytes.len() {
        if bytes[cursor..].starts_with(b"//") {
            cursor += 2;
            while cursor < bytes.len() && bytes[cursor] != b'\n' {
                cursor += 1;
            }
            continue;
        }
        if bytes[cursor..].starts_with(b"/*") {
            cursor += 2;
            let mut depth = 1usize;
            while cursor < bytes.len() && depth > 0 {
                if bytes[cursor..].starts_with(b"/*") {
                    depth += 1;
                    cursor += 2;
                } else if bytes[cursor..].starts_with(b"*/") {
                    depth -= 1;
                    cursor += 2;
                } else {
                    cursor += 1;
                }
            }
            continue;
        }
        if let Some(end) = rust_literal_end(bytes, cursor) {
            cursor = end;
            continue;
        }
        if bytes[cursor].is_ascii_alphabetic() || bytes[cursor] == b'_' {
            let start = cursor;
            cursor += 1;
            while cursor < bytes.len()
                && (bytes[cursor].is_ascii_alphanumeric() || bytes[cursor] == b'_')
            {
                cursor += 1;
            }
            tokens.push(&source[start..cursor]);
            continue;
        }
        if bytes[cursor].is_ascii_digit() {
            let start = cursor;
            cursor += 1;
            while cursor < bytes.len() && bytes[cursor].is_ascii_digit() {
                cursor += 1;
            }
            tokens.push(&source[start..cursor]);
            continue;
        }
        if matches!(
            bytes[cursor],
            b'.' | b'('
                | b')'
                | b'{'
                | b'}'
                | b'['
                | b']'
                | b'#'
                | b';'
                | b','
                | b'&'
                | b'*'
                | b'|'
                | b':'
                | b'!'
                | b'?'
                | b'='
                | b'<'
                | b'>'
        ) {
            tokens.push(&source[cursor..cursor + 1]);
        }
        cursor += 1;
    }

    tokens
}

fn rust_literal_end(source: &[u8], cursor: usize) -> Option<usize> {
    let quote = match source.get(cursor..)? {
        [b'\'', ..] => return rust_character_literal_end(source, cursor),
        [b'b', b'\'', ..] => return rust_character_literal_end(source, cursor + 1),
        [b'"', ..] => cursor,
        [b'b' | b'c', b'"', ..] => cursor + 1,
        [b'r', rest @ ..] => return rust_raw_literal_end(source, cursor, rest),
        [b'b' | b'c', b'r', rest @ ..] => return rust_raw_literal_end(source, cursor + 1, rest),
        _ => return None,
    };
    let mut end = quote + 1;
    while end < source.len() {
        match source[end] {
            b'\\' => end = end.saturating_add(2),
            b'"' => return Some(end + 1),
            _ => end += 1,
        }
    }
    Some(source.len())
}

fn rust_character_literal_end(source: &[u8], quote: usize) -> Option<usize> {
    debug_assert_eq!(source[quote], b'\'');
    let character = quote + 1;
    let character_end = if source.get(character) == Some(&b'\\') {
        rust_character_escape_end(source, character)?
    } else {
        if matches!(source.get(character), Some(b'\'' | b'\n' | b'\r')) {
            return None;
        }
        let width = std::str::from_utf8(source.get(character..)?)
            .ok()?
            .chars()
            .next()?
            .len_utf8();
        character + width
    };
    (source.get(character_end) == Some(&b'\'')).then_some(character_end + 1)
}

fn rust_character_escape_end(source: &[u8], escape: usize) -> Option<usize> {
    match source.get(escape + 1)? {
        b'\'' | b'"' | b'n' | b'r' | b't' | b'\\' | b'0' => Some(escape + 2),
        b'x' => source
            .get(escape + 2..escape + 4)
            .filter(|digits| digits.iter().all(u8::is_ascii_hexdigit))
            .map(|_| escape + 4),
        b'u' if source.get(escape + 2) == Some(&b'{') => {
            let digits_start = escape + 3;
            let close = digits_start
                + source[digits_start..]
                    .iter()
                    .position(|byte| *byte == b'}')?;
            let digits = &source[digits_start..close];
            let digit_count = digits
                .iter()
                .filter(|byte| byte.is_ascii_hexdigit())
                .count();
            (digit_count > 0
                && digit_count <= 6
                && digits
                    .iter()
                    .all(|byte| byte.is_ascii_hexdigit() || *byte == b'_'))
            .then_some(close + 1)
        }
        _ => None,
    }
}

fn rust_raw_literal_end(source: &[u8], raw_prefix: usize, rest: &[u8]) -> Option<usize> {
    debug_assert_eq!(source[raw_prefix], b'r');
    let hash_count = rest.iter().take_while(|byte| **byte == b'#').count();
    if rest.get(hash_count) != Some(&b'"') {
        return None;
    }
    let mut end = raw_prefix + hash_count + 2;
    while end < source.len() {
        if source[end] == b'"'
            && source
                .get(end + 1..end + 1 + hash_count)
                .is_some_and(|suffix| suffix.iter().all(|byte| *byte == b'#'))
        {
            return Some(end + 1 + hash_count);
        }
        end += 1;
    }
    Some(source.len())
}

#[test]
fn interface_inventory_guard_reads_code_identifiers_but_not_prose() {
    assert!(
        rust_code_tokens(r#"'}' b'{' '\'' '\x7d' '\u{7b}' b'\x7b'"#).is_empty(),
        "character and byte-character contents must not become code tokens"
    );
    assert_eq!(
        rust_code_tokens("'a 'static '_ 'label:"),
        ["a", "static", "_", "label", ":"],
        "lifetimes and labels must remain code rather than character literals"
    );
    assert_eq!(
        rust_code_identifiers(
            r###"
            // InterfaceRegistry is prose.
            const NOTE: &str = "EvidenceLookup is prose";
            /* DictionaryDispatch is prose. */
            struct ImplRegistry;
            "###,
        ),
        ["const", "NOTE", "str", "struct", "ImplRegistry"],
    );
    for forbidden in [
        "ImplRegistry",
        "RegistryImpl",
        "impl_lookup",
        "lookup_impl",
        "ImplMethod",
        "RequirementNode",
        "RuntimeRequirement",
        "requirement_registry",
        "RuntimeLookup",
        "dispatch_runtime",
        "registry_interface",
        "AuthorizationRoute",
        "authorization_route",
    ] {
        assert!(is_forbidden_interface_identifier(forbidden));
    }
    for allowed in [
        "impl",
        "Implicit",
        "ImplicitFrame",
        "Implementor",
        "requirement",
        "requirements",
        "lookup",
        "dispatch_entry",
        "registry",
    ] {
        assert!(!is_forbidden_interface_identifier(allowed));
    }
}

trait OperationFamily {
    type Operation;
}

enum PureOperation {}

struct PureOperations;

impl OperationFamily for PureOperations {
    type Operation = PureOperation;
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum MockFutureOperation {
    YieldOnce,
}

struct MockFutureOperations;

impl OperationFamily for MockFutureOperations {
    type Operation = MockFutureOperation;
}

enum Computation<F: OperationFamily> {
    Pure {
        result: Type,
        computation: PureComputation,
    },
    Operation {
        result: Type,
        operation: F::Operation,
    },
}

fn computation_result<F: OperationFamily>(computation: &Computation<F>) -> &Type {
    match computation {
        Computation::Pure { result, .. } | Computation::Operation { result, .. } => result,
    }
}

fn pure_computation_result(computation: &Computation<PureOperations>) -> &Type {
    match computation {
        Computation::Pure { result, .. } => result,
        Computation::Operation { operation, .. } => match *operation {},
    }
}

fn primitive_program() -> (ValidatedProgram, NodeId) {
    let source = SourceFile::new("architecture.ash", "1 + 2").expect("test source");
    let range = ByteRange::new(0, 5).expect("ordered test range");
    let origin = Origin::Source(source.span(range).expect("test span"));
    let mut builder = CoreBuilder::new();
    let left = builder
        .integer(
            Integer::parse_decimal("1").expect("test integer"),
            Type::Int,
            origin.clone(),
        )
        .expect("small arena");
    let right = builder
        .integer(
            Integer::parse_decimal("2").expect("test integer"),
            Type::Int,
            origin.clone(),
        )
        .expect("small arena");
    let root = builder
        .primitive(Primitive::Add, left, right, Type::Int, origin)
        .expect("small arena");
    let program = validate(builder.finish(root).expect("valid root"), &[&source])
        .expect("valid test computation");
    (program, root)
}

fn pure_payload(program: &ValidatedProgram, root: NodeId) -> PureComputation {
    match &program.node(root).expect("validated root").kind {
        PureExprKind::Computation(computation) => computation.clone(),
        PureExprKind::Value(_) | PureExprKind::Variable(_) => {
            panic!("expected primitive computation")
        }
    }
}

mod mock_feature {
    use ash::types::Type;

    #[derive(Clone, Copy, Debug, Eq, PartialEq)]
    pub struct MockNode;

    impl MockNode {
        pub const fn expected_type(self) -> Type {
            Type::Unit
        }
    }
}

struct ShadowTypedExpr {
    ty: Type,
    kind: ShadowExprKind,
}

enum ShadowExprKind {
    Value(ShadowValue),
    Variable(VariableNode),
    Computation(ShadowPureComputation),
    Mock(mock_feature::MockNode),
}

enum ShadowValue {
    Integer(IntegerNode),
    Boolean(BooleanNode),
    Unit(UnitNode),
    Function(FunctionNode),
    Constructor(ConstructorNode),
}

enum ShadowPureComputation {
    Bind(BindingNode),
    RecursiveBind(RecursiveBindingNode),
    Apply(ApplicationNode),
    Primitive(PrimitiveNode),
    Tuple(TupleNode),
    Match(MatchNode),
    TypeAbstraction(TypeAbstractionNode),
    TypeApplication(TypeApplicationNode),
}

fn assemble_shadow(expression: &TypedExpr) -> ShadowTypedExpr {
    let kind = match &expression.kind {
        PureExprKind::Value(value) => ShadowExprKind::Value(match value {
            PureValue::Integer(node) => ShadowValue::Integer(node.clone()),
            PureValue::Boolean(node) => ShadowValue::Boolean(*node),
            PureValue::Unit(node) => ShadowValue::Unit(*node),
            PureValue::Function(node) => ShadowValue::Function(node.clone()),
            PureValue::Constructor(node) => ShadowValue::Constructor(*node),
        }),
        PureExprKind::Variable(node) => ShadowExprKind::Variable(*node),
        PureExprKind::Computation(computation) => ShadowExprKind::Computation(match computation {
            PureComputation::Bind(node) => ShadowPureComputation::Bind(node.clone()),
            PureComputation::RecursiveBind(node) => {
                ShadowPureComputation::RecursiveBind(node.clone())
            }
            PureComputation::Apply(node) => ShadowPureComputation::Apply(*node),
            PureComputation::Primitive(node) => ShadowPureComputation::Primitive(*node),
            PureComputation::Tuple(node) => ShadowPureComputation::Tuple(node.clone()),
            PureComputation::Match(node) => ShadowPureComputation::Match(node.clone()),
            PureComputation::TypeAbstraction(node) => {
                ShadowPureComputation::TypeAbstraction(node.clone())
            }
            PureComputation::TypeApplication(node) => {
                ShadowPureComputation::TypeApplication(node.clone())
            }
        }),
    };
    ShadowTypedExpr {
        ty: expression.ty.clone(),
        kind,
    }
}

fn mock_shadow() -> ShadowTypedExpr {
    ShadowTypedExpr {
        ty: Type::Unit,
        kind: ShadowExprKind::Mock(mock_feature::MockNode),
    }
}

struct ShadowFacts<'program> {
    program: &'program ValidatedProgram,
    binders: &'program HashMap<BinderId, Type>,
}

impl ShadowFacts<'_> {
    fn node_type(&self, node: NodeId) -> Option<&Type> {
        self.program.node(node).map(|expression| &expression.ty)
    }
}

fn validate_shadow(expression: &ShadowTypedExpr, facts: &ShadowFacts<'_>) -> bool {
    match &expression.kind {
        ShadowExprKind::Value(value) => validate_shadow_value(&expression.ty, value, facts),
        ShadowExprKind::Variable(variable) => {
            facts.binders.get(&variable.binder()) == Some(&expression.ty)
        }
        ShadowExprKind::Computation(computation) => {
            validate_shadow_computation(&expression.ty, computation, facts)
        }
        ShadowExprKind::Mock(node) => expression.ty == node.expected_type(),
    }
}

fn validate_shadow_value(ty: &Type, value: &ShadowValue, facts: &ShadowFacts<'_>) -> bool {
    match value {
        ShadowValue::Integer(node) => {
            let _ = node.value();
            *ty == Type::Int
        }
        ShadowValue::Boolean(node) => {
            let _ = node.value();
            *ty == Type::Bool
        }
        ShadowValue::Unit(_) => *ty == Type::Unit,
        ShadowValue::Function(node) => facts.node_type(node.body()).is_some_and(|body_type| {
            ty == &Type::Function(
                Box::new(node.parameter().ty().clone()),
                Box::new(body_type.clone()),
            )
        }),
        ShadowValue::Constructor(node) => {
            let _ = node.constructor();
            true
        }
    }
}

fn validate_shadow_computation(
    ty: &Type,
    computation: &ShadowPureComputation,
    facts: &ShadowFacts<'_>,
) -> bool {
    match computation {
        ShadowPureComputation::Bind(node) => {
            facts.node_type(node.initializer()) == Some(node.binder().ty())
                && facts.node_type(node.body()) == Some(ty)
        }
        ShadowPureComputation::RecursiveBind(node) => {
            !node.members().is_empty()
                && facts.node_type(node.body()) == Some(ty)
                && node.members().iter().all(|member| {
                    facts.node_type(member.initializer()) == Some(member.binder().ty())
                })
        }
        ShadowPureComputation::Apply(node) => {
            let Some(Type::Function(domain, codomain)) = facts.node_type(node.function()) else {
                return false;
            };
            facts.node_type(node.argument()) == Some(domain.as_ref()) && codomain.as_ref() == ty
        }
        ShadowPureComputation::Primitive(node) => {
            let (left, right, result) = match node.primitive() {
                Primitive::Add | Primitive::Multiply => (Type::Int, Type::Int, Type::Int),
                Primitive::Equal => (Type::Int, Type::Int, Type::Bool),
            };
            facts.node_type(node.left()) == Some(&left)
                && facts.node_type(node.right()) == Some(&right)
                && ty == &result
        }
        ShadowPureComputation::Tuple(node) => {
            let Type::Tuple(types) = ty else { return false };
            node.elements().len() == types.len()
                && node
                    .elements()
                    .iter()
                    .zip(types)
                    .all(|(element, expected)| facts.node_type(*element) == Some(expected))
        }
        ShadowPureComputation::Match(node) => {
            facts.node_type(node.scrutinee()).is_some()
                && node
                    .arms()
                    .iter()
                    .all(|arm| facts.node_type(arm.body()) == Some(ty))
        }
        ShadowPureComputation::TypeAbstraction(node) => {
            matches!(ty, Type::Forall(parameters, body)
                if parameters.as_ref() == node.parameters()
                    && facts.node_type(node.body()) == Some(body.as_ref()))
        }
        ShadowPureComputation::TypeApplication(node) => {
            !node.arguments().is_empty() && facts.node_type(node.function()).is_some()
        }
    }
}

fn traverse_shadow(expression: &ShadowTypedExpr) -> Vec<NodeId> {
    match &expression.kind {
        ShadowExprKind::Value(value) => match value {
            ShadowValue::Function(node) => vec![node.body()],
            ShadowValue::Integer(_)
            | ShadowValue::Boolean(_)
            | ShadowValue::Unit(_)
            | ShadowValue::Constructor(_) => Vec::new(),
        },
        ShadowExprKind::Variable(_) | ShadowExprKind::Mock(_) => Vec::new(),
        ShadowExprKind::Computation(computation) => match computation {
            ShadowPureComputation::Bind(node) => vec![node.initializer(), node.body()],
            ShadowPureComputation::RecursiveBind(node) => node
                .members()
                .iter()
                .map(|member| member.initializer())
                .chain(std::iter::once(node.body()))
                .collect(),
            ShadowPureComputation::Apply(node) => vec![node.function(), node.argument()],
            ShadowPureComputation::Primitive(node) => vec![node.left(), node.right()],
            ShadowPureComputation::Tuple(node) => node.elements().to_vec(),
            ShadowPureComputation::Match(node) => std::iter::once(node.scrutinee())
                .chain(node.arms().iter().map(|arm| arm.body()))
                .collect(),
            ShadowPureComputation::TypeAbstraction(node) => vec![node.body()],
            ShadowPureComputation::TypeApplication(node) => vec![node.function()],
        },
    }
}

#[derive(Debug, Eq, PartialEq)]
enum ShadowTransformPlan {
    Preserve(Vec<NodeId>),
    ReplaceWithMockUnit,
}

fn transform_shadow(expression: &ShadowTypedExpr) -> ShadowTransformPlan {
    match &expression.kind {
        ShadowExprKind::Value(value) => match value {
            ShadowValue::Function(node) => ShadowTransformPlan::Preserve(vec![node.body()]),
            ShadowValue::Integer(_)
            | ShadowValue::Boolean(_)
            | ShadowValue::Unit(_)
            | ShadowValue::Constructor(_) => ShadowTransformPlan::Preserve(Vec::new()),
        },
        ShadowExprKind::Variable(_) => ShadowTransformPlan::Preserve(Vec::new()),
        ShadowExprKind::Computation(computation) => match computation {
            ShadowPureComputation::Bind(node) => {
                ShadowTransformPlan::Preserve(vec![node.initializer(), node.body()])
            }
            ShadowPureComputation::RecursiveBind(node) => ShadowTransformPlan::Preserve(
                node.members()
                    .iter()
                    .map(|member| member.initializer())
                    .chain(std::iter::once(node.body()))
                    .collect(),
            ),
            ShadowPureComputation::Apply(node) => {
                ShadowTransformPlan::Preserve(vec![node.function(), node.argument()])
            }
            ShadowPureComputation::Primitive(node) => {
                ShadowTransformPlan::Preserve(vec![node.left(), node.right()])
            }
            ShadowPureComputation::Tuple(node) => {
                ShadowTransformPlan::Preserve(node.elements().to_vec())
            }
            ShadowPureComputation::Match(node) => ShadowTransformPlan::Preserve(
                std::iter::once(node.scrutinee())
                    .chain(node.arms().iter().map(|arm| arm.body()))
                    .collect(),
            ),
            ShadowPureComputation::TypeAbstraction(node) => {
                ShadowTransformPlan::Preserve(vec![node.body()])
            }
            ShadowPureComputation::TypeApplication(node) => {
                ShadowTransformPlan::Preserve(vec![node.function()])
            }
        },
        ShadowExprKind::Mock(_) => ShadowTransformPlan::ReplaceWithMockUnit,
    }
}

fn consume_shadow(expression: &ShadowTypedExpr) -> &'static str {
    match &expression.kind {
        ShadowExprKind::Value(value) => match value {
            ShadowValue::Integer(_) => "integer",
            ShadowValue::Boolean(_) => "boolean",
            ShadowValue::Unit(_) => "unit",
            ShadowValue::Function(_) => "function",
            ShadowValue::Constructor(_) => "constructor",
        },
        ShadowExprKind::Variable(_) => "variable",
        ShadowExprKind::Computation(computation) => match computation {
            ShadowPureComputation::Bind(_) => "binding",
            ShadowPureComputation::RecursiveBind(_) => "recursive binding",
            ShadowPureComputation::Apply(_) => "application",
            ShadowPureComputation::Primitive(_) => "primitive",
            ShadowPureComputation::Tuple(_) => "tuple",
            ShadowPureComputation::Match(_) => "match",
            ShadowPureComputation::TypeAbstraction(_) => "type abstraction",
            ShadowPureComputation::TypeApplication(_) => "type application",
        },
        ShadowExprKind::Mock(_) => "mock",
    }
}

struct Representative {
    program: ValidatedProgram,
    binders: HashMap<BinderId, Type>,
    one: NodeId,
    two: NodeId,
    primitive: NodeId,
    variable: NodeId,
    function: NodeId,
    application: NodeId,
    result_variable: NodeId,
    inner_binding: NodeId,
    boolean: NodeId,
    boolean_binding: NodeId,
    unit: NodeId,
    root: NodeId,
}

fn representative_program() -> Representative {
    let source = SourceFile::new("shadow.ash", "representative").expect("test source");
    let range = ByteRange::new(0, 14).expect("ordered test range");
    let origin = Origin::Source(source.span(range).expect("test span"));
    let mut builder = CoreBuilder::new();
    let one = builder
        .integer(
            Integer::parse_decimal("1").expect("test integer"),
            Type::Int,
            origin.clone(),
        )
        .expect("small arena");
    let two = builder
        .integer(
            Integer::parse_decimal("2").expect("test integer"),
            Type::Int,
            origin.clone(),
        )
        .expect("small arena");
    let primitive = builder
        .primitive(Primitive::Add, one, two, Type::Int, origin.clone())
        .expect("small arena");
    let parameter = builder
        .binder(Type::Int, origin.clone())
        .expect("small binder set");
    let variable = builder
        .variable(parameter.id(), Type::Int, origin.clone())
        .expect("small arena");
    let function = builder
        .function(
            parameter.clone(),
            variable,
            Type::Function(Box::new(Type::Int), Box::new(Type::Int)),
            origin.clone(),
        )
        .expect("small arena");
    let application = builder
        .application(function, primitive, Type::Int, origin.clone())
        .expect("small arena");
    let result_binder = builder
        .binder(Type::Int, origin.clone())
        .expect("small binder set");
    let result_variable = builder
        .variable(result_binder.id(), Type::Int, origin.clone())
        .expect("small arena");
    let inner_binding = builder
        .binding(
            result_binder.clone(),
            application,
            result_variable,
            Type::Int,
            origin.clone(),
        )
        .expect("small arena");
    let boolean = builder
        .boolean(true, Type::Bool, origin.clone())
        .expect("small arena");
    let boolean_binder = builder
        .binder(Type::Bool, origin.clone())
        .expect("small binder set");
    let boolean_binding = builder
        .binding(
            boolean_binder.clone(),
            boolean,
            inner_binding,
            Type::Int,
            origin.clone(),
        )
        .expect("small arena");
    let unit = builder
        .unit(Type::Unit, origin.clone())
        .expect("small arena");
    let unit_binder = builder
        .binder(Type::Unit, origin.clone())
        .expect("small binder set");
    let root = builder
        .binding(
            unit_binder.clone(),
            unit,
            boolean_binding,
            Type::Int,
            origin,
        )
        .expect("small arena");
    let program = validate(builder.finish(root).expect("valid root"), &[&source])
        .expect("valid representative program");
    let binders = HashMap::from([
        (parameter.id(), parameter.ty().clone()),
        (result_binder.id(), result_binder.ty().clone()),
        (boolean_binder.id(), boolean_binder.ty().clone()),
        (unit_binder.id(), unit_binder.ty().clone()),
    ]);

    Representative {
        program,
        binders,
        one,
        two,
        primitive,
        variable,
        function,
        application,
        result_variable,
        inner_binding,
        boolean,
        boolean_binding,
        unit,
        root,
    }
}

#[test]
fn pure_dialect_is_named_and_has_no_inhabited_operation_family() {
    assert_eq!(AshPureDialect::NAME, "ash.pure");

    let (program, root) = primitive_program();
    let pure = Computation::<PureOperations>::Pure {
        result: Type::Int,
        computation: pure_payload(&program, root),
    };
    assert_eq!(pure_computation_result(&pure), &Type::Int);
    let Computation::Pure { computation, .. } = pure;
    assert!(matches!(computation, PureComputation::Primitive(_)));
}

#[test]
fn future_operation_crosses_one_boundary_without_changing_pure_features() {
    let request = Computation::<MockFutureOperations>::Operation {
        result: Type::Unit,
        operation: MockFutureOperation::YieldOnce,
    };
    assert_eq!(computation_result(&request), &Type::Unit);
    let Computation::Operation { operation, .. } = request else {
        panic!("expected mock operation")
    };
    assert_eq!(operation, MockFutureOperation::YieldOnce);

    let unchanged_pure_node = PureExprKind::Value(PureValue::Unit(UnitNode));
    assert!(matches!(
        unchanged_pure_node,
        PureExprKind::Value(PureValue::Unit(_))
    ));
}

#[test]
fn one_mock_pure_feature_changes_only_the_recorded_closed_sites() {
    let representative = representative_program();
    let facts = ShadowFacts {
        program: &representative.program,
        binders: &representative.binders,
    };
    let cases = [
        (representative.one, "integer", vec![]),
        (representative.two, "integer", vec![]),
        (
            representative.primitive,
            "primitive",
            vec![representative.one, representative.two],
        ),
        (representative.variable, "variable", vec![]),
        (
            representative.function,
            "function",
            vec![representative.variable],
        ),
        (
            representative.application,
            "application",
            vec![representative.function, representative.primitive],
        ),
        (representative.result_variable, "variable", vec![]),
        (
            representative.inner_binding,
            "binding",
            vec![representative.application, representative.result_variable],
        ),
        (representative.boolean, "boolean", vec![]),
        (
            representative.boolean_binding,
            "binding",
            vec![representative.boolean, representative.inner_binding],
        ),
        (representative.unit, "unit", vec![]),
        (
            representative.root,
            "binding",
            vec![representative.unit, representative.boolean_binding],
        ),
    ];
    for (id, label, children) in cases {
        let shadow = assemble_shadow(representative.program.node(id).expect("validated node"));
        assert!(validate_shadow(&shadow, &facts));
        assert_eq!(traverse_shadow(&shadow), children);
        assert_eq!(
            transform_shadow(&shadow),
            ShadowTransformPlan::Preserve(children)
        );
        assert_eq!(consume_shadow(&shadow), label);
    }

    let mock = mock_shadow();
    assert!(validate_shadow(&mock, &facts));
    assert_eq!(traverse_shadow(&mock), Vec::<NodeId>::new());
    assert_eq!(
        transform_shadow(&mock),
        ShadowTransformPlan::ReplaceWithMockUnit
    );
    assert_eq!(consume_shadow(&mock), "mock");
}
