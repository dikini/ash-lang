use std::{
    cell::Cell,
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use ash::{
    core::{
        AshEffectDialect, AshPureDialect, CoreBuilder, EffectExprKind, EffectOperation,
        NewtypeConversionDirection, NodeId, Primitive, PureComputation, PureExprKind, PureValue,
        TypedExpr, ValidatedProgram,
        binding::BindingNode,
        data::{ConstructorNode, MatchNode, TupleNode},
        function::{ApplicationNode, FunctionNode},
        literal::{BooleanNode, IntegerNode, UnitNode},
        primitive::PrimitiveNode,
        recursion::RecursiveBindingNode,
        type_ops::{NewtypeConversionNode, TypeAbstractionNode, TypeApplicationNode},
        validate,
        variable::VariableNode,
    },
    elaborate::{EffectElaborator, check_module, link_modules},
    evidence_validation::validate_interface_evidence,
    integer::Integer,
    module::{ModuleRoots, load_module_graph},
    resolve::{DependencyExports, resolve_module},
    resolved::{BinderId, CheckedModule, ResolvedNominalDeclarationKind},
    source::{ByteRange, Origin, SourceFile, Span},
    types::{Kind, Type},
};

#[test]
fn effect_row_carriers_have_one_shared_owner_gate_and_no_core_side_table() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let kind =
        fs::read_to_string(root.join("src/kind.rs")).expect("kind source should be readable");
    let types =
        fs::read_to_string(root.join("src/types.rs")).expect("type source should be readable");

    assert!(kind.contains("fn binder_kind_is_admitted"));
    assert!(kind.contains("EffectRow cannot occur beneath a kind arrow"));
    assert!(types.contains("pub struct ComputationType"));
    assert!(types.contains("pub struct EffectRow"));
    assert!(!types.contains("effect_row_side_table"));
}

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
    CoreTreeAndResolvedTreeAndRegistryTree,
    CheckedTreeAndSummaryTreeAndTransientWork,
    TypeTreeAndResolvedTreeAndRegistryTree,
    CoreTreeAndResolvedTreeAndRegistryTreeAndTransientWork,
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
    // Build/image work uses the cumulative TypeWorkBudget. Borrowed encoder
    // trees and identity indices retain original owners; restored buffers guard
    // canonical trees until final independent Core admission transfers them.
    FieldBuildTypeAndKindBorrow => (Field, Borrowed, Canonical, CarrierRetention, PreservedCarrier, CoreAdmission, Type, TypeTreeAndKindTree),
    FieldCompletedFactShared => (Field, Shared, Checked, CarrierRetention, PreservedCarrier, Resolution, ResolutionType, CheckedTree),
    FieldBuildKindBorrow => (Field, Borrowed, Canonical, CarrierRetention, PreservedCarrier, CoreAdmission, Type, KindTree),
    FieldBuildTypeOwned => (Field, Owned, Canonical, CarrierRetention, PreservedCarrier, CoreAdmission, Type, TypeTree),
    FieldBuildNativeFactsShared => (Field, Shared, Core, CarrierRetention, PreservedCarrier, CoreAdmission, Type, TypeTreeAndResolvedTreeAndRegistryTree),
    FieldBuildNativeFactsBorrow => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, CoreAdmission, Type, TypeTreeAndResolvedTreeAndRegistryTree),
    FieldBuildProgramShared => (Field, Shared, Core, CarrierRetention, PreservedCarrier, CoreAdmission, Type, CoreTreeAndResolvedTreeAndRegistryTree),
    // Native Core stores complete actuals separately from shared original facts.
    // Replay owns a fallible metadata copy; the independently authenticated
    // registry brand only borrows its existing canonical owner.
    FieldNativeCoreFactsShared => (Field, Shared, Core, CarrierRetention, PreservedCarrier, CoreAdmission, CoreType, TypeTreeAndResolvedTreeAndRegistryTree),
    FieldNativeCoreMixed => (Field, Mixed, Core, CarrierRetention, PreservedCarrier, CoreAdmission, CoreType, CoreTreeAndResolvedTreeAndRegistryTree),
    FieldNativeReplayMixed => (Field, Mixed, Transient, CarrierRetention, PreservedCarrier, CoreAdmission, CoreType, CoreTreeAndResolvedTreeAndRegistryTreeAndTransientWork),
    // Slim bindings share prepared symbol facts whose signature owns a Type tree.
    FieldNativeBindingsShared => (Field, Shared, Registry, CarrierRetention, PreservedCarrier, Evaluation, Evaluation, TypeTree),
    FieldNativeBindingBorrow => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, Evaluation, Evaluation, TypeTreeAndResolvedTreeAndRegistryTree),
    FieldNativeProgramBorrow => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, Evaluation, Evaluation, CoreTreeAndResolvedTreeAndRegistryTree),
    // Actual module publication: summaries share only defining certificates;
    // checked code owners separately retain Core, canonical context and facts.
    FieldProviderEvidenceFactsBorrow => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, EvidenceValidation, EvidenceType, SummaryTree),
    // Provider entry borrows leave disposal with the actual source owners:
    // resolved declarations/occurrences, draft Core plus its shared registry,
    // canonical registry Arcs, standalone types/kinds, and capture summaries.
    // Mixed entry aggregates include those distinct owners, while staged
    // publication also retains evidence selections and temporary type buffers.
    FieldProviderKindBorrow => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, CoreValidation, CoreType, KindTree),
    FieldOwnerKindRegistryBorrow => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, ResolvedKind, ResolutionType, RegistryTree),
    FieldOwnerKindTraversalBorrow => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, TypeOperation, Type, TypeTreeAndKindTree),
    FieldProviderRegistryBorrow => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, CoreValidation, CoreType, RegistryTree),
    // Conditional code retains a typed forest, canonical registry and opaque
    // capture graphs. Body-free contracts own rows/kinds and defining import
    // facts; they confer no ordinary Core or publication authority.
    FieldConditionalCaptureMixed => (Field, Mixed, Core, CarrierRetention, PreservedCarrier, CoreValidation, CoreType, SummaryTree),
    // Source occurrences borrow checked imported summaries and own temporary
    // argument/row/adapter buffers. The full external proof additionally borrows
    // Core and resolved entry roots and retains shared capture/registry owners.
    FieldProviderElaborationCoreOwned => (Field, Owned, Transient, CarrierRetention, PreservedCarrier, Elaboration, InferenceType, CoreTree),
    FieldProviderGlobalsMixed => (Field, Mixed, Transient, CarrierRetention, PreservedCarrier, Elaboration, InferenceType, CheckedTreeAndSummaryTreeAndTransientWork),
    // Foreign preparation fixes authored flat kinds before resolved binding;
    // the immutable preparation owns these Kind trees, even when shared by Arc.
    FieldForeignBindingRegistryBorrow => (Field, Borrowed, Registry, CarrierRetention, PreservedCarrier, Resolution, ResolutionType, RegistryTree),
    // Private build encoding borrows checked trees; reconstruction guards own
    // staged records under the same cumulative TypeWorkBudget and Core gate.
    FieldBuildCoreBorrow => (Field, Borrowed, Core, CarrierRetention, PreservedCarrier, CoreAdmission, Type, CoreTree),
    FieldBuildTypeBorrow => (Field, Borrowed, Canonical, CarrierRetention, PreservedCarrier, CoreAdmission, Type, TypeTree),
    FieldBuildCoreOwned => (Field, Owned, Core, CarrierRetention, PreservedCarrier, CoreAdmission, Type, CoreTree),
    FieldBuildRegistryOwned => (Field, Owned, Registry, CarrierRetention, PreservedCarrier, CoreAdmission, Type, RegistryTree),
    // Restored registries own canonical trees and share original native facts.
    FieldBuildRegistryMixed => (Field, Mixed, Registry, CarrierRetention, PreservedCarrier, CoreAdmission, Type, RegistryTree),
    FieldForeignTypesOwned => (Field, Owned, Resolved, CarrierRetention, PreservedCarrier, Resolution, ResolutionType, TypeTree),
    FieldForeignFactsShared => (Field, Shared, Summary, CarrierRetention, PreservedCarrier, Resolution, ResolutionType, TypeTreeAndResolvedTreeAndRegistryTree),
    FieldResourceFactsShared => (Field, Shared, Summary, CarrierRetention, PreservedCarrier, Resolution, ResolutionType, ResolvedTree),
    // Source headers share original resolved facts and checked native owners.
    // Immutable template forests own Core beside those shared allocations;
    // copying claims borrow them while final scopes retain exact substitutions.
    // Ordinary global schemes are owned iteratively and loaned to original
    // source forests; final Core closes each loan against its lexical binder.
    // Unique runtime guards own native destruction obligations but share their
    // immutable Type/Kind authority. Request receipts additionally own complete
    // actual vectors; returned phases retain no native invocation capability.

    FieldMixedCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTreeAndRegistryTree => (Field, Mixed, Core, CarrierRetention, PreservedCarrier, CoreAdmission, CoreType, CoreTreeAndRegistryTree),
    FieldMixedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTreeAndTransientWork => (Field, Mixed, Transient, CarrierRetention, PreservedCarrier, CoreValidation, CoreType, CoreTreeAndTransientWork),
    FieldMixedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTreeAndTransientWork => (Field, Mixed, Transient, CarrierRetention, PreservedCarrier, Elaboration, InferenceType, ResolvedTreeAndTransientWork),
    FieldMixedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTreeAndTransientWork => (Field, Mixed, Transient, CarrierRetention, PreservedCarrier, EvidenceSelection, EvidenceType, EvidenceTreeAndTransientWork),
    FieldMixedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork => (Field, Mixed, Transient, CarrierRetention, PreservedCarrier, EvidenceSelection, EvidenceType, TransientWork),
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
    FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeResolvedTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, EvidenceValidation, EvidenceType, ResolvedTree),
    FieldBorrowedTransientInterfaceArgumentInterfaceParameterEvidenceSelectionEvidenceTypeTypeTree => (Field, Borrowed, Transient, InterfaceArgument, InterfaceParameter, EvidenceSelection, EvidenceType, TypeTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, InterfaceValidation, InterfaceType, CheckedTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeTypeTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, InterfaceValidation, InterfaceType, TypeTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, Resolution, ResolutionType, SummaryTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, Resolution, ResolutionType, SurfaceTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierPatternCoveragePatternCoverageTypeTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, PatternCoverage, PatternCoverage, TypeTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierPatternCoveragePatternCoverageCoreTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, PatternCoverage, PatternCoverage, CoreTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, TypeOperation, Type, TypeTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeSummaryTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, TypeOperation, Type, SummaryTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeRegistryTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, TypeOperation, Type, RegistryTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, TypeOperation, Kind, KindTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, ResolvedKind, ResolutionType, KindTree),
    FieldBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeResolvedTree => (Field, Borrowed, Transient, CarrierRetention, PreservedCarrier, ResolvedKind, ResolutionType, ResolvedTree),
    FieldBorrowedTransientInterfaceArgumentInterfaceParameterResolvedKindResolutionTypeResolvedTree => (Field, Borrowed, Transient, InterfaceArgument, InterfaceParameter, ResolvedKind, ResolutionType, ResolvedTree),
    FieldCanonicalApplicationStructureStructuralSubtreeTypeOperationTypeTypeTree => (Field, Owned, Canonical, ApplicationStructure, StructuralSubtree, TypeOperation, Type, TypeTree),
    FieldCanonicalKindStructureKindSubtreeTypeOperationKindKindTree => (Field, Owned, Canonical, KindStructure, KindSubtree, TypeOperation, Kind, KindTree),
    FieldCanonicalSchemeSchemeValueTypeOperationTypeTypeTree => (Field, Owned, Canonical, Scheme, SchemeValue, TypeOperation, Type, TypeTree),
    FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree => (Field, Owned, Checked, CarrierRetention, PreservedCarrier, Elaboration, InferenceType, CheckedTree),
    FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree => (Field, Owned, Checked, CarrierRetention, PreservedCarrier, InterfaceValidation, InterfaceType, CheckedTree),
    FieldCheckedDeclaredKindDeclaredInterfaceValidationInterfaceTypeCheckedTree => (Field, Owned, Checked, DeclaredKind, Declared, InterfaceValidation, InterfaceType, CheckedTree),
    FieldCheckedInterfaceArgumentInterfaceParameterInterfaceValidationInterfaceTypeCheckedTree => (Field, Owned, Checked, InterfaceArgument, InterfaceParameter, InterfaceValidation, InterfaceType, CheckedTree),
    FieldCheckedSchemeSchemeValueInterfaceValidationInterfaceTypeCheckedTree => (Field, Owned, Checked, Scheme, SchemeValue, InterfaceValidation, InterfaceType, CheckedTree),
    FieldCheckedValueTypeValueInterfaceValidationInterfaceTypeCheckedTree => (Field, Owned, Checked, ValueType, Value, InterfaceValidation, InterfaceType, CheckedTree),
    FieldTransientCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeTransientWork => (Field, Owned, Transient, CarrierRetention, PreservedCarrier, InterfaceValidation, InterfaceType, TransientWork),
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
    // Speculative row choices share immutable tasks and rows; their final owners
    // retain the existing iterative argument/Type/row disposal boundaries.
    FieldSharedUnificationWork => (Field, Shared, Transient, CarrierRetention, PreservedCarrier, Elaboration, InferenceType, TransientWork),
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
    // Current ordinary originals, row-image data and borrowed traversal carriers.
    kind_site!("src/evidence_validation/lexical_sources.rs::LinkedLexicalSource.Declared.0", FieldProviderEvidenceFactsBorrow),
    kind_site!("src/core/transform.rs::$fn_rebuild_pattern::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/transform.rs::$fn_rebuild_pattern::Task.FinishTuple.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/transform.rs::$fn_rebuild_pattern::Task.FinishConstructor.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/elaborate.rs::$fn_check_newtype_representation_cycles::$block_163_1::Value.Argument.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork, Borrowed),
    kind_site!("src/elaborate.rs::$fn_check_newtype_representation_cycles::$block_163_1::Value.Type.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork, Borrowed),
    kind_site!("src/build/image.rs::ArgumentBuffer.0", FieldBuildTypeOwned),
    kind_site!("src/build/image.rs::DecodedRow.value", FieldBuildTypeOwned),
    kind_site!("src/build/image.rs::Decoder.decoded_rows", FieldBuildTypeOwned),
    kind_site!("src/build/image_row_order.rs::$impl_Encoder::$fn_row_order_key::Task.Visit.0", FieldBuildTypeAndKindBorrow),
    kind_site!("src/build/image_row_order.rs::Input.Kind.0", FieldBuildKindBorrow),
    kind_site!("src/build/image_row_order.rs::Input.Structural.0", FieldBuildTypeBorrow),
    kind_site!("src/core/capture/control.rs::PrepaidControlCodeScan.graph", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/foreign/source_bindings.rs::NativeBinding.symbol", FieldNativeBindingsShared),
    kind_site!("src/resolved.rs::AuthorizedImplementationFact.publication", FieldCompletedFactShared),
    kind_site!("src/resolved.rs::ExportedGlobal.publication", FieldCompletedFactShared),
    kind_site!("src/resolved.rs::ImportedGlobalScheme.publication", FieldCompletedFactShared),
    kind_site!("src/resolved.rs::ImportedImplementationFact.publication", FieldCompletedFactShared),
    kind_site!("src/resolved.rs::ConstructorOriginal.$alias", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree, Shared),
    kind_site!("src/resolved.rs::ExportedConstructor.original", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree, Shared),
    kind_site!("src/resolved.rs::ImportedConstructorFact.original", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree, Shared),
    kind_site!("src/resolved/constructor_original.rs::ConstructorOriginal.0", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree, Shared),
    // Generic acquisition/row replay and runtime roots retain existing owner categories.
    kind_site!("src/core/effect.rs::$impl_CoreBuilder::$fn_replay_effect_rows_in_range::Equation.Resource.0", FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/eval/machine.rs::Frame.ResourceBoundary.payload", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Mixed),
    kind_site!("src/eval/machine.rs::ResourcePayload.Generic.instance", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState),
    kind_site!("src/eval/machine.rs::ResourcePayload.Generic.value", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/resolve.rs::ResolveTask.FinishResource.payload", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ResolveTask.GenericResourceInitializer.source", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::ResolvedCellPayloadOwner.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),

    // Image and source carriers retain their current physical owners.
    // Borrowed views, shared facts and owned buffers keep separate profiles.
    kind_site!("src/build/image.rs::DecodedType.value", FieldBuildTypeOwned),
    kind_site!("src/build/image.rs::Decoder.decoded_types", FieldBuildTypeOwned),
    kind_site!("src/build/image.rs::Decoder.source_declaration_catalogs", FieldBuildProgramShared),

    // Original provider catalogue construction borrows the resolved module,
    // checked interface facts and canonical registry without retaining copies.
    // Source resource headers, immutable defining forests, final copying claims,
    // and native owner receipts retain the owners of their completed phase.
    // Source control originals, complete row claims and borrowed graph views.
    // Source readiness and flat host storage share the exact original status
    // symbol. Its existing checked owner disposes Type/Row facts iteratively;
    // the finite scalar branches own no type tree or recursive guard edge.

    // Optional header verification borrows original passive facts; it carries no
    // executable contract or new recursive owner. Source failures reuse the
    // existing iterative pipeline diagnostic owner below.
    kind_site!("src/resolved.rs::$impl_ResolvedRegistry::$fn_with_image_interface_owner_definitions::Pending.0", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree),
    kind_site!("src/resolved.rs::$impl_ResolvedRegistry::$fn_with_image_source_parameters::Parameter.0", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree),
    // Flow proofs borrow original typed inputs. Flat storage owns canonical
    // state/access trees through iterative guards; views and phase receipts share
    // that storage. No slot owns another slot or a recursive native-owner chain.
    // Connected native image reconstruction, exact original brands and bridge plans.
    kind_site!("src/build/bridge.rs::TargetResolvedForeignBridge.symbol", FieldBuildNativeFactsShared),
    kind_site!("src/build/image.rs::NativeBridgeEmission.plan", FieldBuildNativeFactsShared),
    kind_site!("src/build/image.rs::NativeBuildImage.bridges", FieldBuildNativeFactsShared),
    kind_site!("src/build/image.rs::Encoder.original_native_symbols", FieldBuildNativeFactsShared),
    kind_site!("src/build/image.rs::RestoredEffectImage.symbols", FieldBuildNativeFactsShared),
    kind_site!("src/build/image.rs::RestoredNativeRegistry.symbols", FieldBuildNativeFactsShared),
    kind_site!("src/build/image.rs::Encoder.native_symbols", FieldBuildNativeFactsBorrow),
    kind_site!("src/build/image.rs::RestoredEffectImage.program", FieldBuildProgramShared),
    kind_site!("src/build/image.rs::ParameterBuffer.0", FieldBuildRegistryOwned),
    kind_site!("src/build/image.rs::NominalParameterBuffer.0", FieldBuildRegistryOwned),
    kind_site!("src/build/image.rs::GlobalParameterBuffer.0", FieldBuildRegistryOwned),
    kind_site!("src/build/image.rs::RestoredNativeRegistry.registry", FieldBuildRegistryMixed),
    kind_site!("src/build/image.rs::TypeBuffer.0", FieldBuildTypeOwned),
    kind_site!("src/build/image.rs::ArgumentOwner.0", FieldBuildTypeOwned),
    kind_site!("src/build/image.rs::StructuralOwner.Type.0", FieldBuildTypeOwned),
    kind_site!("src/build/image.rs::StructuralOwner.Row.0", FieldBuildTypeOwned),
    kind_site!("src/build/image.rs::StructuralOwner.Instance.0", FieldBuildTypeOwned),
    kind_site!("src/build/image.rs::StructuralOwner.Argument.0", FieldBuildTypeOwned),
    kind_site!("src/build/image.rs::StructuralInput.Type.0", FieldBuildTypeBorrow),
    kind_site!("src/build/image.rs::StructuralInput.Row.0", FieldBuildTypeBorrow),
    kind_site!("src/build/image.rs::StructuralInput.Instance.0", FieldBuildTypeBorrow),
    kind_site!("src/build/image.rs::StructuralInput.Argument.0", FieldBuildTypeBorrow),
    kind_site!("src/build/image.rs::$impl_Encoder::$fn_encode_structural::Task.Visit.0", FieldBuildTypeBorrow),
    kind_site!("src/build/image.rs::$impl_Encoder::$fn_encode_kind::Task.Visit.0", FieldBuildKindBorrow),
    // Connected source-native Core boundary, captured environments and consuming phases.
    kind_site!("src/core/effect.rs::NativeInterpretation.effect", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/effect.rs::NativeInterpretation.symbol", FieldNativeCoreFactsShared),
    kind_site!("src/core/effect.rs::NativeInterpretNode.interpretations", FieldNativeCoreMixed),
    kind_site!("src/core/effect.rs::EffectOperation.NativeInterpret.0", FieldNativeCoreMixed),
    kind_site!("src/core/mod.rs::NativeInterpretNode.$alias", FieldNativeCoreMixed),
    kind_site!("src/core/mod.rs::NativeInterpretation.$alias", FieldNativeCoreMixed),
    kind_site!("src/core/effect.rs::$impl_CoreBuilder::$fn_replay_effect_rows_in_range::Equation.NativeInterpret.1", FieldNativeReplayMixed),
    kind_site!("src/core/validate.rs::AuthenticatedNativeRegistry.registry", FieldProviderRegistryBorrow),
    kind_site!("src/core/capture/control.rs::Control.NativeInterpret.effects", FieldSummaryCarrierRetentionPreservedCarrierElaborationInferenceTypeSummaryTree, Shared),
    kind_site!("src/eval/machine.rs::Frame.NativeInterpretBoundary.environment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Machine.source_bindings", FieldNativeBindingBorrow),
    kind_site!("src/foreign/source_bindings.rs::SourceNativeBindings.entries", FieldNativeBindingsShared),
    kind_site!("src/foreign/source_runtime.rs::SourceNativeBindings.$alias", FieldNativeBindingsShared),
    kind_site!("src/foreign/source_bindings.rs::AdmittedSourceNativeProgram.bindings", FieldNativeBindingBorrow),
    kind_site!("src/foreign/source_bindings.rs::AdmittedSourceNativeProgram.program", FieldNativeProgramBorrow),
    kind_site!("src/foreign/source_runtime.rs::AdmittedSourceNativeProgram.$alias", FieldNativeProgramBorrow),
    // Connected source-native, compiled-program and private build carriers.
    // Native tables share original descriptors; declaration/phase guards retain
    // owned records alongside shared facts and dismantle partial work iteratively.
    kind_site!("src/build/host.rs::BuildFailure.0", FieldTransientCarrierRetentionPreservedCarrierPipelineObservationPipelineTypeObservation),
    kind_site!("src/build/host.rs::Failure.Source.0", FieldTransientCarrierRetentionPreservedCarrierPipelineObservationPipelineTypeObservation),
    kind_site!("src/build/image.rs::$impl_Encoder::$fn_encode_pattern::Task.Finish.0", FieldBuildCoreBorrow),
    kind_site!("src/build/image.rs::$impl_Encoder::$fn_encode_pattern::Task.Visit.0", FieldBuildCoreBorrow),
    kind_site!("src/build/image.rs::ConstructorBuffer.0", FieldBuildRegistryOwned),
    kind_site!("src/build/image.rs::NominalBuffer.0", FieldBuildRegistryOwned),
    kind_site!("src/build/image.rs::PatternOwner.0", FieldBuildCoreOwned),
    kind_site!("src/build/mod.rs::BuildFailure.$alias", FieldTransientCarrierRetentionPreservedCarrierPipelineObservationPipelineTypeObservation),
    kind_site!("src/build/mod.rs::PrivateProgramOutput.0", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/driver.rs::CompiledCore.Effect.0", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree, Shared),
    kind_site!("src/driver.rs::CompiledCore.Pure.0", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree, Shared),
    kind_site!("src/driver.rs::CompiledProgram.core", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree, Shared),
    kind_site!("src/driver.rs::CompiledProgram.ty", FieldTransientValueTypeValuePipelineObservationPipelineTypeObservation),
    kind_site!("src/driver.rs::ObservationMetadata.ty", FieldTransientValueTypeValuePipelineObservationPipelineTypeObservation),
    kind_site!("src/foreign/checked_source.rs::CheckedForeignSymbol.source_signature", FieldForeignTypesOwned),
    // Scalar preflights own their original resolved annotation under the
    // iterative fact destructor; publication shares that same immutable fact.
    // The codec and source origins contain no Type/Kind carrier edges.
    kind_site!("src/foreign/checked_source.rs::ForeignBindingContext.registry", FieldForeignBindingRegistryBorrow),
    kind_site!("src/resolve.rs::$impl_Resolver::$fn_resolve_effect_declarations::ParameterRows.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ImportedTypeVariableRows.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::PendingImplementationBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::PreparedDeclarationSetup.effects", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::PreparedDeclarationSetup.global_type_parameters", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::PreparedDeclarationSetup.pending_implementations", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::PreparedDeclarationSetup.registry", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree, Mixed),
    kind_site!("src/resolve/foreign.rs::EffectSource.Foreign.symbol", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve/foreign.rs::EffectSource.Ordinary.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve/foreign.rs::OperationSource.annotation", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolved.rs::ExportSummary.native_symbols", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree, Shared),
    kind_site!("src/resolved.rs::ImportedFacts.native_symbols", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree, Shared),
    kind_site!("src/resolved.rs::ResolvedEffectBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolved.rs::ResolvedEffectDeclaration.native_contract", FieldForeignFactsShared),
    kind_site!("src/resolved.rs::ResolvedEffectOperationBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::ResolvedRegistry.native_symbols", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree, Shared),
    kind_site!("src/surface.rs::SurfaceForeignLibrary.$alias", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceForeignMember.$alias", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceForeignSymbol.$alias", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceModule.foreign_libraries", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface/foreign.rs::SurfaceForeignLibrary.members", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface/foreign.rs::SurfaceForeignMember.Symbol.0", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface/foreign.rs::SurfaceForeignSymbol.ty", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    // Diagnostic visits borrow written surface records; the source graph owns disposal.
    kind_site!("src/calibration_features.rs::Visit.Nominal.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree, Borrowed),
    kind_site!("src/calibration_features.rs::Visit.Definition.0", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree, Borrowed),
    kind_site!("src/calibration_features.rs::Visit.Equation.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree, Borrowed),
    kind_site!("src/calibration_features.rs::Visit.Block.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree, Borrowed),
    kind_site!("src/calibration_features.rs::Visit.Local.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree, Borrowed),
    kind_site!("src/calibration_features.rs::Visit.Expr.0", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree, Borrowed),
    kind_site!("src/calibration_features.rs::Visit.Type.0", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree, Borrowed),
    kind_site!("src/calibration_features.rs::Visit.Kind.0", FieldSurfaceDeclaredKindDeclaredProjectionProjectionSurfaceTree, Borrowed),
    kind_site!("src/calibration_features.rs::Visit.Parameter.0", FieldSurfaceDeclaredKindDeclaredProjectionProjectionSurfaceTree, Borrowed),
    kind_site!("src/calibration_features.rs::Visit.Row.0", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree, Borrowed),
    kind_site!("src/calibration_features.rs::Visit.Effect.0", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree, Borrowed),
    kind_site!("src/calibration_features.rs::Visit.Application.0", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree, Borrowed),
    kind_site!("src/calibration_features.rs::Visit.Handler.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree, Borrowed),
    // Scalar layout and family carriers retain original authority and exact owner metadata.
    kind_site!("src/resolve.rs::$impl_Resolver::$fn_resolve_resource_family::Parts.interpreted", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::$impl_Resolver::$fn_resolve_resource_family::Parts.provided", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::$impl_Resolver::$fn_resolve_resource_family::Parts.provider", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::$impl_Resolver::$fn_resolve_resource_family::Parts.requirements", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::$impl_Resolver::$fn_resolve_resource_handlers::Clauses.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolved.rs::ResolvedResourceDefinition.family_template", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedResourceFamilyTemplate.handlers", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedResourceFamilyTemplate.interpreted", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedResourceFamilyTemplate.parameter", FieldResolvedDeclaredKindDeclaredResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedResourceFamilyTemplate.provided", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedResourceFamilyTemplate.provider", FieldResolvedInterfaceArgumentInterfaceParameterResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedResourceFamilyTemplate.requirements", FieldResolvedInterfaceArgumentInterfaceParameterResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResourceFamilyTypeFact.interpreted", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResourceFamilyTypeFact.parameter", FieldResolvedDeclaredKindDeclaredResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResourceFamilyTypeFact.provided", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResourceFamilyTypeFact.provider", FieldResolvedInterfaceArgumentInterfaceParameterResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResourceFamilyTypeFact.provider_application", FieldResolvedInterfaceArgumentInterfaceParameterResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResourceFamilyTypeFact.requirements", FieldResolvedInterfaceArgumentInterfaceParameterResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResourceTypeFact.family_template", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/surface.rs::SurfaceResourceDefinition.family", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceResourceFamily.handlers", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceResourceFamily.interpreted", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceResourceFamily.parameter", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceResourceFamily.provided", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceResourceFamily.provider", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceResourceFamily.requirements", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    // Fused borrowed zonking retains source nodes and guards owned results.
    kind_site!("src/elaborate.rs::$fn_zonk_compound_root_with_status_and_inference_and_rows::Task.Type.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_zonk_compound_root_with_status_and_inference_and_rows::Task.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_zonk_compound_root_with_status_and_inference_and_rows::Task.Row.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_zonk_compound_root_with_status_and_inference_and_rows::Task.Instance.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_zonk_compound_root_with_status_and_inference_and_rows::Task.Types.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_zonk_compound_root_with_status_and_inference_and_rows::Task.Arguments.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_zonk_compound_root_with_status_and_inference_and_rows::Task.Instances.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_zonk_compound_root_with_status_and_inference_and_rows::Value.Type.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$fn_zonk_compound_root_with_status_and_inference_and_rows::Value.Argument.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$fn_zonk_compound_root_with_status_and_inference_and_rows::Value.Row.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$fn_zonk_compound_root_with_status_and_inference_and_rows::Value.Instance.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$fn_zonk_compound_root_with_status_and_inference_and_rows::Parameters.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$fn_zonk_compound_root_with_status_and_inference_and_rows::Task.Forall.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$fn_zonk_compound_root_with_status_and_inference_and_rows::$fn_clone_kind::KindTask.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeKindTree),
    // Complete owner arguments preserve ordered Type/row payloads at each boundary.
    // Borrowed traversal tasks retain source authority; reconstruction buffers own
    // guarded fragments and use iterative disposal when admission fails.
    kind_site!("src/core/capture.rs::KindedArguments.0", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork),
    kind_site!("src/core/capture.rs::Metadata.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/core/capture/control.rs::Analysis.owner_rows", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/core/capture/control.rs::RowEquation.Residual.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/core/capture/control.rs::ControlCodeInventory.graph", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/core/capture/control.rs::ControlCodeInventory.owner_rows", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/core/capture/control.rs::TypeUniverseBuilder.ordered", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/core/capture/control.rs::PreparedTypeUniverse.ordered", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/core/capture/control.rs::UnitOccurrence.original", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/core/dialect.rs::IterativeArgumentBuffer.0", FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/dialect.rs::OperationTypeMetadata.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::OperationTypeMetadata.Row.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::TypeAdmissionTask.Owner.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_substitute_interface_application::ArgumentBuffer.0", FieldTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeTransientWork),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_valid_representation_provenance::Payload.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_valid_representation_provenance::Payload.Type.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::$impl_Validator::$fn_valid_type_with_scheme::Task.Owner.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::OwnerKindTask.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::OwnerKindTask.CheckArgument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::OwnerKindTask.Instance.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::OwnerKindTask.Row.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::OwnerKindTask.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::OwnerKindTask.TypeRows.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::OwnerKindTask.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::OwnerValidationOutput.Kind.0", FieldTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeTransientWork),
    kind_site!("src/core/validate.rs::OwnerValidationRoot.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::OwnerValidationRoot.Instance.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::OwnerValidationRoot.Row.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::OwnerValidationRoot.Type.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::OwnerValidationRoot.TypeRows.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/elaborate.rs::$fn_collect_unsolved_inference::Task.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_collect_unsolved_inference::Task.Row.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_collect_unsolved_inference::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_collect_unsolved_inference::Task.Type.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_inference_occurs_in_owner_graph::Task.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_inference_occurs_in_owner_graph::Task.Row.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_inference_occurs_in_owner_graph::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_inference_occurs_in_owner_graph::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_type_contains_unsolved_row_inference::Task.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_type_contains_unsolved_row_inference::Task.Row.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_type_contains_unsolved_row_inference::Task.Type.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_validate_and_charge_public_monotype::Task.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_validate_and_charge_public_monotype::Task.Row.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_zonk_owned_root_with_rows::$fn_argument_sequence::Arguments.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$fn_zonk_owned_root_with_rows::Task.Forall.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$fn_zonk_owned_root_with_rows::Task.Sequence.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$fn_zonk_owned_root_with_rows::Task.Visit.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$fn_zonk_owned_root_with_rows::Value.Argument.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$fn_zonk_owned_root_with_rows::Value.Row.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$fn_zonk_owned_root_with_rows::Value.Type.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$impl_CoreElaborator::$fn_unify_owned_arguments_recorded::Candidates.rows", FieldSharedUnificationWork),
    kind_site!("src/elaborate.rs::$impl_CoreElaborator::$fn_unify_owned_arguments_recorded::FinalRows.rows", FieldSharedUnificationWork),
    kind_site!("src/elaborate.rs::$impl_CoreElaborator::$fn_unify_owned_arguments_recorded::Choice.remaining", FieldSharedUnificationWork),
    kind_site!("src/elaborate.rs::$impl_CoreElaborator::$fn_unify_owned_arguments_recorded::Choice.continuation", FieldSharedUnificationWork),
    kind_site!("src/elaborate.rs::$impl_CoreElaborator::$fn_unify_owned_arguments_recorded::Rows.left", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$impl_CoreElaborator::$fn_unify_owned_arguments_recorded::Rows.right", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$impl_CoreElaborator::$fn_unify_owned_arguments_recorded::Task.Argument.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$impl_CoreElaborator::$fn_unify_owned_arguments_recorded::Task.Argument.1", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$impl_CoreElaborator::$fn_unify_owned_arguments_recorded::Task.CandidateResult.0", FieldSharedUnificationWork),
    kind_site!("src/elaborate.rs::$impl_CoreElaborator::$fn_unify_owned_arguments_recorded::Task.Candidates.0", FieldSharedUnificationWork),
    kind_site!("src/elaborate.rs::$impl_CoreElaborator::$fn_unify_owned_arguments_recorded::Task.FinishRows.0", FieldSharedUnificationWork),
    kind_site!("src/elaborate.rs::$impl_CoreElaborator::$fn_unify_owned_arguments_recorded::Task.Rows.0", FieldSharedUnificationWork),
    kind_site!("src/elaborate.rs::$impl_CoreElaborator::$fn_unify_owned_arguments_recorded::Task.Type.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$impl_CoreElaborator::$fn_unify_owned_arguments_recorded::Task.Type.1", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$impl_TypeProvenance::$fn_aligns_inner::Value.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$impl_TypeProvenance::$fn_aligns_inner::Value.Row.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$impl_TypeProvenance::$fn_aligns_inner::Value.Type.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::BorrowedOwnerArgument.RowArg.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::BorrowedOwnerArgument.TypeArg.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::BorrowedZonkRoot.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::BorrowedZonkRoot.Type.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::InferenceOccurrenceRoot.Row.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::InferenceOccurrenceRoot.Type.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::OwnedArgumentBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::OwnedUnificationEntry.Arguments.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::OwnedUnificationEntry.Arguments.1", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::OwnedUnificationEntry.ArgumentPairs.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::OwnedUnificationEntry.ComparedTypes.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::OwnedUnificationEntry.ComparedTypes.1", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::OwnedZonkRoot.Argument.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::OwnedZonkRoot.Type.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::OwnerReplacementBuffer.rows", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::OwnerReplacementBuffer.types", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/evidence.rs::$fn_goal_key::Task.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTypeTree),
    kind_site!("src/evidence.rs::$fn_goal_key::Task.Instance.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTypeTree),
    kind_site!("src/evidence.rs::$fn_goal_key::Task.Row.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTypeTree),
    kind_site!("src/evidence.rs::$fn_goal_key::Task.Type.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTypeTree),
    kind_site!("src/evidence_validation.rs::OwnerReplacements.rows", FieldTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeTransientWork),
    kind_site!("src/evidence_validation.rs::OwnerReplacements.types", FieldTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeTransientWork),
    kind_site!("src/interface.rs::$fn_same_type_with_constraint_budget_inner::Task.Arguments.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeTypeTree),
    kind_site!("src/interface.rs::$fn_same_type_with_constraint_budget_inner::Task.Arguments.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeTypeTree),
    kind_site!("src/interface.rs::$fn_same_type_with_constraint_budget_inner::Task.Types.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeTypeTree),
    kind_site!("src/interface.rs::$fn_same_type_with_constraint_budget_inner::Task.Types.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeTypeTree),
    kind_site!("src/interface.rs::$impl_InterfaceConstraintBudget::$fn_charge_equal_types::Task.Arguments.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeTypeTree),
    kind_site!("src/interface.rs::$impl_InterfaceConstraintBudget::$fn_charge_equal_types::Task.Arguments.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeTypeTree),
    kind_site!("src/interface.rs::$impl_InterfaceConstraintBudget::$fn_charge_type::Task.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeTypeTree),
    kind_site!("src/interface.rs::ConstraintComparisonRoot.Arguments.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeTypeTree),
    kind_site!("src/interface.rs::ConstraintComparisonRoot.Arguments.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeTypeTree),
    kind_site!("src/interface.rs::ConstraintComparisonRoot.Types.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeTypeTree),
    kind_site!("src/interface.rs::ConstraintComparisonRoot.Types.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_core_with_ledger::Continuation.OwnerArgument.expected", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_core_with_ledger::Continuation.OwnerArgument.remaining", FieldOwnerKindTraversalBorrow),
    kind_site!("src/kind.rs::KindEnvironments.owner_registry", FieldOwnerKindRegistryBorrow),
    kind_site!("src/pattern.rs::$fn_charge_types::Task.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierPatternCoveragePatternCoverageTypeTree),
    kind_site!("src/resolve.rs::$impl_Resolver::$fn_resolve_owner_argument_mode::Task.Application.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::$impl_Resolver::$fn_resolve_owner_argument_mode::Task.EffectArguments.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::$impl_Resolver::$fn_resolve_owner_argument_mode::Task.EffectInstances.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::$impl_Resolver::$fn_resolve_owner_argument_mode::Task.Function.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::$impl_Resolver::$fn_resolve_owner_argument_mode::Task.Row.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::$impl_Resolver::$fn_resolve_owner_argument_mode::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::$impl_Resolver::$fn_resolve_owner_argument_mode::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::$impl_Resolver::$fn_retain_type_nominals_with::Task.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolve.rs::$impl_Resolver::$fn_retain_type_nominals_with::Task.Row.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolve.rs::ResolvedOwnerOccurrenceBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::$fn_same_summary_type_after_substitutions::OwnedSubstitutions.rows", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::$fn_same_summary_type_after_substitutions::OwnedSubstitutions.types", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::$fn_visit_type_identity_references::Task.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::$fn_visit_type_identity_references::Task.Row.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::$fn_visit_type_identity_references::Task.Type.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::$impl_ResolvedRegistry::$fn_display_structural_with_inference::Task.ApplicationSpine.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/resolved.rs::$impl_ResolvedRegistry::$fn_display_structural_with_inference::Task.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::$impl_ResolvedRegistry::$fn_display_structural_with_inference::Task.EffectInstance.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::$impl_ResolvedRegistry::$fn_display_structural_with_inference::Task.EffectRow.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/resolved.rs::$impl_ResolvedRegistry::$fn_display_structural_with_inference::Task.RowTail.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::$impl_ResolvedRegistry::$fn_display_structural_with_inference::Task.Type.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/resolved.rs::$impl_ResolvedRegistry::$fn_with_effects_with_budget::Owned.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolved.rs::NonMaterializedNominalKind.Ordinary.0", FieldRegistryCarrierRetentionPreservedCarrierElaborationInferenceTypeRegistryTree),
    // Interface declarations, facts and original owner records borrow the
    // same immutable parameter allocation. The sized record alone owns its
    // recursive Kind/origin trees and disposes them when its last Arc drops.
    kind_site!("src/resolved.rs::OwnerParameterRecords.parameters", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree),
    kind_site!("src/resolved.rs::SharedOwnerParameters.0", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree, Shared),
    // Sharing an admitted interface fact retains its immutable checked authority;
    // the last Arc owner uses the fact's existing iterative graph disposal.
    kind_site!("src/resolved.rs::SharedCheckedInterfaceFact.0", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree, Shared),
    // Canonical binders retain either an iteratively owned record or a validated
    // immutable original parameter slot; the map remains an independent index.
    kind_site!("src/resolved.rs::CanonicalTypeVariable.0", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree, Mixed),
    kind_site!("src/resolved.rs::CanonicalTypeVariableValue.Owned.0", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree),
    kind_site!("src/resolved.rs::CanonicalTypeVariableValue.SharedOriginal.parameters", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree, Shared),
    kind_site!("src/resolved.rs::OwnerDefinition.parameters", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree, Shared),
    kind_site!("src/resolved.rs::ResolvedOwnerArgument.ty", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedRegistry.owner_definitions", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree, Shared),
    kind_site!("src/resolved.rs::ResourceTypeFact.provider_application", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::SummaryRoot.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::SummaryRoot.Row.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::SummaryRoot.Type.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/surface.rs::SurfaceTypeKind.RowArgument.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/types.rs::$fn_kinded_arguments_have_rigid_rows_with_budget::Task.Type.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_kinded_arguments_have_rigid_rows_with_budget::Task.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_kinded_arguments_have_rigid_rows_with_budget::Task.Row.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_compare_structural_with_charge::Task.Arguments.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_compare_structural_with_charge::Task.Arguments.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_compare_structural_with_charge::Task.Instances.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_compare_structural_with_charge::Task.Instances.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_compare_structural_with_charge::Task.Kinds.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/types.rs::$fn_compare_structural_with_charge::Task.Kinds.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/types.rs::$fn_compare_structural_with_charge::Task.Rows.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_compare_structural_with_charge::Task.Rows.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_compare_structural_with_charge::Task.Types.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_compare_structural_with_charge::Task.Types.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_discard_type_iteratively::Task.Argument.0", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork),
    kind_site!("src/types.rs::$fn_discard_type_iteratively::Task.Arguments.0", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork),
    kind_site!("src/types.rs::$fn_discard_type_iteratively::Task.Row.0", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork),
    kind_site!("src/types.rs::$fn_qualify_scheme_row_replacements_with_budget::Task.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_qualify_scheme_row_replacements_with_budget::Task.Row.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_qualify_scheme_row_replacements_with_budget::Task.Type.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_same_type::Task.ArgumentSequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_same_type::Task.CompareArguments.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_same_type::Task.CompareArguments.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_same_type_with_budget::Task.ArgumentSequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_substitute_structural_type_and_row_variables::RowShape.replacement", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_substitute_structural_type_and_row_variables::Task.EnterForall.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_substitute_structural_type_and_row_variables::Task.ExitForall.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_substitute_structural_type_and_row_variables::Task.FinishForall.0", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork),
    kind_site!("src/types.rs::$fn_substitute_structural_type_and_row_variables::Task.FinishRow.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_substitute_structural_type_and_row_variables::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_substitute_structural_type_and_row_variables::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_substitute_structural_type_and_row_variables::Task.VisitArgument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_substitute_structural_type_and_row_variables::Task.VisitRow.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_write_structural_inner::Task.ApplicationSpine.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_write_structural_inner::Task.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_write_structural_inner::Task.Arguments.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_write_structural_inner::Task.EffectInstance.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_write_structural_inner::Task.EffectInstances.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_write_structural_inner::Task.EffectRow.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_write_structural_inner::Task.EffectRowTail.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_write_structural_inner::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_write_structural_inner::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::IterativeArgumentOwner.$alias", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork),
    kind_site!("src/types.rs::KindedArgument.RowArg.0", FieldCanonicalApplicationStructureStructuralSubtreeTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::KindedArgument.TypeArg.0", FieldCanonicalApplicationStructureStructuralSubtreeTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::SubstitutionRoot.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::SubstitutionRoot.Type.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::Type.ResourceApply.1", FieldCanonicalApplicationStructureStructuralSubtreeTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::TypeHashTask.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::TypeHashTask.Arguments.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::TypeStructureNode.Tail.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::TypeStructureNode.Type.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types/owner_arguments.rs::$fn_clone_kind_precharged::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/types/owner_arguments.rs::$fn_clone_compound_structural_with_failure::Task.Forall.0", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork),
    kind_site!("src/types/owner_arguments.rs::$fn_clone_compound_structural_with_failure::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types/owner_arguments.rs::$fn_map_kinded_argument_types_with_budget::Task.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types/owner_arguments.rs::$fn_map_kinded_argument_types_with_budget::Task.Instance.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types/owner_arguments.rs::$fn_map_kinded_argument_types_with_budget::Task.Row.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types/owner_arguments.rs::IterativeArgumentOwner.0", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork),
    kind_site!("src/types/owner_arguments.rs::StructuralOwned.Argument.0", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork),
    kind_site!("src/types/owner_arguments.rs::StructuralOwned.Instance.0", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork),
    kind_site!("src/types/owner_arguments.rs::StructuralOwned.Row.0", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork),
    kind_site!("src/types/owner_arguments.rs::StructuralOwned.Type.0", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork),
    kind_site!("src/types/owner_arguments.rs::StructuralRoot.Argument.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types/owner_arguments.rs::StructuralRoot.Instance.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types/owner_arguments.rs::StructuralRoot.Row.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types/owner_arguments.rs::StructuralRoot.Type.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types/owner_arguments.rs::StructuralValue.0", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork),
    // Complete tagged arguments and rows retain their physical owners.
    kind_site!("src/elaborate.rs::ModuleBodyChecking.facts", FieldProviderGlobalsMixed),
    kind_site!("src/elaborate.rs::ModuleBodyChecking.globals", FieldProviderGlobalsMixed, Owned),
    kind_site!("src/evidence.rs::PreflightedEvidencePublication.publication", FieldMixedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTreeAndTransientWork),
    kind_site!("src/kind.rs::KindEnvironments.imported_resource_owners", FieldOwnerKindRegistryBorrow),
    kind_site!("src/parser/project.rs::ExpressionTask.FinishProviderResource.arguments", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceProviderResourceExpr.arguments", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/types.rs::TemplateRowReplacements.inference_rows", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    // Source-closed experiment carriers, including imported catalog proofs,
    // staged Core forests, resolved resource metadata, and retained runtime
    // instantiation Arcs. Retention follows the source, not the field's name.
    kind_site!("src/core/capture.rs::BuiltCaptureGraph.graph", FieldConditionalCaptureMixed),
    // Instance preparation retains independently observed request rows and a
    // temporary typed control/value graph. Nothing enters executable authority.
    kind_site!("src/core/dialect.rs::MethodEvidenceDomain.source_parameters", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::MonotypeVariableKinds.CatalogOwner.0", FieldProviderKindBorrow),
    kind_site!("src/resolved.rs::ImportedFacts.resource_facts", FieldResourceFactsShared),
    kind_site!("src/core/validate.rs::BorrowedClauseContract.effect", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::BorrowedClauseContract.clause", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::BorrowedClauseContract.answer", FieldMixedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTreeAndTransientWork),
    kind_site!("src/core/validate.rs::BorrowedClauseContract.output", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/validate.rs::ClauseOutput.Ordinary.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/elaborate.rs::CheckedEffectClause.pattern", FieldProviderElaborationCoreOwned),
    kind_site!("src/eval/machine.rs::Environment.instantiation", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::EnvironmentEntry.instantiation", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.Request.instantiation", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.TypeApplication.caller", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/evidence.rs::PendingOccurrence.application", FieldBorrowedTransientInterfaceArgumentInterfaceParameterEvidenceSelectionEvidenceTypeTypeTree),
    kind_site!("src/evidence.rs::PendingOccurrence.method_arguments", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTypeTree),
    kind_site!("src/evidence.rs::PendingOccurrence.selection", FieldBorrowedEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence_validation.rs::MethodEvidenceInputs.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeResolvedTree),
    kind_site!("src/resolve.rs::ResolvedDeclarations.resources", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModule.resources", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModuleParts.resources", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ImportedFacts.resource_types", FieldResourceFactsShared),
    kind_site!("src/resolved.rs::ExportSummary.resource_types", FieldResourceFactsShared),
    kind_site!("src/resolved.rs::ResolvedResourceDefinition.parameters", FieldResolvedDeclaredKindDeclaredResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedResourceDefinition.input", FieldResolvedValueTypeValueResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedResourceDefinition.state", FieldResolvedValueTypeValueResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedResourceDefinition.result", FieldResolvedValueTypeValueResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedResourceDefinition.answer", FieldResolvedDeclaredKindDeclaredResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedResourceDefinition.provider", FieldResolvedInterfaceArgumentInterfaceParameterResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedResourceDefinition.provided", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedResourceDefinition.interpreted", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedResourceDefinition.acquire", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedResourceDefinition.finish", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedResourceDefinition.handlers", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResourceTypeFact.parameters", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResourceTypeFact.input", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResourceTypeFact.state", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResourceTypeFact.result", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResourceTypeFact.answer", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResourceTypeFact.provider", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResourceTypeFact.provided", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResourceTypeFact.interpreted", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/surface.rs::SurfaceModule.resources", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    // Product resource grammar retains unresolved facts for checked source admission.
    kind_site!("src/surface.rs::SurfaceExprKind.ProviderResource.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceResourceDefinition.parameters", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceResourceDefinition.input", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceResourceDefinition.state", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceResourceDefinition.result", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceResourceDefinition.answer", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceResourceDefinition.provider", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceResourceDefinition.provided", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceResourceDefinition.interpreted", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceResourceDefinition.acquire", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceResourceDefinition.finish", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceResourceDefinition.handlers", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceProviderResourceExpr.initializer", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceProviderResourceExpr.body", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),

    // Collector-local graph borrows use the caller's type ledger in both
    // summary construction and import retention; they own no summary tree.
    kind_site!("src/core/capture.rs::CaptureGraphVisits.seen", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeSummaryTree),
    kind_site!("src/core/capture.rs::CaptureValueSummary.graph", FieldSummaryCarrierRetentionPreservedCarrierElaborationInferenceTypeSummaryTree, Shared),
    kind_site!("src/core/capture.rs::CallableSlots.positions", FieldSummaryCarrierRetentionPreservedCarrierElaborationInferenceTypeSummaryTree),
    kind_site!("src/core/capture.rs::SummaryGraph.callables", FieldSummaryCarrierRetentionPreservedCarrierElaborationInferenceTypeSummaryTree),
    kind_site!("src/core/capture.rs::SummaryGraph.code", FieldSummaryCarrierRetentionPreservedCarrierElaborationInferenceTypeSummaryTree, Shared),
    kind_site!("src/core/capture.rs::SummaryGraph.types", FieldSummaryCarrierRetentionPreservedCarrierElaborationInferenceTypeSummaryTree),
    kind_site!("src/core/capture.rs::CallableSlots.absent_unit", FieldSummaryCarrierRetentionPreservedCarrierElaborationInferenceTypeSummaryTree),
    kind_site!("src/core/capture.rs::Callable.ty", FieldSummaryCarrierRetentionPreservedCarrierElaborationInferenceTypeSummaryTree),
    kind_site!("src/core/capture.rs::ImportedCallables.callables", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/core/capture.rs::ImportedCallables.graphs", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/core/capture.rs::Request.effect", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork, Shared),
    kind_site!("src/core/capture.rs::Request.opaque_row", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork, Shared),
    kind_site!("src/core/capture.rs::CleanupRequirement.expected", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/core/capture.rs::CleanupRequirement.retained", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/core/capture.rs::CleanupRequirement.row", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    // Requested-root metadata preparation borrows one exact typed Core forest.
    kind_site!("src/core/capture.rs::FunctionMetadataPreparation.nodes", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreValidationCoreTypeCoreTree),
    kind_site!("src/core/capture.rs::Metadata.Type.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/core/capture.rs::Metadata.Row.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/core/capture.rs::MethodAdapter.head_arguments", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/core/capture/control.rs::Control.Request.0", FieldSummaryCarrierRetentionPreservedCarrierElaborationInferenceTypeSummaryTree, Shared),
    kind_site!("src/core/capture/control.rs::Control.Handler.effect", FieldSummaryCarrierRetentionPreservedCarrierElaborationInferenceTypeSummaryTree, Shared),
    kind_site!("src/core/capture/control.rs::Control.Resource.effect", FieldSummaryCarrierRetentionPreservedCarrierElaborationInferenceTypeSummaryTree, Shared),
    kind_site!("src/core/capture/control.rs::Analysis.graph", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/core/capture/control.rs::Analysis.types", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/core/capture/control.rs::Analysis.labels", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork, Shared),
    kind_site!("src/core/capture/control.rs::Analysis.cleanup_rows", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/core/capture.rs::TypeArguments.0", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork),
    kind_site!("src/resolved.rs::CheckedGlobalScheme.capture", FieldSummaryCarrierRetentionPreservedCarrierElaborationInferenceTypeSummaryTree, Shared),
    kind_site!("src/resolved.rs::ExportedGlobal.capture", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree, Shared),
    kind_site!("src/resolved.rs::ImportedGlobalScheme.capture", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree, Shared),
    kind_site!("src/elaborate.rs::ElaborationTask.Equation.0", FieldMixedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTreeAndTransientWork),
    kind_site!("src/elaborate.rs::EquationTask.ContinueEquations.0", FieldMixedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTreeAndTransientWork),
    kind_site!("src/elaborate.rs::EquationTask.ContinueLexicalEvidence.0", FieldMixedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTreeAndTransientWork),
    kind_site!("src/elaborate.rs::EquationTask.FinishEquationClause.patterns", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::EquationTask.FinishEquationClause.progress", FieldMixedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTreeAndTransientWork),
    kind_site!("src/elaborate.rs::EquationTask.FinishLexicalMethod.progress", FieldMixedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTreeAndTransientWork),
    kind_site!("src/elaborate.rs::EquationTask.FinishLexicalMethod.resumes", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::EquationsProgress.coverage_matrix", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::EquationsProgress.domain_types", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::EquationsProgress.domains", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::EquationsProgress.equations", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::EquationsProgress.expected_body_effects", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::EquationsProgress.function_type", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::EquationsProgress.parameters", FieldTransientCarrierRetentionPreservedCarrierElaborationCoreTypeTransientWork),
    kind_site!("src/elaborate.rs::EquationsProgress.remainder", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LexicalEvidenceProgress.active", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LexicalEvidenceProgress.application", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LexicalEvidenceProgress.checked_methods", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LexicalEvidenceProgress.members", FieldTransientCarrierRetentionPreservedCarrierElaborationCoreTypeTransientWork),
    kind_site!("src/elaborate.rs::LexicalEvidenceProgress.methods", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LexicalEvidenceProgress.source", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::LexicalEvidenceProgress.supplied", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/parser/project.rs::PendingLexicalEvidence.application", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/resolve.rs::PendingLexicalResolution.application", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::PendingLexicalResolution.equations", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::PendingLexicalResolution.groups", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::PendingLexicalResolution.source", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::ResolveTask.ContinueLexicalEvidence.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ResolveTask.FinishLexicalEquation.state", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ResolveTask.VisitLexicalEvidence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceCatalog.lexical_owners", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceLexicalOwner.application", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/elaborate.rs::ElaboratedDeclaration.Evidence.members", FieldTransientCarrierRetentionPreservedCarrierElaborationCoreTypeTransientWork),
    kind_site!("src/elaborate.rs::EquationTask.LexicalEvidence.0", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::EvidenceLowering.lexical_binders", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/evidence.rs::EvidenceSelector.lexical_sources", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::LexicalSource.application", FieldEvidenceInterfaceArgumentInterfaceParameterEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence_validation.rs::EvidenceScope.lexical_sources", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeResolvedTree),
    kind_site!("src/evidence_validation.rs::EvidenceScope.local_scopes", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeResolvedTree),
    kind_site!("src/evidence_validation.rs::LinkedLocalScope.Annotation.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeResolvedTree),
    kind_site!("src/evidence_validation.rs::LinkedLocalScope.Equation.source", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeResolvedTree),
    kind_site!("src/evidence_validation.rs::LinkedLocalScope.Equation.method", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeResolvedTree),
    kind_site!("src/evidence_validation.rs::LinkedLocalScope.Method.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeResolvedTree),
    kind_site!("src/interface.rs::CheckedLexicalEvidence.application", FieldEvidenceInterfaceArgumentInterfaceParameterEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::CheckedLexicalEvidence.methods", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::CheckedLexicalMethod.scheme", FieldEvidenceSchemeSchemeValueEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::LexicalEvidenceSlot.0", FieldSharedEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/parser/project.rs::PendingLocalDeclaration.Evidence.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/resolved.rs::ResolvedLexicalEvidence.application", FieldResolvedInterfaceArgumentInterfaceParameterResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedLexicalEvidence.checked", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Shared),
    kind_site!("src/resolved.rs::ResolvedLexicalEvidence.method_groups", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedLocalDeclaration.Evidence.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/surface.rs::SurfaceLocalDeclaration.Evidence.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceLexicalEvidence.application", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceLexicalEvidence.equations", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/driver.rs::PipelineFailure.Kind.0", FieldTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_core_with_ledger::Continuation.ApplicationArgument.function", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_core_with_ledger::Continuation.ApplicationFunction.argument", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_core_with_ledger::Continuation.ApplicationFunction.argument_mirror", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_core_with_ledger::Continuation.FunctionDomain.codomain", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_core_with_ledger::Continuation.FunctionDomain.codomain_mirror", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_core_with_ledger::Continuation.Tuple.remaining", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_core_with_ledger::Continuation.Tuple.remaining_mirrors", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_core_with_ledger::State.Complete.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_core_with_ledger::State.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_core_with_ledger::State.Visit.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::BodyWork.Declaration.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeResolvedTree),
    kind_site!("src/kind.rs::BodyWork.Expression.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeResolvedTree),
    kind_site!("src/kind.rs::BodyWork.LexicalNewtype.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeResolvedTree),
    kind_site!("src/kind.rs::BodyWork.RecursiveMember.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeResolvedTree),
    kind_site!("src/kind.rs::InterfaceKindFact.parameters", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site!("src/kind.rs::ResourceKindFact.parameters", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site!("src/kind.rs::KindEnvironments.row_resource_owners", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site!("src/kind.rs::KindEnvironments.delta", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::KindEnvironments.effects", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site!("src/kind.rs::KindEnvironments.iota", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site!("src/kind.rs::KindEnvironments.omega", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeKindTree),
    kind_site!("src/kind.rs::KindEnvironments.xi", FieldTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::KindError.expectation", FieldTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site!("src/kind.rs::KindError.found", FieldTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site!("src/kind.rs::KindExpectation.Exact.0", FieldTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site!("src/kind.rs::KindExpectation.Function.domain", FieldTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site!("src/kind.rs::KindFact.kind", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::KindFact.retained_mirrors", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::DeclaredKindFact.fact", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::KindFailure.Source.0", FieldTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site!("src/kind.rs::NominalKindFact.kind", FieldTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::CompleteInterfaceApplication.arguments", FieldBorrowedTransientInterfaceArgumentInterfaceParameterResolvedKindResolutionTypeResolvedTree),
    kind_site!("src/kind.rs::CompleteInterfaceApplication.parameters", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site!("src/kind.rs::RetainedKindMirrors.Two.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::RetainedKindMirrors.Two.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/resolve.rs::ResolveModuleError.Kind.0", FieldTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeKindTree),
    kind_site!("src/resolve.rs::ResolveModuleError.Representation.0", FieldTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeResolvedTree),
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
    kind_site!("src/core/dialect.rs::IterativeTypeMap.0", FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/dialect.rs::MethodEvidenceAdapterEdge.application", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceAdapterEdge.method_parameters", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceAdapterEdge.value_type", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceAnchor.application", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceCatalog.adapters", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceCatalog.concrete_sources", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceCatalog.domains", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceCatalog.implementation_owners", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceCatalog.methods", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceCatalog.occurrences", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree, Mixed),
    kind_site!("src/core/dialect.rs::MethodEvidenceConcreteSource.head_arguments", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceDomain.application", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceImplementationOwner.application", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceImplementationOwner.source_parameters", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceMethod.parameters", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceMethod.value_type", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceOccurrence.checked_application", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceOccurrence.checked_value_type", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceOccurrence.method_arguments", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::MethodEvidenceOccurrence.selection", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree, Shared),
    kind_site!("src/core/dialect.rs::OperationTypeMetadata.Pattern.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::OperationTypeMetadata.Type.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
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
    kind_site!("src/core/dialect.rs::CoreProgram.nodes", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::CoreProgram.method_evidence", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree, Shared),
    kind_site!("src/core/dialect.rs::CoreProgram.method_evidence_anchors", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::CoreProgram.registry", FieldRegistryCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeRegistryTree, Shared),
    kind_site!("src/core/dialect.rs::CoreTypedExpr.effects", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::CoreTypedExpr.kind", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::CoreTypedExpr.ty", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::PureProgram.$alias", FieldMixedCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTreeAndRegistryTree),
    kind_site!("src/core/dialect.rs::PureValue.Function.0", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::StoredNode.effects", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::StoredNode.kind", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::StoredNode.ty", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::TypeAdmissionTask.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::TypeAdmissionTask.VisitSequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::TypedExpr.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::UnvalidatedParts.$alias", FieldMixedCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTreeAndRegistryTree),
    kind_site!("src/core/dialect.rs::UnvalidatedCoreProgram.nodes", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::UnvalidatedCoreProgram.method_evidence", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree, Shared),
    kind_site!("src/core/dialect.rs::UnvalidatedCoreProgram.method_evidence_anchors", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/dialect.rs::UnvalidatedCoreProgram.registry", FieldRegistryCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeRegistryTree, Shared),
    kind_site!("src/core/dialect.rs::UnvalidatedProgram.$alias", FieldMixedCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTreeAndRegistryTree),
    kind_site!("src/core/dialect.rs::ValidatedCoreProgram.0", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree, Shared),
    kind_site!("src/core/dialect.rs::ValidatedProgram.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree, Shared),
    kind_site!("src/core/effect.rs::EffectClause.arm", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/effect.rs::EffectCoreBuilder.$alias", FieldMixedCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTreeAndRegistryTree),
    kind_site!("src/core/effect.rs::EffectExpr.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/effect.rs::EffectExprKind.Operation.0", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree, Mixed),
    kind_site!("src/core/effect.rs::EffectExprKind.Pure.0", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/effect.rs::EffectOperation.Handler.0", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/effect.rs::EffectOperation.Request.0", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/effect.rs::EffectOperation.Resource.0", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/effect.rs::ResourceScopeNode.handle", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/elaborate.rs::ElaborationTask.FinishPerform.0", FieldMixedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTreeAndTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.FinishResource.0", FieldMixedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTreeAndTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.ResourceBody.resource", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::PerformProgress.request", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::PerformProgress.result", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ResourceProgress.handle", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ResourceProgress.initializer", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ResourceProgress.resource", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/evidence_validation.rs::LinkedLocalScope.Resource.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeResolvedTree),
    kind_site!("src/kind.rs::BodyWork.ResourceBody.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeResolvedTree),
    kind_site!("src/kind.rs::BodyWork.ResourceExit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeResolvedTree),
    kind_site!("src/resolve.rs::ResolveTask.FinishResource.identity", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ResolveTask.FinishResource.initializer", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ResolveTask.ResourceInitializer.source", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolved.rs::ResolvedExprKind.Resource.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedExprKind.Cleanup.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedCleanupExpr.body", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedCleanupExpr.action", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedResourceExpr.body", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedResourceExpr.identity", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedResourceExpr.initializer", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/core/effect.rs::$impl_CoreBuilder::$fn_replay_effect_rows_in_range::Equation.Handler.0", FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/effect.rs::$impl_CoreBuilder::$fn_replay_effect_rows_in_range::Equation.Request.1", FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/effect.rs::HandlerNode.clauses", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/effect.rs::HandlerNode.effect", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/effect.rs::HandlerNode.hook_root", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/effect.rs::HandlerNode.hook_registration", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/effect.rs::RequestNode.effect", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/effect.rs::UnvalidatedEffectProgram.$alias", FieldMixedCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTreeAndRegistryTree),
    kind_site!("src/core/effect.rs::ValidatedEffectProgram.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree, Shared),
    kind_site!("src/core/function.rs::FunctionNode.parameter", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::CoreBuilder.$alias", FieldMixedCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTreeAndRegistryTree),
    kind_site!("src/core/mod.rs::CoreMatchArm.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::CorePattern.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::CorePatternKind.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::EffectClause.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::EffectCoreBuilder.$alias", FieldMixedCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTreeAndRegistryTree),
    kind_site!("src/core/mod.rs::EffectExpr.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::EffectExprKind.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree, Mixed),
    kind_site!("src/core/mod.rs::EffectOperation.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree, Mixed),
    kind_site!("src/core/mod.rs::HandlerNode.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::MatchNode.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::PureComputation.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::PureExprKind.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::PureProgram.$alias", FieldMixedCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTreeAndRegistryTree),
    kind_site!("src/core/mod.rs::PureValue.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::RecursiveBindingMember.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::RecursiveBindingNode.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::RequestNode.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::TypeAbstractionNode.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::TypeApplicationNode.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::TypedBinder.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::TypedExpr.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/mod.rs::UnvalidatedProgram.$alias", FieldMixedCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTreeAndRegistryTree),
    kind_site!("src/core/mod.rs::UnvalidatedEffectProgram.$alias", FieldMixedCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTreeAndRegistryTree),
    kind_site!("src/core/mod.rs::ValidatedEffectProgram.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree, Shared),
    kind_site!("src/core/mod.rs::ValidatedProgram.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree, Shared),
    kind_site!("src/core/recursion.rs::RecursiveBindingMember.binder", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/recursion.rs::RecursiveBindingNode.members", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/type_ops.rs::TypeAbstractionNode.parameters", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/type_ops.rs::TypeApplicationNode.arguments", FieldCoreCoreInstantiationInstantiationArgumentCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/type_ops.rs::TypeApplicationNode.row_arguments", FieldCoreCoreInstantiationInstantiationArgumentCoreAdmissionCoreTypeCoreTree),
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
    kind_site!("src/driver.rs::ModularCoreResult.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree, Shared),
    kind_site!("src/driver.rs::FileFailure.Pipeline.0", FieldTransientCarrierRetentionPreservedCarrierPipelineObservationPipelineTypeObservation),
    kind_site!("src/driver.rs::Observation._heap", FieldTransientCarrierRetentionPreservedCarrierPipelineObservationPipelineTypeObservation, Shared),
    kind_site!("src/driver.rs::Observation.ty", FieldTransientValueTypeValuePipelineObservationPipelineTypeObservation),
    kind_site!("src/driver.rs::Observation.value", FieldTransientCarrierRetentionPreservedCarrierPipelineObservationPipelineTypeObservation, Shared),
    kind_site!("src/driver.rs::ObservationParts.ty", FieldTransientValueTypeValuePipelineObservationPipelineTypeObservation),
    kind_site!("src/driver.rs::ObservationParts.value", FieldTransientCarrierRetentionPreservedCarrierPipelineObservationPipelineTypeObservation, Shared),
    kind_site!("src/driver.rs::ObservationValue._heap", FieldTransientCarrierRetentionPreservedCarrierPipelineObservationPipelineTypeObservation, Shared),
    kind_site!("src/driver.rs::ObservationValue.value", FieldTransientCarrierRetentionPreservedCarrierPipelineObservationPipelineTypeObservation, Shared),
    kind_site!("src/driver.rs::PipelineFailure.Typing.0", FieldTransientCarrierRetentionPreservedCarrierPipelineObservationPipelineTypeObservation),
    kind_site!("src/driver.rs::PipelineDiagnostic.failure", FieldTransientCarrierRetentionPreservedCarrierPipelineObservationPipelineTypeObservation),
    kind_site!("src/elaborate.rs::$fn_compare_concrete_types::Task.Pair.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_compare_concrete_types::Task.Pair.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_compare_concrete_types::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_compare_concrete_types::Task.Sequence.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_pure_core_type_from_precharged::Task.Forall.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::$fn_pure_core_type_from_precharged::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_pure_core_type_from_precharged::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_resume_usage_with_budget::Task.BeginMatch.0", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::$fn_resume_usage_with_budget::Task.CheckFunction.0", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::$fn_resume_usage_with_budget::Task.CheckHandlerClauses.0", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::$fn_resume_usage_with_budget::Task.CheckRecursive.0", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::$fn_resume_usage_with_budget::Task.FinishMatchArm.arms", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::$fn_resume_usage_with_budget::Task.Visit.0", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::$fn_validate_and_charge_public_monotype::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::$fn_validate_and_charge_public_monotype::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTypeTree),
    kind_site!("src/elaborate.rs::ActiveEvidenceBinder.ty", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ActiveEvidenceBinder.application", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ActiveResume.input", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ActiveResume.result", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CheckedBodyBuffers.definitions", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork, Mixed),
    kind_site!("src/elaborate.rs::CheckedBodyBuffers.implementations", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork, Mixed),
    kind_site!("src/elaborate.rs::CheckedImplementationFactBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork, Mixed),
    kind_site!("src/elaborate.rs::CheckedInterfaceMethodRef.Imported.0", FieldSummaryCarrierRetentionPreservedCarrierElaborationInferenceTypeSummaryTree, Borrowed),
    kind_site!("src/elaborate.rs::CheckedInterfaceMethodRef.Local.0", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::CheckedInterfaceRef.Imported.0", FieldSummaryCarrierRetentionPreservedCarrierElaborationInferenceTypeSummaryTree, Borrowed),
    kind_site!("src/elaborate.rs::CheckedInterfaceRef.Local.0", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::CheckedPattern.pattern", FieldTransientCarrierRetentionPreservedCarrierElaborationCoreTypeTransientWork),
    kind_site!("src/elaborate.rs::CheckedSchemeBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork, Mixed),
    kind_site!("src/elaborate.rs::CoreElaborator.row_inference_solutions", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CoreElaborator.row_inference_obligations", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CoreElaborator.cleanup_rows", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate/cleanup_rows.rs::CleanupRows.equalities", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate/cleanup_rows.rs::CleanupRows.equations", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate/cleanup_rows.rs::CleanupRows.recomputations", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate/cleanup_rows.rs::Equation.Remove.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate/cleanup_rows.rs::Equation.Remove.1", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate/cleanup_rows.rs::Equation.Union.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate/cleanup_rows.rs::Equation.Union.1", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::RowInferenceSolutionMap.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CoreRecursiveMemberBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CorePatternBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CorePatternMatrixBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CorePatternOwner.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CorePatternRowSequence.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CurrentImplementationMethod.method_arguments", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaboratedBinding.binder", FieldTransientCarrierRetentionPreservedCarrierElaborationCoreTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaboratedBindingBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaboratedDeclaration.Binding.binder", FieldTransientCarrierRetentionPreservedCarrierElaborationCoreTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaboratedDeclaration.Binding.effects", FieldTransientCarrierRetentionPreservedCarrierElaborationCoreTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaboratedDeclaration.PatternBinding.effects", FieldTransientCarrierRetentionPreservedCarrierElaborationCoreTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaboratedDeclaration.PatternBinding.pattern", FieldTransientCarrierRetentionPreservedCarrierElaborationCoreTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaboratedDeclaration.Recursive.effects", FieldTransientCarrierRetentionPreservedCarrierElaborationCoreTypeTransientWork),
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
    kind_site!("src/elaborate.rs::ElaborationTask.BeginRegistrationBinding.binding", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::ElaborationTask.BeginCleanupBinding.binding", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::CleanupActionProgress.expected", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CleanupActionProgress.inferred", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.FinishCleanupAction.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.FinishCleanup.cleanup", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::ElaborationTask.BeginRegistrationBinding.handler", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
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
    kind_site!("src/elaborate.rs::ElaborationTask.FinishApplication.latent_effects", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.FinishBinding.binding", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::ElaborationTask.FinishHookBody.handler", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
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
    kind_site!("src/elaborate.rs::CoreElaborator.base_context", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CoreElaborator.current_implementation_method", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CoreElaborator.builder", FieldMixedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeCoreTreeAndRegistryTree),
    kind_site!("src/elaborate.rs::CoreElaborator.active_resumes", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CoreElaborator.expected_effect_rows", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CoreElaborator.expected_scheme_rows", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::EquationsProgress.ambient_rows", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::FunctionCheck.ambient_rows", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.CheckFunction.ambient_rows", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CoreElaborator.evidence_lowering", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CoreElaborator.generated_type_variables", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CoreElaborator.inference_solutions", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CoreElaborator.inference_variables", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::CoreElaborator.registry", FieldRegistryCarrierRetentionPreservedCarrierElaborationInferenceTypeRegistryTree, Shared),
    kind_site!("src/elaborate.rs::CoreElaborator.selection", FieldMixedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeEvidenceTreeAndTransientWork),
    kind_site!("src/elaborate.rs::PatternDecisionBinderBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::PatternDecisionBinderSequence.remaining", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::PatternDecisionColumn.ty", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::PatternDecisionColumnArena.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::PatternDecisionContinuation.application_types", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::PatternDecisionContinuationArena.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::PatternDecisionFlattenScratch.work", FieldTransientCarrierRetentionPreservedCarrierElaborationCoreTypeTransientWork),
    kind_site!("src/elaborate.rs::PatternDecisionFlattenTask.FinishConstructor.ty", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::PatternDecisionFlattenTask.FinishTuple.ty", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::PatternDecisionFlattenTask.Visit.0", FieldTransientCarrierRetentionPreservedCarrierElaborationCoreTypeTransientWork),
    kind_site!("src/elaborate.rs::PatternDecisionFlattenWork.0", FieldTransientCarrierRetentionPreservedCarrierElaborationCoreTypeTransientWork),
    kind_site!("src/elaborate.rs::PatternDecisionPattern.ty", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::PatternDecisionPatternArena.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::PatternDecisionPatternSequence.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::PatternDecisionTask.FinishBinding.binder", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::PatternDecisionTask.FinishBinding.result_type", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::PatternDecisionTask.FinishMatch.patterns", FieldTransientCarrierRetentionPreservedCarrierElaborationCoreTypeTransientWork),
    kind_site!("src/elaborate.rs::PatternDecisionTask.FinishMatch.result_type", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::PatternDecisionWork.0", FieldTransientCarrierRetentionPreservedCarrierElaborationCoreTypeTransientWork),
    kind_site!("src/elaborate.rs::EffectElaborator.$alias", FieldMixedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeCoreTreeAndRegistryTree),
    kind_site!("src/elaborate.rs::Elaborator.$alias", FieldMixedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeCoreTreeAndRegistryTree),
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
    kind_site!("src/elaborate.rs::LoweredEvidenceMethod.adapter_application", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredImplementationMethod.application", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredImplementationMethod.scheme", FieldTransientSchemeSchemeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredInterfaceMethod.value_type", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredInterfaceMethod.type_parameters", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredRequirement.methods", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredRequirementMethod.ty", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredRequirementMethod.application", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredScheme.core_scheme", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredScheme.requirements", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredScheme.source_type_parameters", FieldTransientDeclaredKindDeclaredElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredScheme.type_parameters", FieldTransientDeclaredKindDeclaredElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::LoweredScheme.value_type", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::MatchProgress.expression", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::MatchProgress.arm_bodies", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::MatchProgress.matrix", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::MatchProgress.result_type", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::MatchProgress.scrutinee", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::MatchProgressOwner.0", FieldMixedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTreeAndTransientWork),
    kind_site!("src/elaborate.rs::ProvenancedTypeBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ProvenancedTypeOwner.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::OwnedTypeBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::PreparedFinalBinder.checked", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree, Borrowed),
    kind_site!("src/elaborate.rs::PreparedFinalBinder.lowered", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork, Borrowed),
    kind_site!("src/elaborate.rs::PreparedGlobals.binders", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::PreparedGlobals.context", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::PreparedGlobals.globals", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::PreparedGlobals.quantifiers", FieldTransientDeclaredKindDeclaredElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ProvenancedType.ty", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ScopedEvidenceBinder.binder", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ScopedEvidenceBinder.application", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::TypeContext.binders", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::TypeError.Mismatch.0", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree),
    kind_site!("src/elaborate.rs::TypeFact.quantified", FieldTransientDeclaredKindDeclaredElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::TypeFact.ty", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::TypeFactOwner.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::TypeMismatch.expected", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::TypeMismatch.found", FieldTransientValueTypeValueElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::TypeReplacementBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::TypedNode.ty", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::TypedNode.effects", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::TypedNodeOwner.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::TypedNodeBuffer.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/eval/instantiation.rs::Bindings.rows", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState),
    kind_site!("src/eval/instantiation.rs::Bindings.types", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState),
    kind_site!("src/eval/instantiation.rs::Instantiation.0", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Control.Evaluate.1", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Control.Return.0", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Environment.head", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::EnvironmentEntry.kind", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::EnvironmentEntry.parent", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::EnvironmentEntryKind.Binding.value", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::CapturedContinuation.frames", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Mixed),
    kind_site!("src/eval/machine.rs::Evaluation.heap", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Evaluation.value", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.ApplyArgument.function", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.ApplyFunction.caller_environment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.Bind.environment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.CleanupBoundary.environment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.CleanupCompletion.saved", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.ClauseBoundary.continuation", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Mixed),
    kind_site!("src/eval/machine.rs::Frame.HandlerBoundary.environment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.InitializeRecursive.environment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.ResourceInitializer.environment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.Match.arms", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState),
    kind_site!("src/eval/machine.rs::Frame.Match.environment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.PrimitiveLeft.environment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.PrimitiveRight.left", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.RegistrationBoundary.callback", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
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
    kind_site!("src/eval/mod.rs::ExecutableNode.$alias", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Borrowed),
    kind_site!("src/eval/mod.rs::ExecutableProgram.$alias", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/mod.rs::ObservedHeap.$alias", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/mod.rs::ObservedValue.$alias", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/mod.rs::Value.$alias", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/value.rs::$impl_ObservedValue::$fn_render::Task.Value.0", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationTransientWork, Shared),
    kind_site!("src/eval/value.rs::Closure.environment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/value.rs::Closure.program", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/value.rs::ExecutableNode.Effect.0", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Borrowed),
    kind_site!("src/eval/value.rs::ExecutableNode.Pure.0", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Borrowed),
    kind_site!("src/eval/value.rs::ExecutableProgram.Effect.0", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/value.rs::ExecutableProgram.Pure.0", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/value.rs::HeapCell.Constructor.1", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/value.rs::HeapCell.Tuple.0", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/value.rs::ObservedHeap.cells", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/value.rs::ObservedHeap.registry", FieldRegistryCarrierRetentionPreservedCarrierEvaluationEvaluationRegistryTree, Shared),
    kind_site!("src/eval/value.rs::ObservedValue.heap", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/value.rs::Value.Data.0", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/value.rs::Value.Function.0", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/value.rs::Value.Polymorphic.environment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/evidence.rs::EvidenceSelector.abstracts", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::EvidenceSelector.implementations", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::EvidenceSelector.interfaces", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::EvidenceSelector.method_rigidities", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::EvidenceSelector.pending", FieldMixedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTreeAndTransientWork),
    kind_site!("src/evidence.rs::EvidenceSelector.selected", FieldMixedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTreeAndTransientWork),
    kind_site!("src/evidence.rs::EvidenceSelector.schemes", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::DeterminationSnapshot.tasks", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::EvidenceTypeBuffer.0", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::Goal.application", FieldTransientInterfaceArgumentInterfaceParameterEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::ImplementationCandidateAuthentication.arguments", FieldBorrowedTransientInterfaceArgumentInterfaceParameterEvidenceSelectionEvidenceTypeTypeTree),
    kind_site!("src/evidence.rs::ImplementationCandidateAuthentication.parameter_records", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeResolvedTreeAndCheckedTree),
    kind_site!("src/evidence.rs::ImplementationEntry.application", FieldEvidenceInterfaceArgumentInterfaceParameterEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::ImplementationEntry.prerequisites", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::ImprovementTask.actual_dependents", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::ImprovementTask.expected_dependents", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::ImprovementTask.key", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::ImprovementTaskParts.$alias", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::InterfaceEntry.parameters", FieldEvidenceDeclaredKindDeclaredEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::InterfaceEntry.methods", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::MethodEntry.value_type", FieldEvidenceValueTypeValueEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::MethodEntry.type_parameters", FieldEvidenceDeclaredKindDeclaredEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::MethodObligationMetadata.method_arguments", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::MethodObligationMetadata.checked_value_type", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::MethodObligationMetadata.method_rigidity", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::MethodRigidityCheck.method_arguments", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTypeTree),
    kind_site!("src/evidence.rs::MethodRigidityCheck.rigid_arguments", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTypeTree),
    kind_site!("src/evidence.rs::MethodRigidityCondition.rigid_arguments", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::MethodRigidityDeterminationSnapshot.task", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::PendingEvidencePublication.occurrences", FieldMixedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTreeAndTransientWork),
    kind_site!("src/evidence.rs::PendingObligation.application", FieldTransientInterfaceArgumentInterfaceParameterEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::PendingObligation.method_arguments", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::PendingObligation.checked_value_type", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::PendingObligation.method_rigidity", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::PendingObligation.slot", FieldSharedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::ReplacementMap.values", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::RequirementEntry.application", FieldEvidenceInterfaceArgumentInterfaceParameterEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::SchemeEntry.scheme", FieldEvidenceSchemeSchemeValueEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::SelectedMethodRigidity.condition", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::SelectedOccurrence.checked_application", FieldTransientInterfaceArgumentInterfaceParameterEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::SelectedOccurrence.checked_value_type", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::SelectedOccurrence.method_arguments", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::SelectedOccurrence.selection", FieldSharedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::SelectedOccurrence.slot", FieldSharedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::SelectionMethod.interface_parameters", FieldBorrowedEvidenceDeclaredKindDeclaredEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::SelectionMethod.type_parameters", FieldBorrowedEvidenceDeclaredKindDeclaredEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::SelectionMethod.value_type", FieldBorrowedEvidenceValueTypeValueEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::SelectionSite.slot", FieldSharedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/evidence.rs::SelectionTask.Finish.substitution", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::SelectionTask.Select.goal", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence.rs::SelectionWork.0", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/evidence_validation.rs::PendingGoal.application", FieldTransientInterfaceArgumentInterfaceParameterEvidenceValidationEvidenceTypeTransientWork),
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
    kind_site!("src/interface.rs::CheckedImplementation.application", FieldCheckedInterfaceArgumentInterfaceParameterInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/interface.rs::CanonicalImplementationGoal.environments", FieldMixedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/interface.rs::CanonicalImplementationGoal.roots", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTypeTree),
    kind_site!("src/interface.rs::CheckedRequirement.application", FieldCheckedInterfaceArgumentInterfaceParameterInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/interface.rs::ConstrainedScheme.requirements", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/interface.rs::ConstrainedScheme.type_parameters", FieldCheckedDeclaredKindDeclaredInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/interface.rs::ConstrainedScheme.value_type", FieldCheckedValueTypeValueInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/interface.rs::EvidenceNode.Implementation.substitution", FieldBorrowedEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::EvidenceNodeData.Implementation.substitution", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::EvidencePlan.application", FieldEvidenceInterfaceArgumentInterfaceParameterEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::EvidencePlan.nodes", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::EvidenceSelection.plan", FieldSharedEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::EvidenceSelectionBuilder.nodes", FieldTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeTransientWork),
    kind_site!("src/interface.rs::EvidenceSlot.filled", FieldSharedEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::EvidenceSlotHandle.filled", FieldSharedTransientCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::EvidenceSubstitution.argument", FieldEvidenceDeclaredKindDeclaredEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::FilledEvidenceSlot.checked_application", FieldEvidenceInterfaceArgumentInterfaceParameterEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::FilledEvidenceSlot.checked_value_type", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::FilledEvidenceSlot.method_arguments", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree),
    kind_site!("src/interface.rs::FilledEvidenceSlot.selection", FieldEvidenceCarrierRetentionPreservedCarrierEvidenceSelectionEvidenceTypeEvidenceTree, Shared),
    kind_site!("src/interface.rs::OverlapHead.ty", FieldBorrowedTransientCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeTypeTree),
    kind_site!("src/interface.rs::InterfaceApplication.arguments", FieldCheckedInterfaceArgumentInterfaceParameterInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/interface.rs::InterfaceArgumentBuffer.0", FieldTransientCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeTransientWork),
    kind_site!("src/module.rs::LoadedModule.surface", FieldSurfaceCarrierRetentionPreservedCarrierModuleStagingProjectionSurfaceTree),
    kind_site!("src/module.rs::ModuleGraph.modules", FieldSurfaceCarrierRetentionPreservedCarrierModuleStagingProjectionSurfaceTree),
    kind_site!("src/module.rs::StagedModule.surface", FieldSurfaceCarrierRetentionPreservedCarrierModuleStagingProjectionSurfaceTree),
    kind_site!("src/parser/project.rs::ExpressionTask.FinishBlock.declarations", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/parser/project.rs::ExpressionTask.FinishHandle.effect", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/parser/project.rs::ExpressionTask.FinishHook.effect", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/parser/project.rs::ExpressionTask.FinishRegistration.effect", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/parser/project.rs::ExpressionTask.FinishPerform.arguments", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/parser/project.rs::PendingBinding.annotation", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/parser/project.rs::PendingLocalDeclaration.Binding.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/parser/project.rs::PendingLocalDeclaration.Newtype.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
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
    kind_site!("src/resolve.rs::$impl_Resolver::$fn_retain_type_nominals_with::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolve.rs::$impl_Resolver::$fn_retain_type_nominals_with::Task.Type.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolve.rs::DependencyExports.summary", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree, Borrowed),
    kind_site!("src/resolve.rs::ImportedConstructorFactBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ImportedTypeVariableBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::PendingInterfaceTypeParameters.methods", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::PendingInterfaceTypeParameters.parameters", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::PendingImplementation.head_parameters", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::PendingImplementation.prerequisite_only_parameters", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ResolveTaskBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ResolvedConstructorOwnerBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ResolvedDeclarationBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ResolvedDefinitionBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ResolvedEquationBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ResolvedExpressionBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ResolvedExpressionOwner.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ResolvedImplementationBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ResolvedImplementationMethodGroupBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ResolvedInterfaceBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ResolvedInterfaceMethodBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ResolvedMatchArmBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ResolvedNominalOwnerBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ResolvedNominalParameterOwnerBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ResolvedRequirementBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ResolvedTypedPatternBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ResolvedTypeOccurrenceBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ResolvedTypeOccurrenceOwner.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ResolveTask.FinishBinding.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::ResolveTask.FinishLocalNewtype.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::ResolveTask.FinishRecursiveGroup.group", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::ResolveTask.VisitBlock.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::ResolveTask.VisitExpr.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::ResolveTask.VisitRecursiveGroup.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolve.rs::ResolvedDeclarations.definitions", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolve.rs::ResolvedDeclarations.effects", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolve.rs::ResolvedDeclarations.implementations", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolve.rs::ResolvedDeclarations.interfaces", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolve.rs::ResolvedDeclarations.registry", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree, Shared),
    kind_site!("src/resolve.rs::ResolvedDeclarationParts.$alias", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolve.rs::ResolvedTypeBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::Resolver.imported", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolve.rs::Resolver.lexical_constructors", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::Resolver.lexical_nominal_parameters", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::Resolver.lexical_nominals", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::Resolver.lexical_method_parameters", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::Resolver.resolved_interfaces", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ValidatedImportedConstructorRoute.exported", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::AuthorizedImplementationFact.fact", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::CanonicalNominalKind.Frozen.kind", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/resolved.rs::CanonicalNominalKind.Parameters.parameters", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeRegistryTree),
    kind_site!("src/resolved.rs::CanonicalRepresentationFact.representation", FieldSummaryValueTypeValueResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::CheckedDefinition.source", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::CheckedGlobalScheme.scheme", FieldCheckedSchemeSchemeValueInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedImplementationBody.source", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::CheckedImplementationFact.application", FieldCheckedInterfaceArgumentInterfaceParameterInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedImplementationFact.head_parameters", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedImplementationFact.methods", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::CheckedImplementationFact.prerequisites", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedImplementationMethodFact.scheme", FieldCheckedSchemeSchemeValueInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedImplementationMethodFact.capture", FieldSummaryCarrierRetentionPreservedCarrierElaborationInferenceTypeSummaryTree, Shared),
    kind_site!("src/resolved.rs::CheckedInterfaceFact.methods", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::CheckedInterfaceFact.parameters", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree, Shared),
    kind_site!("src/resolved.rs::CheckedInterfaceMethodFact.method_binder_authority", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree, Shared),
    kind_site!("src/resolved.rs::CheckedInterfaceMethodFact.type_parameters", FieldCheckedDeclaredKindDeclaredInterfaceValidationInterfaceTypeCheckedTree, Shared),
    kind_site!("src/resolved.rs::CheckedInterfaceMethodFact.value_type", FieldCheckedValueTypeValueInterfaceValidationInterfaceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedModule.definitions", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::CheckedModule.effects", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::CheckedModule.imported_effects", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::CheckedModule.checked_implementations", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedModule.exports", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::CheckedModule.implementation_facts", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::CheckedModule.implementations", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::CheckedModule.interface_facts", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree, Shared),
    kind_site!("src/resolved.rs::CheckedModule.interfaces", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::CheckedModule.registry", FieldRegistryCarrierRetentionPreservedCarrierElaborationInferenceTypeRegistryTree, Shared),
    kind_site!("src/resolved.rs::CheckedModule.schemes", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::CheckedModuleParts.definitions", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::CheckedModuleParts.checked_implementations", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree),
    kind_site!("src/resolved.rs::CheckedModuleParts.exports", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::CheckedModuleParts.implementation_facts", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::CheckedModuleParts.implementations", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::CheckedModuleParts.interface_facts", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree, Shared),
    kind_site!("src/resolved.rs::CheckedModuleParts.schemes", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::CombinedRegistryBuilder.canonical_variables", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::CombinedRegistryBuilder.constructors", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::CombinedRegistryBuilder.lexical_constructors", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::CombinedRegistryBuilder.lexical_nominals", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::CombinedRegistryBuilder.nominals", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::CombinedRegistryBuilder.effects", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolved.rs::CombinedRegistryBuilder.nominal_parameters", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::CombinedRegistryBuilder.parameter_rows", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::CombinedRegistryBuilder.type_variables", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolved.rs::ExportSummary.constructors", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree, Mixed),
    kind_site!("src/resolved.rs::ExportSummary.canonical_representations", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ExportSummary.effects", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree, Mixed),
    kind_site!("src/resolved.rs::ExportSummary.hidden_constructors", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree, Mixed),
    kind_site!("src/resolved.rs::ExportSummary.hidden_interfaces", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree, Shared),
    kind_site!("src/resolved.rs::ExportSummary.hidden_nominals", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ExportSummary.implementations", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree, Mixed),
    kind_site!("src/resolved.rs::ExportSummary.interfaces", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree, Shared),
    kind_site!("src/resolved.rs::ExportSummary.nominals", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ExportSummary.terms", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree, Mixed),
    kind_site!("src/resolved.rs::ExportedConstructor.payload", FieldSummaryValueTypeValueResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ExportedConstructor.scheme", FieldSummarySchemeSchemeValueResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ExportedGlobal.scheme", FieldSummarySchemeSchemeValueResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ExportedHiddenType.parameters", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ExportedHiddenType.representation", FieldSummaryValueTypeValueResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ExportedType.parameters", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ExportedType.representation", FieldSummaryValueTypeValueResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ImportedConstructorFact.payload", FieldSummaryValueTypeValueResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ImportedConstructorFact.scheme", FieldSummarySchemeSchemeValueResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ImportedFacts.constructors", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree, Mixed),
    kind_site!("src/resolved.rs::ImportedFacts.canonical_representations", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ImportedFacts.effects", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree, Mixed),
    kind_site!("src/resolved.rs::ImportedFacts.globals", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree, Mixed),
    kind_site!("src/resolved.rs::ImportedFacts.implementations", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree, Mixed),
    kind_site!("src/resolved.rs::ImportedFacts.interfaces", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree, Shared),
    kind_site!("src/resolved.rs::ImportedFacts.nominals", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ImportedGlobalScheme.scheme", FieldSummarySchemeSchemeValueResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ImportedImplementationFact.fact", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree, Mixed),
    kind_site!("src/resolved.rs::ImportedInterfaceFact.fact", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree, Shared),
    kind_site!("src/resolved.rs::ImportedNominalFact.parameters", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ImportedNominalFact.representation", FieldSummaryValueTypeValueResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::ImportedNominalFactRef.parameters", FieldSummaryCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree, Borrowed),
    kind_site!("src/resolved.rs::ImportedNominalFactRef.representation", FieldSummaryValueTypeValueResolutionResolutionTypeSummaryTree, Borrowed),
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
    kind_site!("src/resolved.rs::ResolvedDefinitionKind.ForeignConstant.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedDefinitionKind.InlineOperational.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedEquation.body", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedEffectDeclaration.operations", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedEffectDeclaration.parameters", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedEffectInstance.instance", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedEffectOperation.annotation", FieldResolvedValueTypeValueResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedEquationalGlobal.equations", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedEquationalGlobal.interface", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedExpr.kind", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedExprKind.Add.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedExprKind.Apply.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedExprKind.Block.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedExprKind.Equal.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedExprKind.Function.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedExprKind.Handle.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedExprKind.Match.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedExprKind.Multiply.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedExprKind.Occurrence.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Shared),
    kind_site!("src/resolved.rs::ResolvedExprKind.Perform.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedExprKind.Resume.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedExprKind.Tuple.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedExternalInterface.annotation", FieldResolvedValueTypeValueResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedExternalInterface.requirements", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedExternalInterface.type_parameters", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedFunctionExpr.body", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedHandleExpr.body", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedHandleExpr.clauses", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedHandleExpr.effect", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedHandleExpr.hook_root", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedHandleExpr.hook_registration", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::HookRootContract.target", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::HookRegistrationContract.target", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolve.rs::ResolveTask.FinishHook.effect", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ResolveTask.FinishPerform.effect", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ResolveTask.FinishRegistration.effect", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::ResolvedHandlerClause.body", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedImplementation.head", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedImplementation.head_parameters", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedImplementation.method_groups", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedImplementation.prerequisite_only_parameters", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedImplementation.prerequisites", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedImplementationMethodGroup.equations", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedImplementationMethodGroup.contextual_parameters", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedInlineOperationalGlobal.body", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedInlineOperationalGlobal.header", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedInlineOperationalHeader.parameters", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedInlineOperationalHeader.requirements", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedInlineOperationalHeader.result_effects", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedInlineOperationalHeader.result_type", FieldResolvedValueTypeValueResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedInlineOperationalHeader.type_parameters", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedInterfaceDeclaration.methods", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedInterfaceApplication.arguments", FieldResolvedInterfaceArgumentInterfaceParameterResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedInterfaceDeclaration.parameters", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Shared),
    kind_site!("src/resolved.rs::ResolvedInterfaceMethod.annotation", FieldResolvedValueTypeValueResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedInterfaceMethod.type_parameters", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Shared),
    kind_site!("src/resolved.rs::ResolvedLocalDeclaration.Binding.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedLocalDeclaration.Recursive.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedMatchArm.body", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedMatchExpr.arms", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedMatchExpr.scrutinee", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModule.definitions", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModule.effects", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModule.implementations", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModule.imported", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModule.interfaces", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModule.registry", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree, Shared),
    kind_site!("src/resolved.rs::ResolvedModuleGroup.definitions", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModuleGroup.checked_implementations", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree),
    kind_site!("src/resolved.rs::ResolvedModuleGroup.implementation_facts", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModuleGroup.implementations", FieldCheckedCarrierRetentionPreservedCarrierElaborationInferenceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModuleGroup.interface_facts", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree, Shared),
    kind_site!("src/resolved.rs::ResolvedModuleGroup.interfaces", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModuleGroup.schemes", FieldCheckedCarrierRetentionPreservedCarrierInterfaceValidationInterfaceTypeCheckedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModuleParts.definitions", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModuleParts.effects", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModuleParts.implementations", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModuleParts.imported", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModuleParts.interfaces", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModuleParts.registry", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree, Shared),
    kind_site!("src/resolved.rs::ResolvedModuleProgram.groups", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedModuleProgram.registry", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree, Shared),
    kind_site!("src/resolved.rs::ResolvedModuleProgram.result", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedNominalBuffer.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedNominalParameterBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::ResolvedNominalParameterVecBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::ResolvedGlobalParameterVecBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::ResolvedOccurrence.evidence", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Shared),
    kind_site!("src/resolved.rs::ResolvedPerformExpr.effect", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedPerformExpr.operand", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedRecursiveGroup.members", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedRecursiveMember.annotation", FieldResolvedValueTypeValueResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedRecursiveMember.initializer", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedRegistry.abstract_nominal_kinds", FieldRegistryCarrierRetentionPreservedCarrierElaborationInferenceTypeRegistryTree),
    kind_site!("src/resolved.rs::ResolvedRegistry.constructors", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree),
    kind_site!("src/resolved.rs::ResolvedRegistry.lexical_constructors", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree),
    kind_site!("src/resolved.rs::ResolvedRegistry.lexical_nominals", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree),
    kind_site!("src/resolved.rs::ResolvedRegistry.nominals", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree),
    kind_site!("src/resolved.rs::ResolvedRegistry.effects", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedRegistry.nominal_parameters", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree),
    kind_site!("src/resolved.rs::ResolvedRegistry.type_variables", FieldRegistryCarrierRetentionPreservedCarrierResolutionResolutionTypeRegistryTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedRequirement.application", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedNominalType.representation", FieldResolvedValueTypeValueResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedResumeExpr.value", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedType.ty", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedTypeVariableBuffer.0", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolved.rs::ResolvedTypeVariable.kind", FieldResolvedDeclaredKindDeclaredResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedTypedPattern.annotation", FieldResolvedValueTypeValueResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::SummaryDeterminedApplicationSlices.dependents", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
    kind_site!("src/resolved.rs::SummaryDeterminedApplicationSlices.key", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSummaryTree),
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
    kind_site!("src/surface.rs::FunctionType.effects", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::InlineOperationalGlobal.body", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::InlineOperationalGlobal.header", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceBinding.annotation", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceBinding.initializer", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceBlock.declarations", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceBlock.result", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceCleanupExpr.action", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceCleanupExpr.body", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceConstructorDeclaration.fields", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceDefinition.kind", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceDefinitionKind.Equational.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceDefinitionKind.InlineOperational.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceEffectDeclaration.operations", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceEffectDeclaration.parameters", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceEffectInstance.arguments", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceEffectOperation.annotation", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceEffectRow.effects", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceEquation.body", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExpr.kind", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExprKind.Add.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExprKind.Apply.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExprKind.Block.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExprKind.Cleanup.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExprKind.Equal.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExprKind.Function.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExprKind.Handle.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExprKind.Hook.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExprKind.Registration.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExprKind.Match.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExprKind.Multiply.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExprKind.Perform.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExprKind.Resume.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExprKind.Resource.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceResourceExpr.body", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceResourceExpr.initializer", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExprKind.Tuple.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExternalInterface.annotation", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExternalInterface.requirements", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExternalInterface.type_parameters", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceImplementation.equations", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceImplementation.head", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceImplementation.prerequisites", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceImplementation.type_parameters", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceHandleExpr.body", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceHandleExpr.clauses", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceHandleExpr.effect", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceHookExpr.body", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceHookExpr.effect", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceRegistrationExpr.body", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceRegistrationExpr.effect", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceRegistrationExpr.transformer", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceHandlerClause.body", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceInlineOperationalHeader.parameters", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceInlineOperationalHeader.requirements", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceInlineOperationalHeader.result_effects", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceInlineOperationalHeader.result_type", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceInlineOperationalHeader.type_parameters", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceInterfaceDeclaration.methods", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceInterfaceApplication.arguments", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceInterfaceDeclaration.parameters", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceInterfaceMethod.annotation", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceInterfaceMethod.type_parameters", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceKind.kind", FieldSurfaceDeclaredKindDeclaredProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceKindKind.Function.codomain", FieldSurfaceDeclaredKindDeclaredProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceKindKind.Function.domain", FieldSurfaceDeclaredKindDeclaredProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceLocalDeclaration.Binding.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceLocalDeclaration.Newtype.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceLocalDeclaration.Recursive.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceMatchArm.body", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceMatchExpr.arms", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceMatchExpr.scrutinee", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceModule.definitions", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceModule.effects", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceModule.implementations", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceModule.interfaces", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceModule.type_declarations", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfacePerformExpr.arguments", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfacePerformExpr.operand", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceRecursiveGroup.members", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceRecursiveMember.annotation", FieldSurfaceProjectionOnlyDeferredProjectionProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceRecursiveMember.initializer", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceRequirement.$alias", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
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
    kind_site!("src/types.rs::Type.EffectfulFunction.0", FieldCanonicalApplicationStructureStructuralSubtreeTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::Type.EffectfulFunction.1", FieldCanonicalApplicationStructureStructuralSubtreeTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::Type.Tuple.0", FieldCanonicalApplicationStructureStructuralSubtreeTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::ComputationType.effects", FieldCanonicalApplicationStructureStructuralSubtreeTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::ComputationType.value", FieldCanonicalApplicationStructureStructuralSubtreeTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::EffectInstance.arguments", FieldCanonicalApplicationStructureStructuralSubtreeTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::EffectRow.known", FieldCanonicalApplicationStructureStructuralSubtreeTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::EffectRow.tail", FieldCanonicalApplicationStructureStructuralSubtreeTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::EffectRowTail.lacks", FieldCanonicalApplicationStructureStructuralSubtreeTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::FunctionTypeView.domain", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::FunctionTypeView.effects", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::FunctionTypeView.value", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_clone_kind_with_budget::Task.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/types.rs::$fn_discard_type_iteratively::Task.Sequence.0", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork),
    kind_site!("src/types.rs::$fn_discard_type_iteratively::Task.EffectInstances.0", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork),
    kind_site!("src/types.rs::$fn_discard_type_iteratively::Task.Visit.0", FieldTransientCarrierRetentionPreservedCarrierTypeOperationTypeTransientWork),
    kind_site!("src/types.rs::TypeHashTask.EffectRow.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::TypeHashTask.Instance.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::TypeHashTask.Instances.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::TypeHashTask.Kind.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/types.rs::TypeHashTask.Parameter.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/types.rs::TypeHashTask.Parameters.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/types.rs::TypeHashTask.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::TypeHashTask.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_render_kind_with_budget::RenderedKind.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/types.rs::$fn_same_type::Task.Compare.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_same_type::Task.Compare.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_same_type::Task.CompareRows.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_same_type::Task.CompareRows.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_same_type::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_same_type_with_budget::Task.Compare.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_same_type_with_budget::Task.Compare.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_same_type_with_budget::Task.CompareRows.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_same_type_with_budget::Task.CompareRows.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_same_type_with_budget::Task.Sequence.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/types.rs::$fn_write_kind::Task.kind", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
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
    kind_site_for!("src/core/dialect.rs::$kind.typed_expr_ordinary_result", "src/core/dialect.rs::CoreTypedExpr.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/dialect.rs::$kind.typed_expr_type_abstraction_scheme", "src/core/dialect.rs::CoreTypedExpr.ty", KindSiteCoreSchemeSchemeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/dialect.rs::$kind.typed_expr_type_application_result", "src/core/dialect.rs::CoreTypedExpr.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
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
    // Region carriers retain the existing ownership boundaries: automatic Core
    // binder metadata, borrowed Source work, owned lowering rows, and shared
    // runtime code/instantiation. Captured continuation segments remain Mixed.
    kind_site!("src/core/capture/control.rs::Control.Call.prefix", FieldSummaryCarrierRetentionPreservedCarrierElaborationInferenceTypeSummaryTree, Shared),
    kind_site!("src/core/effect.rs::$impl_CoreBuilder::$fn_replay_effect_rows_in_range::Equation.Region.0", FieldTransientCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeTransientWork),
    kind_site!("src/core/effect.rs::EffectOperation.Region.0", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/effect.rs::EffectOperation.RegionClosure.0", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/region.rs::RegionClosureCode.Function.0", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/region.rs::RegionClosureNode.code", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/core/region.rs::RegionScopeNode.access", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree),
    kind_site!("src/driver.rs::ModularEffectCoreResult.$alias", FieldCoreCarrierRetentionPreservedCarrierCoreAdmissionCoreTypeCoreTree, Shared),
    kind_site!("src/elaborate.rs::ElaborationTask.FinishRegion.0", FieldMixedTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTreeAndTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.FinishSelection.0", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate.rs::ElaborationTask.RegionBody.source", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::ElaborationTask.SelectionBody.source", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate.rs::EquationsProgress.outer_arrow_effects", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate/region.rs::RegionProgress.access", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate/region.rs::RegionProgress.provider", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate/region.rs::RegionProgress.provider_rows", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate/region.rs::RegionProgress.source", FieldBorrowedResolvedCarrierRetentionPreservedCarrierElaborationInferenceTypeResolvedTree),
    kind_site!("src/elaborate/region.rs::SelectionProgress.operand", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/elaborate/region.rs::SelectionProgress.selected", FieldTransientCarrierRetentionPreservedCarrierElaborationInferenceTypeTransientWork),
    kind_site!("src/eval/machine.rs::Frame.RegionAllocated.segment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Mixed),
    kind_site!("src/eval/machine.rs::Frame.RegionBoundary.allocate", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.RegionBoundary.preceding", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.RegionBoundary.release", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.RegionBuffer.0", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.RegionCompletion.allocate", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.RegionCompletion.preceding", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.RegionCompletion.saved", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.RegionContext.environment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.RegionForwarding.environment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.RegionPreceding.environment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.RegionProvider.environment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.RegionProvider.preceding", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.RegionRequest.context", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.RegionTuple.environment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Frame.RegionTuple.fields", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::Instantiation.$alias", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/machine.rs::ResourcePayload.Cell.0", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/region.rs::BufferProgress.environment", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/region.rs::BufferProgress.left", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/region.rs::BufferProgress.prepared", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/region.rs::PreparedBuffer.payload", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/value.rs::ClosureCode.instantiation", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/value.rs::ClosureCode.program", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/value.rs::RegionFunction.instantiation", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/value.rs::Value.ClosureCode.0", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/eval/value.rs::Value.RegionFunction.0", FieldTransientCarrierRetentionPreservedCarrierEvaluationEvaluationEvaluatorState, Shared),
    kind_site!("src/evidence_validation.rs::LinkedLocalScope.Region.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierEvidenceValidationEvidenceTypeResolvedTree),
    kind_site!("src/kind.rs::BodyWork.RegionBody.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolvedKindResolutionTypeResolvedTree),
    kind_site!("src/resolve.rs::ResolveTask.FinishRegion.identity", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ResolveTask.FinishRegion.provider", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork, Mixed),
    kind_site!("src/resolve.rs::ResolveTask.RegionProvider.identity", FieldTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeTransientWork),
    kind_site!("src/resolve.rs::ResolveTask.RegionProvider.source", FieldBorrowedTransientCarrierRetentionPreservedCarrierResolutionResolutionTypeSurfaceTree),
    kind_site!("src/resolved.rs::ResolvedExprKind.Region.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedExprKind.RegionSelection.0", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedRegionExpr.body", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedRegionExpr.identity", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree),
    kind_site!("src/resolved.rs::ResolvedRegionExpr.provider", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedRegionSelectionExpr.body", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/resolved.rs::ResolvedRegionSelectionExpr.region", FieldResolvedCarrierRetentionPreservedCarrierResolutionResolutionTypeResolvedTree, Mixed),
    kind_site!("src/surface.rs::SurfaceExprKind.Region.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceExprKind.RegionSelection.0", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceRegionExpr.body", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceRegionExpr.provider", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceRegionSelectionExpr.body", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
    kind_site!("src/surface.rs::SurfaceRegionSelectionExpr.region", FieldSurfaceCarrierRetentionPreservedCarrierProjectionProjectionSurfaceTree),
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
    kind_site_for!("src/core/dialect.rs::$kind.typed_expr_ordinary_result", "src/core/dialect.rs::CoreTypedExpr.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/dialect.rs::$kind.typed_expr_type_abstraction_scheme", "src/core/dialect.rs::CoreTypedExpr.ty", KindSiteCoreSchemeSchemeValueCoreAdmissionCoreTypeCoreTree),
    kind_site_for!("src/core/dialect.rs::$kind.typed_expr_type_application_result", "src/core/dialect.rs::CoreTypedExpr.ty", KindSiteCoreValueTypeValueCoreAdmissionCoreTypeCoreTree),
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
        "src/core/dialect.rs::CoreTypedExpr.ty",
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
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_core_with_ledger::Continuation.ApplicationArgument.function", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_core_with_ledger::Continuation.ApplicationFunction.argument", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_core_with_ledger::Continuation.ApplicationFunction.argument_mirror", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_core_with_ledger::Continuation.FunctionDomain.codomain", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_core_with_ledger::Continuation.FunctionDomain.codomain_mirror", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_core_with_ledger::Continuation.Tuple.remaining", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_core_with_ledger::Continuation.Tuple.remaining_mirrors", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_core_with_ledger::State.Complete.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationKindKindTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_core_with_ledger::State.Visit.0", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
    kind_site!("src/kind.rs::$impl_KindEnvironments::$fn_synthesize_core_with_ledger::State.Visit.1", FieldBorrowedTransientCarrierRetentionPreservedCarrierTypeOperationTypeTypeTree),
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
            Kind::Type | Kind::EffectRow | Kind::Arrow(_, _) => {}
        }
    }

    fn exhaust_type_variants(ty: &Type) {
        match ty {
            Type::Bytes
            | Type::String
            | Type::Int
            | Type::Bool
            | Type::Unit
            | Type::Tuple(_)
            | Type::Nominal(_)
            | Type::Variable(_)
            | Type::Inference(_)
            | Type::Application(_, _)
            | Type::ResourceApply(_, _)
            | Type::Forall(_, _)
            | Type::Function(_, _)
            | Type::EffectfulFunction(_, _) => {}
        }
    }

    fn exhaust_owner_argument_variants(argument: &ash::types::KindedArgument) {
        match argument {
            ash::types::KindedArgument::TypeArg(_) | ash::types::KindedArgument::RowArg(_) => {}
        }
    }

    exhaust_kind_variants(&Kind::Type);
    exhaust_type_variants(&Type::Unit);
    exhaust_owner_argument_variants(&ash::types::KindedArgument::TypeArg(Type::Unit));
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

const SURFACE_SOURCE: &str = include_str!("../src/surface.rs");
const RESOLVED_SOURCE: &str = include_str!("../src/resolved.rs");
const INTERFACE_SOURCE: &str = include_str!("../src/interface.rs");
const EVIDENCE_SOURCE: &str = include_str!("../src/evidence.rs");
const EVIDENCE_VALIDATION_SOURCE: &str = include_str!("../src/evidence_validation.rs");
const ELABORATE_SOURCE: &str = include_str!("../src/elaborate.rs");
const CORE_DIALECT_SOURCE: &str = include_str!("../src/core/dialect.rs");
const CORE_TRANSFORM_SOURCE: &str = include_str!("../src/core/transform.rs");

#[derive(Clone, Copy)]
struct MethodParameterCarrier {
    key: &'static str,
    path: &'static str,
    source: &'static str,
    marker: &'static str,
}

macro_rules! method_parameter_carrier {
    ($key:literal, $path:literal, $source:ident, $marker:literal) => {
        MethodParameterCarrier {
            key: $key,
            path: $path,
            source: $source,
            marker: $marker,
        }
    };
}

const METHOD_PARAMETER_CARRIERS: &[MethodParameterCarrier] = &[
    method_parameter_carrier!(
        "syntax.cst_method_parameter_list",
        "src/parser/grammar.rs",
        PARSER_GRAMMAR,
        "TypeParameterOwnerBoundary::InterfaceMethod"
    ),
    method_parameter_carrier!(
        "syntax.projected_method_parameter_list",
        "src/parser/project.rs",
        PARSER_PROJECTION,
        "type_parameters: project_optional_type_parameters"
    ),
    method_parameter_carrier!(
        "syntax.surface_method_parameter_list",
        "src/surface.rs",
        SURFACE_SOURCE,
        "pub type_parameters: Option<Vec<SurfaceTypeParameter>>"
    ),
    method_parameter_carrier!(
        "binder.resolved_method_parameters",
        "src/resolved.rs",
        RESOLVED_SOURCE,
        "pub type_parameters: SharedOwnerParameters"
    ),
    method_parameter_carrier!(
        "binder.resolved_explicit_list_bit",
        "src/resolved.rs",
        RESOLVED_SOURCE,
        "pub has_explicit_type_parameters: bool"
    ),
    method_parameter_carrier!(
        "binder.checked_method_parameters",
        "src/resolved.rs",
        RESOLVED_SOURCE,
        "pub(crate) type_parameters: SharedOwnerParameters"
    ),
    method_parameter_carrier!(
        "binder.private_method_authority",
        "src/resolved.rs",
        RESOLVED_SOURCE,
        "method_binder_authority: Option<SharedOwnerParameters>"
    ),
    method_parameter_carrier!(
        "scheme.checked_method_value_type",
        "src/resolved.rs",
        RESOLVED_SOURCE,
        "pub(crate) value_type: Type"
    ),
    method_parameter_carrier!(
        "scheme.checked_method_annotation_span",
        "src/resolved.rs",
        RESOLVED_SOURCE,
        "annotation_span: Span"
    ),
    method_parameter_carrier!(
        "scheme.implementation_method_scheme",
        "src/resolved.rs",
        RESOLVED_SOURCE,
        "pub scheme: ConstrainedScheme"
    ),
    method_parameter_carrier!(
        "scheme.implementation_head_boundary",
        "src/resolved.rs",
        RESOLVED_SOURCE,
        "pub(crate) head_type_parameter_count: usize"
    ),
    method_parameter_carrier!(
        "summary.imported_authority_method_index",
        "src/resolved.rs",
        RESOLVED_SOURCE,
        "authority_method_indices: Box<[usize]>"
    ),
    method_parameter_carrier!(
        "occurrence.selector_method_scheme",
        "src/evidence.rs",
        EVIDENCE_SOURCE,
        "struct MethodEntry"
    ),
    method_parameter_carrier!(
        "occurrence.obligation_metadata_arguments",
        "src/evidence.rs",
        EVIDENCE_SOURCE,
        "pub(crate) struct MethodObligationMetadata"
    ),
    method_parameter_carrier!(
        "occurrence.pending_arguments",
        "src/evidence.rs",
        EVIDENCE_SOURCE,
        "struct PendingObligation"
    ),
    method_parameter_carrier!(
        "occurrence.rigid_arguments",
        "src/evidence.rs",
        EVIDENCE_SOURCE,
        "pub(crate) struct MethodRigidityCondition"
    ),
    method_parameter_carrier!(
        "occurrence.rigidity_diagnostic_site",
        "src/evidence.rs",
        EVIDENCE_SOURCE,
        "pub(crate) struct MethodRigiditySite"
    ),
    method_parameter_carrier!(
        "occurrence.rigidity_match_rank",
        "src/evidence.rs",
        EVIDENCE_SOURCE,
        "enum MethodRigidityMatchRank"
    ),
    method_parameter_carrier!(
        "occurrence.rigidity_target",
        "src/evidence.rs",
        EVIDENCE_SOURCE,
        "pub(crate) struct MethodRigidityTarget"
    ),
    method_parameter_carrier!(
        "occurrence.rigidity_determination_snapshot",
        "src/evidence.rs",
        EVIDENCE_SOURCE,
        "pub(crate) struct MethodRigidityDeterminationSnapshot"
    ),
    method_parameter_carrier!(
        "occurrence.selected_rigidity",
        "src/evidence.rs",
        EVIDENCE_SOURCE,
        "struct SelectedMethodRigidity"
    ),
    method_parameter_carrier!(
        "occurrence.borrowed_rigidity_check",
        "src/evidence.rs",
        EVIDENCE_SOURCE,
        "pub(crate) struct MethodRigidityCheck"
    ),
    method_parameter_carrier!(
        "occurrence.selected_arguments",
        "src/evidence.rs",
        EVIDENCE_SOURCE,
        "struct SelectedOccurrence"
    ),
    method_parameter_carrier!(
        "occurrence.atomic_publication",
        "src/evidence.rs",
        EVIDENCE_SOURCE,
        "pub(crate) struct PendingEvidencePublication"
    ),
    method_parameter_carrier!(
        "occurrence.borrowed_selection_method",
        "src/evidence.rs",
        EVIDENCE_SOURCE,
        "pub(crate) struct SelectionMethod"
    ),
    method_parameter_carrier!(
        "occurrence.filled_slot_arguments",
        "src/interface.rs",
        INTERFACE_SOURCE,
        "struct FilledEvidenceSlot"
    ),
    method_parameter_carrier!(
        "occurrence.current_implementation_method_arguments",
        "src/elaborate.rs",
        ELABORATE_SOURCE,
        "struct CurrentImplementationMethod"
    ),
    method_parameter_carrier!(
        "linked.authenticated_program_catalog",
        "src/evidence_validation.rs",
        EVIDENCE_VALIDATION_SOURCE,
        "method_evidence: Arc<MethodEvidenceCatalog>"
    ),
    method_parameter_carrier!(
        "linked.authentication_capability",
        "src/evidence_validation.rs",
        EVIDENCE_VALIDATION_SOURCE,
        "struct MethodEvidenceAuthentication"
    ),
    method_parameter_carrier!(
        "linked.catalog_carrier",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "pub(crate) struct MethodEvidenceCatalog"
    ),
    method_parameter_carrier!(
        "linked.catalog_methods",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "methods: Vec<MethodEvidenceMethod>"
    ),
    method_parameter_carrier!(
        "linked.catalog_implementation_owners",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "implementation_owners: Vec<MethodEvidenceImplementationOwner>"
    ),
    method_parameter_carrier!(
        "linked.catalog_lexical_owners",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "lexical_owners: Vec<MethodEvidenceLexicalOwner>"
    ),
    method_parameter_carrier!(
        "linked.lexical_owner_relation",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "pub(crate) struct MethodEvidenceLexicalOwner"
    ),
    method_parameter_carrier!(
        "linked.catalog_domains",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "domains: Vec<MethodEvidenceDomain>"
    ),
    method_parameter_carrier!(
        "linked.catalog_occurrences",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "occurrences: Vec<MethodEvidenceOccurrence>"
    ),
    method_parameter_carrier!(
        "linked.catalog_adapters",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "adapters: Vec<MethodEvidenceAdapter>"
    ),
    method_parameter_carrier!(
        "linked.catalog_concrete_sources",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "concrete_sources: Vec<MethodEvidenceConcreteSource>"
    ),
    method_parameter_carrier!(
        "linked.catalog_expectations",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "expectations: Vec<MethodEvidenceExpectation>"
    ),
    method_parameter_carrier!(
        "linked.method_parameters_and_value_type",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "pub(crate) struct MethodEvidenceMethod"
    ),
    method_parameter_carrier!(
        "linked.implementation_owner_parameters",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "pub(crate) struct MethodEvidenceImplementationOwner"
    ),
    method_parameter_carrier!(
        "linked.domain_relation",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "pub(crate) struct MethodEvidenceDomain"
    ),
    method_parameter_carrier!(
        "linked.resource_owner_identity",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "pub(crate) enum MethodEvidenceResourceOwner"
    ),
    method_parameter_carrier!(
        "linked.owner_identity",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "pub(crate) enum MethodEvidenceOwner"
    ),
    method_parameter_carrier!(
        "linked.expected_role",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "pub(crate) enum MethodEvidenceExpectedRole"
    ),
    method_parameter_carrier!(
        "linked.expectation_relation",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "pub(crate) struct MethodEvidenceExpectation"
    ),
    method_parameter_carrier!(
        "linked.occurrence_arguments",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "pub(crate) struct MethodEvidenceOccurrence"
    ),
    method_parameter_carrier!(
        "adapter.generated_adapter_parameters",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "pub(crate) struct MethodEvidenceAdapter"
    ),
    method_parameter_carrier!(
        "adapter.prerequisite_method_parameters",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "pub(crate) struct MethodEvidenceAdapterEdge"
    ),
    method_parameter_carrier!(
        "adapter.concrete_source_arguments",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "pub(crate) struct MethodEvidenceConcreteSource"
    ),
    method_parameter_carrier!(
        "adapter.concrete_prerequisite_relation",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "pub(crate) struct MethodEvidenceConcretePrerequisite"
    ),
    method_parameter_carrier!(
        "adapter.expected_producer_relation",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "pub(crate) enum MethodEvidenceExpectedProducer"
    ),
    method_parameter_carrier!(
        "adapter.producer_identity",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "pub(crate) enum MethodEvidenceProducer"
    ),
    method_parameter_carrier!(
        "core_authentication.lowered_interface_scheme",
        "src/elaborate.rs",
        ELABORATE_SOURCE,
        "struct LoweredInterfaceMethod"
    ),
    method_parameter_carrier!(
        "core_authentication.lowered_implementation_scheme",
        "src/elaborate.rs",
        ELABORATE_SOURCE,
        "struct LoweredImplementationMethod"
    ),
    method_parameter_carrier!(
        "core_authentication.lowered_evidence_adapter",
        "src/elaborate.rs",
        ELABORATE_SOURCE,
        "struct LoweredEvidenceMethod"
    ),
    method_parameter_carrier!(
        "core_authentication.active_evidence_binder",
        "src/elaborate.rs",
        ELABORATE_SOURCE,
        "struct ActiveEvidenceBinder"
    ),
    method_parameter_carrier!(
        "core_authentication.polymorphic_evidence_producer",
        "src/elaborate.rs",
        ELABORATE_SOURCE,
        "enum PolymorphicEvidenceProducer"
    ),
    method_parameter_carrier!(
        "core_authentication.scoped_evidence_binder",
        "src/elaborate.rs",
        ELABORATE_SOURCE,
        "struct ScopedEvidenceBinder"
    ),
    method_parameter_carrier!(
        "core_authentication.evidence_lowering_maps",
        "src/elaborate.rs",
        ELABORATE_SOURCE,
        "struct EvidenceLowering"
    ),
    method_parameter_carrier!(
        "core_authentication.lexical_evidence_progress",
        "src/elaborate.rs",
        ELABORATE_SOURCE,
        "struct LexicalEvidenceProgress"
    ),
    method_parameter_carrier!(
        "core_authentication.evidence_specification_buffer",
        "src/elaborate.rs",
        ELABORATE_SOURCE,
        "struct EvidenceSpecificationBuffer"
    ),
    method_parameter_carrier!(
        "core_authentication.evidence_specification_sequence",
        "src/elaborate.rs",
        ELABORATE_SOURCE,
        "struct EvidenceSpecificationSequence"
    ),
    method_parameter_carrier!(
        "core_authentication.anchor_role",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "pub(crate) enum MethodEvidenceAnchorRole"
    ),
    method_parameter_carrier!(
        "core_authentication.anchor",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "pub(crate) struct MethodEvidenceAnchor"
    ),
    method_parameter_carrier!(
        "core_authentication.unvalidated_catalog_and_anchors",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "pub struct UnvalidatedCoreProgram"
    ),
    method_parameter_carrier!(
        "core_authentication.validated_catalog_and_anchors",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "pub struct CoreProgram"
    ),
    method_parameter_carrier!(
        "core_authentication.validated_capability",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "pub struct ValidatedCoreProgram"
    ),
    method_parameter_carrier!(
        "core_authentication.builder_catalog_anchors_and_consumption",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "consumed_method_evidence: Vec<bool>"
    ),
    method_parameter_carrier!(
        "transformation.shared_catalog",
        "src/core/transform.rs",
        CORE_TRANSFORM_SOURCE,
        "Arc::clone(program.method_evidence())"
    ),
    method_parameter_carrier!(
        "transformation.remapped_anchors",
        "src/core/transform.rs",
        CORE_TRANSFORM_SOURCE,
        "program.method_evidence_anchors()"
    ),
    method_parameter_carrier!(
        "teardown.checked_method",
        "src/resolved.rs",
        RESOLVED_SOURCE,
        "impl Drop for CheckedInterfaceMethodFact"
    ),
    method_parameter_carrier!(
        "teardown.pending_occurrence",
        "src/evidence.rs",
        EVIDENCE_SOURCE,
        "impl Drop for PendingObligation"
    ),
    method_parameter_carrier!(
        "teardown.selected_occurrence",
        "src/evidence.rs",
        EVIDENCE_SOURCE,
        "impl Drop for SelectedOccurrence"
    ),
    method_parameter_carrier!(
        "teardown.published_occurrence",
        "src/interface.rs",
        INTERFACE_SOURCE,
        "impl Drop for FilledEvidenceSlot"
    ),
    method_parameter_carrier!(
        "teardown.linked_occurrence",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "impl Drop for MethodEvidenceOccurrence"
    ),
    method_parameter_carrier!(
        "teardown.adapter",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "impl Drop for MethodEvidenceAdapter"
    ),
    method_parameter_carrier!(
        "teardown.unvalidated_core",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "Drop for UnvalidatedCoreProgram"
    ),
    method_parameter_carrier!(
        "teardown.validated_core",
        "src/core/dialect.rs",
        CORE_DIALECT_SOURCE,
        "Drop for CoreProgram"
    ),
];

#[test]
fn method_parameter_carrier_inventory_is_stage_complete_and_source_attached() {
    let required_stages = BTreeSet::from([
        "syntax",
        "binder",
        "scheme",
        "occurrence",
        "summary",
        "linked",
        "adapter",
        "core_authentication",
        "transformation",
        "teardown",
    ]);
    let mut actual_stages = BTreeSet::new();
    let mut keys = BTreeSet::new();

    for carrier in METHOD_PARAMETER_CARRIERS {
        assert!(
            keys.insert(carrier.key),
            "duplicate carrier key: {}",
            carrier.key
        );
        actual_stages.insert(
            carrier
                .key
                .split_once('.')
                .expect("carrier keys must name their stage")
                .0,
        );
        assert!(
            carrier.source.contains(carrier.marker),
            "{} is detached from {} marker {:?}",
            carrier.key,
            carrier.path,
            carrier.marker,
        );
    }

    assert_eq!(actual_stages, required_stages);
    assert!(
        !std::mem::needs_drop::<Span>(),
        "the imported annotation Span is a zero-allocation, zero-traversal copy carrier",
    );
}

fn declared_carrier_names(source: &str, include: impl Fn(&str) -> bool) -> BTreeSet<String> {
    production_rust_code_tokens(source)
        .windows(2)
        .filter(|window| matches!(window[0], "struct" | "enum") && include(window[1]))
        .map(|window| window[1].to_owned())
        .collect()
}

fn manifested_declared_carrier_names(
    path: &str,
    include: impl Fn(&str) -> bool,
) -> BTreeSet<String> {
    METHOD_PARAMETER_CARRIERS
        .iter()
        .filter(|carrier| carrier.path == path)
        .flat_map(|carrier| rust_code_tokens(carrier.marker))
        .collect::<Vec<_>>()
        .windows(2)
        .filter(|window| matches!(window[0], "struct" | "enum") && include(window[1]))
        .map(|window| window[1].to_owned())
        .collect()
}

#[test]
fn method_evidence_and_scope_carriers_are_bidirectionally_manifested() {
    let occurrence_declared = declared_carrier_names(EVIDENCE_SOURCE, |name| {
        name.starts_with("Method")
            || name.starts_with("SelectedMethod")
            || matches!(
                name,
                "PendingObligation"
                    | "SelectedOccurrence"
                    | "PendingEvidencePublication"
                    | "SelectionMethod"
            )
    });
    let occurrence_manifested = manifested_declared_carrier_names("src/evidence.rs", |name| {
        name.starts_with("Method")
            || name.starts_with("SelectedMethod")
            || matches!(
                name,
                "PendingObligation"
                    | "SelectedOccurrence"
                    | "PendingEvidencePublication"
                    | "SelectionMethod"
            )
    });
    assert_eq!(occurrence_manifested, occurrence_declared);

    let authentication_declared = declared_carrier_names(EVIDENCE_VALIDATION_SOURCE, |name| {
        name == "MethodEvidenceAuthentication"
    });
    let authentication_manifested =
        manifested_declared_carrier_names("src/evidence_validation.rs", |name| {
            name == "MethodEvidenceAuthentication"
        });
    assert_eq!(authentication_manifested, authentication_declared);

    let core_declared = declared_carrier_names(CORE_DIALECT_SOURCE, |name| {
        name.starts_with("MethodEvidence") && !name.ends_with("ForTest")
    });
    let core_manifested = manifested_declared_carrier_names("src/core/dialect.rs", |name| {
        name.starts_with("MethodEvidence") && !name.ends_with("ForTest")
    });
    assert_eq!(core_manifested, core_declared);

    let scope_declared = declared_carrier_names(ELABORATE_SOURCE, |name| {
        name.contains("Evidence") || name == "PolymorphicEvidenceProducer"
    });
    let scope_manifested = manifested_declared_carrier_names("src/elaborate.rs", |name| {
        name.contains("Evidence") || name == "PolymorphicEvidenceProducer"
    });
    assert_eq!(scope_manifested, scope_declared);
}

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
    module: String,
    module_imports: BTreeMap<String, String>,
    module_declarations: BTreeSet<String>,
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
    let retention_membership = RetentionMembership::new(&retention_modes);
    let retention_mismatches = fields
        .iter()
        .filter_map(|field| {
            let key = field.key();
            if !actual.contains(&key) {
                return None;
            }
            let derived = field_type_retention(field, &declarations, &retention_membership)
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
         use std::borrow::Cow as CopyOnWrite; \
         struct QualifiedCow<'a>(std::borrow::Cow<'a, crate::types::Type>); \
         struct AllocCow<'a>(alloc::borrow::Cow<'a, crate::types::Type>); \
         struct AliasedCow<'a>(CopyOnWrite<'a, crate::types::Type>); \
         type CowAlias<'a> = std::borrow::Cow<'a, crate::types::Type>; \
         struct TypeAliasedCow<'a>(CowAlias<'a>); \
         struct BorrowedCow<'a>(&'a std::borrow::Cow<'a, crate::types::Type>); \
         struct SharedCow<'a>(std::sync::Arc<std::borrow::Cow<'a, crate::types::Type>>); \
         struct Cow<T>(T); \
         struct LocalCow<'a>(Cow<crate::types::Type>); \
         mod local { pub struct Cow<T>(T); } \
         struct QualifiedLocalCow(local::Cow<crate::types::Type>); \
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
        ("QualifiedCow", RetentionMode::Mixed),
        ("AllocCow", RetentionMode::Mixed),
        ("AliasedCow", RetentionMode::Mixed),
        ("CowAlias", RetentionMode::Mixed),
        ("TypeAliasedCow", RetentionMode::Mixed),
        ("BorrowedCow", RetentionMode::Borrowed),
        ("SharedCow", RetentionMode::Mixed),
        ("LocalCow", RetentionMode::Owned),
        ("QualifiedLocalCow", RetentionMode::Owned),
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

#[test]
fn carrier_scanner_resolves_inherited_shared_wrappers_without_erasing_borrowed_paths() {
    let sources = [
        ("src/lib.rs", "mod types; mod parent; mod facade; mod user;"),
        ("src/types.rs", "struct Type;"),
        (
            "src/parent.rs",
            "pub use std::sync::Arc; pub use std::rc::Rc; mod child;",
        ),
        (
            "src/parent/child.rs",
            r#"use super::{Arc, Rc};
            struct Payload { owned: crate::types::Type, shared: std::sync::Arc<crate::types::Type> }
            struct BorrowedPayload { owned: crate::types::Type, borrowed: &'static crate::types::Type }
            struct Inherited { arc: Arc<Payload>, rc: Rc<Payload> }
            struct InheritedBorrowed(Arc<BorrowedPayload>);"#,
        ),
        (
            "src/facade.rs",
            "pub use crate::parent::{Arc as SharedArc, Rc as SharedRc};",
        ),
        (
            "src/user.rs",
            r#"use crate::facade::{SharedArc, SharedRc};
            use crate::facade as Wrappers;
            struct Reexported { arc: SharedArc<crate::parent::child::Payload>, rc: SharedRc<crate::parent::child::Payload> }
            struct ModuleAliased(Wrappers::SharedArc<crate::parent::child::Payload>);
            mod local {
                struct Arc<T>(T);
                struct Rc<T>(T);
                struct Local { arc: Arc<crate::types::Type>, rc: Rc<crate::types::Type> }
                struct Qualified(crate::user::local::Arc<crate::types::Type>);
            }"#,
        ),
    ];
    let fields = fields_from_sources(&sources);
    let modes = transitive_type_retention(&fields);
    for (source, carrier, expected) in [
        ("src/parent/child.rs", "Inherited", RetentionMode::Shared),
        (
            "src/parent/child.rs",
            "InheritedBorrowed",
            RetentionMode::Mixed,
        ),
        ("src/user.rs", "Reexported", RetentionMode::Shared),
        ("src/user.rs", "ModuleAliased", RetentionMode::Shared),
        ("src/user.rs", "local::Local", RetentionMode::Owned),
        ("src/user.rs", "local::Qualified", RetentionMode::Owned),
    ] {
        assert_eq!(
            modes.get(&CarrierId {
                source: source.to_owned(),
                name: carrier.to_owned()
            }),
            Some(&expected),
            "incorrect retention through exact wrapper route {source}::{carrier}",
        );
    }
}

#[test]
fn carrier_scanner_shared_wrapper_routes_preserve_lexical_type_shadowing_and_cycles() {
    let fields = parse_top_level_fields(
        "src/shadows.rs",
        r#"use std::sync::Arc;
        use std::rc::Rc;
        fn scope() {
            struct Arc<T>(T);
            struct Rc<T>(T);
            struct Local { arc: Arc<crate::types::Type>, rc: Rc<crate::types::Type> }
            {
                use std::sync::Arc;
                struct Inner(Arc<crate::types::Type>);
            }
        }"#,
    );
    let mut all = parse_top_level_fields("src/types.rs", "struct Type;");
    let inner = fields
        .iter()
        .find(|field| field.carrier.ends_with("::Inner"))
        .map(|field| CarrierId {
            source: field.source.clone(),
            name: field.carrier.clone(),
        })
        .expect("the deeper reimport fixture retains its exact local carrier");
    all.extend(fields);
    let modes = transitive_type_retention(&all);
    assert_eq!(modes.get(&inner), Some(&RetentionMode::Shared));
    assert_eq!(
        modes.get(&CarrierId {
            source: "src/shadows.rs".to_owned(),
            name: "$fn_scope::Local".to_owned(),
        }),
        Some(&RetentionMode::Owned),
        "local type declarations shadow the imported shared wrapper names",
    );
    assert!(
        std::panic::catch_unwind(|| parse_top_level_fields(
            "src/collision.rs",
            "use std::sync::Arc; struct Arc<T>(T); struct Ambiguous(Arc<crate::types::Type>);",
        ))
        .is_err(),
        "same-scope imported and declared type bindings must refuse ambiguity",
    );
    let roots = [
        (
            "src/lib.rs",
            "pub use crate as root; pub use std::sync::Arc; mod types; mod user;",
        ),
        ("src/types.rs", "struct Type;"),
        (
            "src/user.rs",
            "struct RootAlias(crate::root::root::root::Arc<crate::types::Type>);",
        ),
    ];
    let rooted = transitive_type_retention(&fields_from_sources(&roots));
    assert_eq!(
        rooted.get(&CarrierId {
            source: "src/user.rs".to_owned(),
            name: "RootAlias".to_owned()
        }),
        Some(&RetentionMode::Shared),
        "finite repeated root reexports consume the qualified suffix",
    );
    assert!(
        std::panic::catch_unwind(|| resolve_wrapper_import(
            "crate::cycle::Arc",
            &BTreeMap::from([("cycle".to_owned(), "crate::cycle::more".to_owned())]),
        ))
        .is_err(),
        "a growing repeated wrapper path must refuse rather than loop",
    );
    let cyclic = [
        ("src/lib.rs", "mod types; mod cycle;"),
        ("src/types.rs", "struct Type;"),
        (
            "src/cycle.rs",
            "use crate::cycle::B as A; use crate::cycle::A as B; struct Loop(A<crate::types::Type>);",
        ),
    ];
    assert!(
        std::panic::catch_unwind(|| transitive_type_retention(&fields_from_sources(&cyclic)))
            .is_err(),
        "exact wrapper-import cycles must fail closed",
    );
}

#[test]
fn carrier_scanner_restricted_visibility_preserves_module_attributes() {
    for visibility in [
        "pub(super)",
        "pub(crate)",
        "pub(self)",
        "pub(in crate)",
        "pub(in crate::parent)",
    ] {
        let parent = format!(
            r#"#[path = "storage.rs"] {visibility} mod selected;
            #[cfg(test)] #[path = "helper.rs"] {visibility} mod hidden;
            #[path = "helper.rs"] #[cfg(test)] {visibility} mod hidden_alias;
            struct Holder(selected::Retained);"#
        );
        let fields = fields_from_sources(&[
            ("src/lib.rs", "mod types; mod parent;"),
            ("src/types.rs", "pub struct Type;"),
            ("src/parent.rs", &parent),
            ("src/storage.rs", "pub struct Retained(crate::types::Type);"),
            ("src/helper.rs", "struct Hidden(crate::types::Type);"),
        ]);
        assert!(
            fields.iter().any(|field| field.source == "src/storage.rs"),
            "restricted-visible path module omitted for {visibility}"
        );
        assert!(
            !fields.iter().any(|field| field.source == "src/helper.rs"),
            "direct cfg(test) module became production for {visibility}"
        );
        assert_eq!(
            transitive_type_retention(&fields).get(&CarrierId {
                source: "src/parent.rs".to_owned(),
                name: "Holder".to_owned(),
            }),
            Some(&RetentionMode::Owned),
            "path module owner identity changed for {visibility}"
        );
    }

    let missing = [
        ("src/lib.rs", "mod parent;"),
        (
            "src/parent.rs",
            r#"#[path = "absent.rs"] pub(super) mod missing;"#,
        ),
    ];
    assert!(
        std::panic::catch_unwind(|| fields_from_sources(&missing)).is_err(),
        "a missing restricted-visible path module must still fail closed"
    );
}

#[test]
fn carrier_scanner_tuple_visibility_preserves_exact_type_references() {
    for visibility in [
        "pub(super)",
        "pub(crate)",
        "pub(self)",
        "pub(in crate)",
        "pub(in crate::parent)",
    ] {
        let source = format!(
            "struct Payload({visibility} Box<[crate::types::Type]>, \
             {visibility} *const crate::types::Type, \
             {visibility} std::sync::Arc<crate::types::Type>, \
             {visibility} (std::sync::Arc<crate::types::Type>, *const crate::types::Type));"
        );
        let fields = parse_top_level_fields("src/parent.rs", &source);
        assert_eq!(fields.len(), 4);
        for (field, (references, retention)) in fields.iter().zip([
            (&["Box", "crate::types::Type"][..], RetentionSet::owned()),
            (
                &["crate::types::Type"][..],
                RetentionSet(RetentionSet::BORROWED),
            ),
            (
                &["std::sync::Arc", "crate::types::Type"][..],
                RetentionSet(RetentionSet::SHARED),
            ),
            (
                &["std::sync::Arc", "crate::types::Type"][..],
                RetentionSet(RetentionSet::SHARED | RetentionSet::BORROWED),
            ),
        ]) {
            assert_eq!(
                field.references,
                references
                    .iter()
                    .map(|reference| (*reference).to_owned())
                    .collect(),
                "visibility became type evidence for {visibility} field {}",
                field.field,
            );
            assert_eq!(
                field.reference_retentions["crate::types::Type"], retention,
                "visibility changed retention for {visibility} field {}",
                field.field,
            );
        }
    }
}

#[test]
fn carrier_scanner_follows_path_modules_reexports_and_inherited_imports() {
    let sources = [
        (
            "src/lib.rs",
            r#"mod facade; mod types; mod namespace; pub use namespace::namespace; #[cfg(test)] #[path = "storage.rs"] mod test_storage;"#,
        ),
        ("src/types.rs", "struct Type;"),
        (
            "src/namespace.rs",
            "fn namespace() {} struct Value(crate::types::Type); struct Holder(crate::namespace::Value);",
        ),
        (
            "src/facade.rs",
            r#"#[path = "storage.rs"] mod implementation;
            pub use implementation::Staged as Published;
            struct Draft { staged: implementation::Staged }
            use self::implementation::Staged as Imported;
            use self::implementation as Storage;
            mod child { use super::implementation::Staged as Relative;
                struct Holder { inherited: Imported, relative: Relative,
                    module_alias: Storage::Staged,
                    qualified: crate::facade::implementation::Staged,
                    published: super::Published } }
            #[cfg(test)] #[path = "absent.rs"] mod absent_tests;
            #[cfg(test)] mod tests { #[path = "helper.rs"] mod helper; }"#,
        ),
        (
            "src/storage.rs",
            "struct Staged { owned: crate::types::Type, borrowed: &'static crate::types::Type }",
        ),
        (
            "src/facade/tests/helper.rs",
            "struct TestOnly(crate::types::Type);",
        ),
    ];
    let fields = fields_from_sources(&sources);
    assert!(
        !fields
            .iter()
            .any(|field| field.source == "src/facade/tests/helper.rs")
    );
    let modes = transitive_type_retention(&fields);
    for (source, name) in [
        ("src/facade.rs", "Draft"),
        ("src/facade.rs", "Published"),
        ("src/facade.rs", "child::Holder"),
        ("src/storage.rs", "Staged"),
    ] {
        assert_eq!(
            modes.get(&CarrierId {
                source: source.to_owned(),
                name: name.to_owned()
            }),
            Some(&RetentionMode::Mixed),
            "unreached path module carrier {source}::{name}"
        );
    }
    assert_eq!(
        modes.get(&CarrierId {
            source: "src/namespace.rs".to_owned(),
            name: "Holder".to_owned()
        }),
        Some(&RetentionMode::Owned)
    );
    let conflicting = [
        (
            "src/lib.rs",
            "#[path = \"a.rs\"] mod same; #[path = \"b.rs\"] mod same;",
        ),
        ("src/a.rs", "struct A;"),
        ("src/b.rs", "struct B;"),
    ];
    assert!(
        std::panic::catch_unwind(|| fields_from_sources(&conflicting)).is_err(),
        "conflicting lexical module identities must fail closed"
    );
}

#[test]
fn carrier_scanner_module_value_reexports_preserve_generic_type_and_wrapper_paths() {
    let sources = [
        ("src/lib.rs", "mod types; mod core; mod facade; mod user;"),
        ("src/types.rs", "struct Type;"),
        (
            "src/core/mod.rs",
            r#"pub mod validate;
            pub use validate::{validate, Layouts};
            pub struct Local<'a>(validate::Layouts<'a>);
            pub struct SharedLocal(validate::Arc<crate::core::validate::Owned>);
            pub mod inline {
                pub mod inspect {
                    pub fn inspect() {}
                    pub struct View<'a>(&'a crate::types::Type);
                }
                pub use inspect::inspect;
                pub struct Local<'a>(inspect::View<'a>);
            }"#,
        ),
        (
            "src/core/validate.rs",
            r#"pub fn validate() {}
            pub struct Layouts<'a>(&'a crate::types::Type);
            pub struct Owned(crate::types::Type);
            pub use std::sync::Arc;"#,
        ),
        ("src/facade.rs", "pub use crate::core as Core;"),
        (
            "src/user.rs",
            r#"use crate::core::validate as Validation;
            use crate::core::Layouts as LayoutAlias;
            struct Direct(crate::core::validate::Layouts<'static>);
            struct Reexported(LayoutAlias<'static>);
            struct ModuleAliased(Validation::Layouts<'static>);
            struct Facade(crate::facade::Core::validate::Layouts<'static>);
            struct Inline(crate::core::inline::inspect::View<'static>);
            struct Shared(crate::facade::Core::validate::Arc<crate::core::validate::Owned>);"#,
        ),
    ];
    let fields = fields_from_sources(&sources);
    let declarations = declaration_index(&fields);
    assert!(
        !fields
            .iter()
            .any(|field| field.source == "src/facade.rs" && field.carrier == "Core"),
        "an exported module alias has no synthesized type-carrier row"
    );
    assert_eq!(
        declarations.imports.get("facade::Core").map(String::as_str),
        Some("crate::core"),
        "the genuine uppercase module alias still supplies qualified paths",
    );
    assert!(
        fields.iter().any(|field| field.source == "src/core/mod.rs"
            && field.carrier == "Layouts"
            && field.field == "$alias"),
        "the genuine exported type alias remains a physical inventory row"
    );
    assert!(!declarations.imports.contains_key("core::validate"));
    assert!(!declarations.imports.contains_key("core::inline::inspect"));
    assert_eq!(
        declarations
            .imports
            .get("user::Validation")
            .map(String::as_str),
        Some("crate::core::validate"),
        "genuine imported module aliases remain available",
    );
    let owners = transitive_type_owners(&fields);
    let modes = transitive_type_retention(&fields);
    for (carrier, alias, target) in [
        ("Local", "validate", "crate::core::validate"),
        ("inline::Local", "inspect", "crate::core::inline::inspect"),
    ] {
        let field = fields
            .iter()
            .find(|field| {
                field.source == "src/core/mod.rs" && field.carrier == carrier && field.field == "0"
            })
            .expect("the local borrowed loan field remains in the inventory");
        assert_eq!(field.aliases.get(alias).map(String::as_str), Some(target));
        let owner = CarrierId {
            source: field.source.clone(),
            name: field.carrier.clone(),
        };
        assert!(owners.contains(&owner));
        assert_eq!(modes.get(&owner), Some(&RetentionMode::Borrowed));
    }
    let shared_local = CarrierId {
        source: "src/core/mod.rs".to_owned(),
        name: "SharedLocal".to_owned(),
    };
    assert!(owners.contains(&shared_local));
    assert_eq!(modes.get(&shared_local), Some(&RetentionMode::Shared));
    for (carrier, expected) in [
        ("Direct", RetentionMode::Borrowed),
        ("Reexported", RetentionMode::Borrowed),
        ("ModuleAliased", RetentionMode::Borrowed),
        ("Facade", RetentionMode::Borrowed),
        ("Inline", RetentionMode::Borrowed),
        ("Shared", RetentionMode::Shared),
    ] {
        let owner = CarrierId {
            source: "src/user.rs".to_owned(),
            name: carrier.to_owned(),
        };
        assert!(
            owners.contains(&owner),
            "the type carrier {carrier} remains inventoried"
        );
        assert_eq!(
            modes.get(&owner),
            Some(&expected),
            "incorrect retention for {carrier}"
        );
    }
}

#[test]
fn carrier_scanner_cfg_attr_external_modules_remain_production() {
    let sources = [
        (
            "src/lib.rs",
            r#"mod types;
            #[cfg_attr(test, cfg(test))] mod child;
            #[allow(dead_code)] #[cfg_attr(test, cfg(test))] mod stacked;
            #[cfg_attr(test, cfg(test))] #[allow(dead_code)] mod reversed;
            #[allow(dead_code)] #[cfg(test)] #[cfg_attr(test, cfg(test))] mod test_only;
            #[cfg(test)] #[path = "child.rs"] mod test_route;"#,
        ),
        ("src/types.rs", "struct Type;"),
        ("src/child.rs", "struct Child(crate::types::Type);"),
        ("src/stacked.rs", "struct Stacked(crate::types::Type);"),
        ("src/reversed.rs", "struct Reversed(crate::types::Type);"),
        ("src/test_only.rs", "struct TestOnly(crate::types::Type);"),
    ];
    let fields = fields_from_sources(&sources);
    let modes = transitive_type_retention(&fields);
    for (source, carrier) in [
        ("src/child.rs", "Child"),
        ("src/stacked.rs", "Stacked"),
        ("src/reversed.rs", "Reversed"),
    ] {
        assert_eq!(
            modes.get(&CarrierId {
                source: source.to_owned(),
                name: carrier.to_owned(),
            }),
            Some(&RetentionMode::Owned),
            "cfg_attr production route omitted {source}::{carrier}"
        );
    }
    assert!(
        !fields
            .iter()
            .any(|field| field.source == "src/test_only.rs")
    );
}

#[test]
fn carrier_scanner_cfg_attr_inline_modules_remain_production() {
    let sources = [
        ("src/types.rs", "struct Type;"),
        (
            "src/lib.rs",
            r#"mod types;
            #[cfg_attr(test, cfg(test))] mod child {
                struct Child(crate::types::Type);
                #[allow(dead_code)] #[cfg_attr(test, cfg(test))] mod stacked {
                    struct Stacked(crate::types::Type);
                }
            }
            #[cfg_attr(test, cfg(test))] #[allow(dead_code)] mod reversed {
                struct Reversed(crate::types::Type);
            }
            #[cfg_attr(test, cfg(test))] #[cfg(test)] mod test_only {
                struct TestOnly(crate::types::Type);
            }"#,
        ),
    ];
    let fields = fields_from_sources(&sources);
    let modes = transitive_type_retention(&fields);
    for carrier in [
        "child::Child",
        "child::stacked::Stacked",
        "reversed::Reversed",
    ] {
        assert_eq!(
            modes.get(&CarrierId {
                source: "src/lib.rs".to_owned(),
                name: carrier.to_owned(),
            }),
            Some(&RetentionMode::Owned),
            "cfg_attr production inline carrier omitted {carrier}"
        );
    }
    assert!(
        !fields
            .iter()
            .any(|field| field.carrier == "test_only::TestOnly")
    );
}

#[test]
fn carrier_scanner_alias_seed_retention_uses_canonical_targets() {
    let sources = [
        ("src/lib.rs", "mod types; mod facade; mod aliases;"),
        ("src/types.rs", "struct Type;"),
        (
            "src/facade.rs",
            "pub use crate::types::Type as Published; struct Anchor;",
        ),
        (
            "src/aliases.rs",
            r#"use crate::types::Type as Payload;
            use crate::types as TypeModule;
            use crate::facade::Published as Renamed;
            struct Direct(Payload);
            struct SelfQualified(self::Payload);
            struct Borrowed<'a>(&'a Payload);
            struct Shared(std::sync::Arc<Payload>);
            struct Mixed<'a> { pair: (Payload, &'a self::Payload) }
            struct ModuleQualified(TypeModule::Type);
            struct Reexport(crate::facade::Published);
            struct Reimport(Renamed);
            mod child {
                struct Parent(super::Payload);
                struct ParentBorrowed<'a>(&'a super::Payload);
            }"#,
        ),
    ];
    let modes = transitive_type_retention(&fields_from_sources(&sources));
    for (carrier, expected) in [
        ("Direct", RetentionMode::Owned),
        ("SelfQualified", RetentionMode::Owned),
        ("Borrowed", RetentionMode::Borrowed),
        ("Shared", RetentionMode::Shared),
        ("Mixed", RetentionMode::Mixed),
        ("ModuleQualified", RetentionMode::Owned),
        ("Reexport", RetentionMode::Owned),
        ("Reimport", RetentionMode::Owned),
        ("child::Parent", RetentionMode::Owned),
        ("child::ParentBorrowed", RetentionMode::Borrowed),
    ] {
        assert_eq!(
            modes.get(&CarrierId {
                source: "src/aliases.rs".to_owned(),
                name: carrier.to_owned(),
            }),
            Some(&expected),
            "alias target retention omitted or changed for {carrier}"
        );
    }
}

#[test]
fn carrier_scanner_alias_seed_retention_preserves_nonowners_and_glob_refusal() {
    let sources = [
        ("src/lib.rs", "mod types; mod plain; mod controls;"),
        ("src/types.rs", "struct Type;"),
        ("src/plain.rs", "struct Type;"),
        (
            "src/controls.rs",
            r#"use crate::plain::Type as PlainPayload;
            use external::Unmodeled as ExternalPayload;
            struct Plain(PlainPayload);
            struct External(ExternalPayload);
            struct Unknown(Unmodeled);
            struct Generic<T>(T);
            mod shadow {
                struct Type;
                struct Local(Type);
            }"#,
        ),
    ];
    let modes = transitive_type_retention(&fields_from_sources(&sources));
    for carrier in ["Plain", "External", "Unknown", "Generic", "shadow::Local"] {
        assert!(
            !modes.contains_key(&CarrierId {
                source: "src/controls.rs".to_owned(),
                name: carrier.to_owned(),
            }),
            "nonowner incorrectly retained Type through {carrier}"
        );
    }
    let glob = [
        ("src/lib.rs", "mod types; mod selected;"),
        ("src/types.rs", "struct Type;"),
        (
            "src/selected.rs",
            "use crate::types::*; struct Selected(Type);",
        ),
    ];
    assert!(
        std::panic::catch_unwind(|| transitive_type_retention(&fields_from_sources(&glob)))
            .is_err(),
        "unresolved glob selection must retain its existing refusal"
    );
}

#[derive(Clone, Debug)]
struct SourceModuleEdge {
    source: String,
    inline_prefix: String,
    name: String,
    target: String,
    test_only: bool,
}

#[test]
fn production_source_selection_follows_module_declarations_instead_of_filenames() {
    static NEXT_ID: AtomicU64 = AtomicU64::new(0);
    let directory = std::env::temp_dir().join(format!(
        "ash-source-selection-{}-{}",
        std::process::id(),
        NEXT_ID.fetch_add(1, Ordering::Relaxed)
    ));
    let root = directory.join("src");
    fs::create_dir_all(&root).unwrap();
    for (name, source) in [
        (
            "lib.rs",
            "mod types; #[path = \"production_tests.rs\"] mod production; #[cfg(test)] mod helper;",
        ),
        ("types.rs", "struct Type;"),
        (
            "production_tests.rs",
            "struct Production(crate::types::Type);",
        ),
        ("helper.rs", "struct TestOnly(crate::types::Type);"),
    ] {
        fs::write(root.join(name), source).unwrap();
    }
    let mut paths = Vec::new();
    collect_production_rust_sources(&root, &mut paths);
    let sources = paths
        .iter()
        .map(|path| {
            (
                path.strip_prefix(&directory)
                    .unwrap()
                    .to_string_lossy()
                    .into_owned(),
                fs::read_to_string(path).unwrap(),
            )
        })
        .collect::<Vec<_>>();
    let fields = fields_from_sources(
        &sources
            .iter()
            .map(|(path, source)| (path.as_str(), source.as_str()))
            .collect::<Vec<_>>(),
    );
    assert!(fields.iter().any(|field| field.source == "src/production_tests.rs" && field.carrier == "Production"));
    assert!(!fields.iter().any(|field| field.source == "src/helper.rs"));
    fs::remove_dir_all(directory).unwrap();
}

fn source_module_identities(sources: &[(&str, &str)]) -> BTreeMap<String, String> {
    #[expect(
        clippy::too_many_arguments,
        reason = "module resolution tracks physical and lexical directories with inherited test state"
    )]
    fn collect(
        source: &str,
        tokens: &[&str],
        inline_prefix: &str,
        module_directory: &Path,
        attribute_directory: &Path,
        available: &BTreeSet<&str>,
        edges: &mut Vec<SourceModuleEdge>,
        inherited_test: bool,
    ) {
        let mut cursor = 0;
        while cursor < tokens.len() {
            if tokens[cursor] == "mod" {
                let name = tokens[cursor + 1];
                let delimiter = cursor + 2;
                let test_only = inherited_test || has_direct_cfg_test_attribute(tokens, cursor);
                if tokens[delimiter] == "{" {
                    let close = matching_token(tokens, delimiter, "{", "}");
                    let nested = module_directory.join(name);
                    collect(
                        source,
                        &tokens[delimiter + 1..close],
                        &qualify_declaration(inline_prefix, name),
                        &nested,
                        &nested,
                        available,
                        edges,
                        test_only,
                    );
                    cursor = close + 1;
                    continue;
                }
                assert_eq!(
                    tokens[delimiter], ";",
                    "unsupported module declaration in {source}"
                );
                let attributes = direct_attribute_tokens(tokens, cursor);
                let explicit_path = attributes.windows(3).find_map(|window| {
                    (window[0] == "path" && window[1] == "=").then(|| {
                        window[2]
                            .strip_prefix('"')
                            .and_then(|path| path.strip_suffix('"'))
                            .expect("module path must be a plain string literal")
                    })
                });
                let target = if let Some(path) = explicit_path {
                    attribute_directory.join(path)
                } else {
                    let flat = module_directory.join(format!("{name}.rs"));
                    let directory = module_directory.join(name).join("mod.rs");
                    assert!(
                        !(available.contains(flat.to_str().unwrap())
                            && available.contains(directory.to_str().unwrap())),
                        "ambiguous source files for module {source}::{name}"
                    );
                    if available.contains(flat.to_str().unwrap()) {
                        flat
                    } else {
                        directory
                    }
                };
                let target = target.to_string_lossy().replace('\\', "/");
                if test_only && !available.contains(target.as_str()) {
                    cursor = delimiter + 1;
                    continue;
                }
                assert!(
                    available.contains(target.as_str()),
                    "module source {target} is absent from the closed source scan"
                );
                edges.push(SourceModuleEdge {
                    source: source.to_owned(),
                    inline_prefix: inline_prefix.to_owned(),
                    name: name.to_owned(),
                    target,
                    test_only,
                });
                cursor = delimiter + 1;
            } else if tokens[cursor] == "{" {
                cursor = matching_token(tokens, cursor, "{", "}") + 1;
            } else {
                cursor += 1;
            }
        }
    }
    let available = sources
        .iter()
        .map(|(path, _)| *path)
        .collect::<BTreeSet<_>>();
    let mut edges = Vec::new();
    for (source, text) in sources {
        let path = Path::new(source);
        let parent = path.parent().unwrap();
        let module_directory = if matches!(
            path.file_name().and_then(|name| name.to_str()),
            Some("lib.rs" | "main.rs" | "mod.rs")
        ) {
            parent.to_path_buf()
        } else {
            parent.join(path.file_stem().unwrap())
        };
        collect(
            source,
            &rust_tokens_with_literals(text, true),
            "",
            &module_directory,
            parent,
            &available,
            &mut edges,
            false,
        );
    }
    let mut declared = BTreeMap::new();
    for edge in &edges {
        let key = (&edge.source, &edge.inline_prefix, &edge.name);
        assert!(
            declared.insert(key, &edge.target).is_none(),
            "duplicate lexical module declaration {key:?}"
        );
    }
    let incoming = edges
        .iter()
        .map(|edge| edge.target.as_str())
        .collect::<BTreeSet<_>>();
    let mut production_sources = sources
        .iter()
        .filter(|(path, _)| {
            !incoming.contains(path) || matches!(*path, "src/lib.rs" | "src/main.rs")
        })
        .map(|(path, _)| (*path).to_owned())
        .collect::<BTreeSet<_>>();
    loop {
        let previous = production_sources.len();
        let reached = edges
            .iter()
            .filter(|edge| !edge.test_only && production_sources.contains(&edge.source))
            .map(|edge| edge.target.clone())
            .collect::<Vec<_>>();
        production_sources.extend(reached);
        if production_sources.len() == previous {
            break;
        }
    }
    let mut modules = sources
        .iter()
        .map(|(path, _)| ((*path).to_owned(), default_source_module(path)))
        .collect::<BTreeMap<_, _>>();
    for _ in 0..=sources.len() {
        let mut next = modules.clone();
        let mut assigned = BTreeMap::new();
        for edge in edges
            .iter()
            .filter(|edge| !edge.test_only && production_sources.contains(&edge.source))
        {
            let identity = qualify_declaration(
                &qualify_declaration(&modules[&edge.source], &edge.inline_prefix),
                &edge.name,
            );
            if let Some(previous) = assigned.insert(edge.target.clone(), identity.clone()) {
                assert_eq!(
                    previous, identity,
                    "source belongs to multiple lexical modules"
                );
            }
            next.insert(edge.target.clone(), identity);
        }
        let mut reverse = BTreeMap::new();
        for (source, module) in &next {
            if let Some(previous) = reverse.insert(module, source) {
                assert_eq!(previous, source, "lexical module has multiple source files");
            }
        }
        if next == modules {
            let mut test_sources = edges
                .iter()
                .filter(|edge| edge.test_only)
                .map(|edge| edge.target.clone())
                .collect::<BTreeSet<_>>();
            loop {
                let previous = test_sources.len();
                let inherited = edges
                    .iter()
                    .filter(|edge| test_sources.contains(&edge.source))
                    .map(|edge| edge.target.clone())
                    .collect::<Vec<_>>();
                test_sources.extend(inherited);
                if test_sources.len() == previous {
                    break;
                }
            }
            modules.retain(|source, _| {
                !test_sources.contains(source) || production_sources.contains(source)
            });
            return modules;
        }
        modules = next;
    }
    panic!("cyclic source module relationships do not reach a fixed point")
}

fn fields_from_sources(sources: &[(&str, &str)]) -> Vec<ProductionField> {
    let modules = source_module_identities(sources);
    let mut declared_modules = BTreeSet::new();
    let mut imports = BTreeMap::new();
    for (path, source) in sources {
        let Some(module) = modules.get(*path) else {
            continue;
        };
        let tokens = production_rust_code_tokens(source);
        declared_modules.extend(declared_module_paths(&tokens, module));
        for (binding, target) in module_import_bindings(&tokens, module) {
            if let Some(previous) = imports.insert(binding.clone(), target.clone()) {
                assert_eq!(previous, target, "conflicting module import {binding}");
            }
        }
    }
    let mut fields = sources
        .iter()
        .filter_map(|(path, source)| {
            modules.get(*path).map(|module| {
                parse_fields_in_module(path, source, module, &imports, &declared_modules)
            })
        })
        .flatten()
        .collect::<Vec<_>>();
    // Namespace-only sources may have no stored type fields. Retain the closed
    // scan's genuine namespace metadata without synthesizing a type carrier.
    if let Some(field) = fields.first_mut() {
        field.module_imports.extend(imports);
        field.module_declarations.extend(declared_modules);
    }
    fields
}

#[test]
fn imported_catalog_authentication_has_an_exact_compile_time_inventory() {
    let helper = "same_imported_method_evidence_catalog";
    for path in [
        "src/core/dialect.rs",
        "src/core/validate.rs",
        "src/core/transform.rs",
        "src/core/provider.rs",
        "src/core/provider/handler.rs",
        "src/eval/machine.rs",
    ] {
        assert!(!is_allowed_private_core_method_evidence_identifier(
            path, helper
        ));
    }
    for identifier in [
        "same_imported_method_evidence_catalog_unchecked",
        "provider_method_dispatch",
        "ProviderInterfaceRuntime",
        "interface_dispatch",
    ] {
        assert!(!is_allowed_private_core_method_evidence_identifier(
            "src/core/provider/external.rs",
            identifier
        ));
    }
}

fn production_fields() -> Vec<ProductionField> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut sources = Vec::new();
    collect_production_rust_sources(&root, &mut sources);
    sources.sort();
    let sources = sources
        .into_iter()
        .map(|path| {
            let relative = path
                .strip_prefix(env!("CARGO_MANIFEST_DIR"))
                .unwrap()
                .to_string_lossy()
                .replace('\\', "/");
            (
                relative,
                fs::read_to_string(path).expect("production Rust source should be readable"),
            )
        })
        .collect::<Vec<_>>();
    fields_from_sources(
        &sources
            .iter()
            .map(|(path, source)| (path.as_str(), source.as_str()))
            .collect::<Vec<_>>(),
    )
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
        } else if path.extension().is_some_and(|extension| extension == "rs") {
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

// Membership sets belong to one immutable retention fixed-point snapshot.
struct RetentionMembership {
    by_mode: [BTreeSet<CarrierId>; 3],
}

impl RetentionMembership {
    fn new(carrier_modes: &BTreeMap<CarrierId, RetentionSet>) -> Self {
        Self {
            by_mode: [
                RetentionSet::OWNED,
                RetentionSet::SHARED,
                RetentionSet::BORROWED,
            ]
            .map(|bit| {
                carrier_modes
                    .iter()
                    .filter_map(|(carrier, mode)| (mode.0 & bit != 0).then_some(carrier.clone()))
                    .collect()
            }),
        }
    }
}

fn field_type_retention(
    field: &ProductionField,
    declarations: &DeclarationIndex,
    membership: &RetentionMembership,
) -> Option<RetentionMode> {
    field_type_retention_set(field, declarations, membership).map(RetentionSet::collapse)
}

fn field_type_retention_set(
    field: &ProductionField,
    declarations: &DeclarationIndex,
    membership: &RetentionMembership,
) -> Option<RetentionSet> {
    let mut result = None;
    for reference in &field.references {
        let generic_carrier = generic_type_carrier(reference, &field.aliases);
        let mut referenced = RetentionSet::owned();
        if !generic_carrier {
            referenced = RetentionSet(0);
            for (bit, owners) in [
                RetentionSet::OWNED,
                RetentionSet::SHARED,
                RetentionSet::BORROWED,
            ]
            .into_iter()
            .zip(&membership.by_mode)
            {
                if reference_reaches_owner_with_aliases(
                    &field.source,
                    &field.carrier,
                    reference,
                    &field.aliases,
                    declarations,
                    owners,
                ) {
                    referenced.0 |= bit;
                }
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

fn generic_type_carrier(reference: &str, aliases: &BTreeMap<String, String>) -> bool {
    reference.split_once("::").is_some_and(|(prefix, suffix)| {
        aliases
            .get(prefix)
            .is_some_and(|target| target == "$generic")
            && matches!(suffix, "Effects" | "Kind" | "Operation")
    })
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
        let membership = RetentionMembership::new(&modes);
        let mut discovered = BTreeMap::<CarrierId, RetentionSet>::new();
        for field in fields {
            let Some(retention) = field_type_retention_set(field, &declarations, &membership)
            else {
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

#[derive(Default)]
struct DeclarationIndex {
    by_name: BTreeMap<String, Vec<CarrierId>>,
    modules: BTreeMap<String, String>,
    imports: BTreeMap<String, String>,
}

impl std::ops::Deref for DeclarationIndex {
    type Target = BTreeMap<String, Vec<CarrierId>>;
    fn deref(&self) -> &Self::Target {
        &self.by_name
    }
}

impl From<BTreeMap<String, Vec<CarrierId>>> for DeclarationIndex {
    fn from(by_name: BTreeMap<String, Vec<CarrierId>>) -> Self {
        Self {
            by_name,
            modules: BTreeMap::new(),
            imports: BTreeMap::new(),
        }
    }
}

fn declaration_index(fields: &[ProductionField]) -> DeclarationIndex {
    let by_name = fields.iter().fold(
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
    );
    let mut modules = BTreeMap::new();
    for field in fields {
        if let Some(previous) = modules.insert(field.source.clone(), field.module.clone()) {
            assert_eq!(previous, field.module, "conflicting source module identity");
        }
    }
    let mut imports = BTreeMap::new();
    for field in fields {
        for (binding, target) in &field.module_imports {
            if let Some(previous) = imports.insert(binding.clone(), target.clone()) {
                assert_eq!(previous, *target, "conflicting module import {binding}");
            }
        }
    }
    // Rust keeps module/type bindings separate from value reexports. For
    // example, core::validate is a module even though core reexports a value
    // named validate from that module. Only module aliases can prefix types.
    let mut module_paths = modules.values().cloned().collect::<BTreeSet<_>>();
    for field in fields {
        module_paths.extend(field.module_declarations.iter().cloned());
        let mut prefix = field.module.clone();
        for segment in field
            .carrier
            .split("::")
            .take(field.carrier.matches("::").count())
        {
            if segment.starts_with('$') {
                break;
            }
            prefix = qualify_declaration(&prefix, segment);
            module_paths.insert(prefix.clone());
        }
    }
    loop {
        let previous = module_paths.len();
        let discovered = imports
            .iter()
            .filter_map(|(binding, target)| {
                let target = if target == "crate" {
                    ""
                } else {
                    target.strip_prefix("crate::").unwrap_or(target)
                };
                module_paths.contains(target).then(|| binding.clone())
            })
            .collect::<Vec<_>>();
        module_paths.extend(discovered);
        if module_paths.len() == previous {
            break;
        }
    }
    imports.retain(|binding, target| {
        binding.rsplit("::").next().unwrap().as_bytes()[0].is_ascii_uppercase()
            || module_paths.contains(if target == "crate" {
                ""
            } else {
                target.strip_prefix("crate::").unwrap_or(target)
            })
            || matches!(target.split("::").next(), Some("std" | "alloc" | "core"))
    });
    DeclarationIndex {
        by_name,
        modules,
        imports,
    }
}

fn reference_reaches_owner(
    source: &str,
    carrier: &str,
    reference: &str,
    declarations: &DeclarationIndex,
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
    declarations: &DeclarationIndex,
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
        declarations: &DeclarationIndex,
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
            if target == "$generic" {
                return generic_type_carrier(reference, aliases);
            }
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
        let absolute = qualified_reference_crate_path(
            &module_source(current, declarations),
            &current.name,
            reference,
        )
        .or_else(|| {
            reference.contains("::").then(|| {
                qualified_reference_crate_path(
                    &module_source(current, declarations),
                    &current.name,
                    &format!("self::{reference}"),
                )
                .unwrap()
            })
        });
        if let Some(absolute) = absolute {
            let segments = absolute.split("::").collect::<Vec<_>>();
            for prefix_length in (1..=segments.len()).rev() {
                let binding = segments[..prefix_length].join("::");
                if let Some(target) = declarations.imports.get(&binding) {
                    record_module_import_progress(
                        &binding,
                        segments.len() - prefix_length,
                        visited,
                    );
                    let expanded = if prefix_length == segments.len() {
                        target.clone()
                    } else {
                        format!("{target}::{}", segments[prefix_length..].join("::"))
                    };
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
            }
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
                "a visible glob import can bind unresolved carrier reference {reference} from {}::{}",
                current.source,
                current.name,
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
                &module_source(current, declarations),
                &current.name,
                &format!("self::{reference}"),
            )
            .expect("a self-qualified path is crate-relative");
            let exact = candidates
                .iter()
                .filter(|candidate| {
                    let path = carrier_crate_path(candidate, declarations);
                    path == relative || path == reference
                })
                .collect::<Vec<_>>();
            return if exact.is_empty() {
                false
            } else {
                resolved_ownership(&exact, owners)
            };
        }
        if let Some(expected) = qualified_reference_crate_path(
            &module_source(current, declarations),
            &current.name,
            reference,
        ) {
            let exact = candidates
                .iter()
                .filter(|candidate| carrier_crate_path(candidate, declarations) == expected)
                .collect::<Vec<_>>();
            if !exact.is_empty() {
                return resolved_ownership(&exact, owners);
            }
            assert!(
                !exact.is_empty(),
                "qualified carrier reference {reference} does not resolve to {expected}: paths={:?}; modules={:?}",
                candidates
                    .iter()
                    .map(|candidate| carrier_crate_path(candidate, declarations))
                    .collect::<Vec<_>>(),
                declarations.modules
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
            "a visible glob import can bind ambiguous carrier reference {reference} from {}::{}",
            current.source,
            current.name,
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

fn default_source_module(source: &str) -> String {
    let source = source.strip_prefix("src/").unwrap_or(source);
    let module = source
        .strip_suffix("/mod.rs")
        .or_else(|| source.strip_suffix(".rs"))
        .unwrap_or(source);
    if module == "lib" {
        String::new()
    } else {
        module.replace('/', "::")
    }
}

fn module_source(carrier: &CarrierId, declarations: &DeclarationIndex) -> String {
    let module = declarations
        .modules
        .get(&carrier.source)
        .cloned()
        .unwrap_or_else(|| default_source_module(&carrier.source));
    format!(
        "src/{}.rs",
        if module.is_empty() {
            "lib".to_owned()
        } else {
            module.replace("::", "/")
        }
    )
}

fn carrier_crate_path(carrier: &CarrierId, declarations: &DeclarationIndex) -> String {
    let module = declarations
        .modules
        .get(&carrier.source)
        .cloned()
        .unwrap_or_else(|| default_source_module(&carrier.source));
    qualify_declaration(&module, &carrier.name)
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

    let candidates: DeclarationIndex = BTreeMap::from([(
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
    )])
    .into();
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
    let uniformly_owned: DeclarationIndex = BTreeMap::from([(
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
    )])
    .into();
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
    let uniformly_plain: DeclarationIndex = BTreeMap::from([(
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
    )])
    .into();
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

    let inline_candidates: DeclarationIndex = BTreeMap::from([(
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
    )])
    .into();
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

#[test]
fn carrier_scanner_distinguishes_precise_captures_from_imports() {
    let fields = parse_top_level_fields(
        "src/lib.rs",
        r#"
        mod types { struct Type; }
        use crate::{types::Type as RootType};
        struct Before { ty: RootType }
        fn values<'a>(value: &'a RootType) -> impl Iterator<Item = &'a RootType> + use<'a> {
            use crate::types::Type as LocalType;
            struct Local { ty: LocalType }
            let _ = 0;
            std::iter::once(value)
        }
        use crate::types::Type as AfterType;
        struct After { ty: AfterType }
        "#,
    );
    let declarations = declaration_index(&fields);
    let owners = BTreeSet::from([CarrierId {
        source: "src/lib.rs".to_owned(),
        name: "types::Type".to_owned(),
    }]);
    let typed = fields
        .iter()
        .filter(|field| field.field == "ty")
        .collect::<Vec<_>>();
    assert_eq!(typed.len(), 3);
    for field in typed {
        let reference = field
            .references
            .first()
            .expect("the type alias must remain visible");
        assert_eq!(field.references.len(), 1);
        assert_eq!(
            resolve_import_alias(reference, &field.aliases),
            "crate::types::Type"
        );
        assert!(reference_reaches_owner_with_aliases(
            &field.source,
            &field.carrier,
            reference,
            &field.aliases,
            &declarations,
            &owners,
        ));
    }
}

fn parse_top_level_fields(path: &str, source: &str) -> Vec<ProductionField> {
    let module = default_source_module(path);
    let declared_modules = declared_module_paths(&production_rust_code_tokens(source), &module);
    parse_fields_in_module(path, source, &module, &BTreeMap::new(), &declared_modules)
}

fn declared_module_paths(tokens: &[&str], module: &str) -> BTreeSet<String> {
    let mut modules = BTreeSet::from([module.to_owned()]);
    let mut cursor = 0;
    while cursor < tokens.len() {
        if tokens[cursor] == "mod" {
            let nested = qualify_declaration(module, tokens[cursor + 1]);
            let delimiter = cursor + 2;
            assert!(
                matches!(tokens[delimiter], "{" | ";"),
                "unsupported module declaration"
            );
            let production = !has_direct_cfg_test_attribute(tokens, cursor);
            if production {
                modules.insert(nested.clone());
            }
            if tokens[delimiter] == "{" {
                let close = matching_token(tokens, delimiter, "{", "}");
                if production {
                    modules.extend(declared_module_paths(
                        &tokens[delimiter + 1..close],
                        &nested,
                    ));
                }
                cursor = close + 1;
            } else {
                cursor = delimiter + 1;
            }
        } else if tokens[cursor] == "{" {
            cursor = matching_token(tokens, cursor, "{", "}") + 1;
        } else {
            cursor += 1;
        }
    }
    modules
}

fn parse_fields_in_module(
    path: &str,
    source: &str,
    module: &str,
    wrapper_imports: &BTreeMap<String, String>,
    declared_modules: &BTreeSet<String>,
) -> Vec<ProductionField> {
    let tokens = production_rust_code_tokens(source);
    let module_imports = module_import_bindings(&tokens, module);
    let mut imports = wrapper_imports.clone();
    for (binding, target) in &module_imports {
        if let Some(previous) = imports.insert(binding.clone(), target.clone()) {
            assert_eq!(previous, *target, "conflicting module import {binding}");
        }
    }
    let mut fields =
        parse_declaration_fields(path, &tokens, "", module, &BTreeMap::new(), &imports);
    // Exported imports of modules supply qualified paths, not stored type
    // aliases. Keep their import metadata while omitting the synthesized row.
    fields.retain(|field| {
        if field.field != "$alias" {
            return true;
        }
        let binding = qualify_declaration(module, &field.carrier);
        let Some(target) = imports.get(&binding) else {
            return true;
        };
        if !field.references.contains(target) {
            return true;
        }
        let target = resolve_wrapper_import(target, &imports);
        let module = if target == "crate" {
            Some("")
        } else {
            target.strip_prefix("crate::")
        };
        !module.is_some_and(|module| declared_modules.contains(module))
    });
    for field in &mut fields {
        field.module = module.to_owned();
        field.module_imports = module_imports.clone();
    }
    if let Some(field) = fields.first_mut() {
        field
            .module_declarations
            .extend(declared_module_paths(&tokens, module));
    }
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

fn anchored_import_target(tokens: &[&str], module: &str, target: &str) -> String {
    let synthetic_source = format!(
        "src/{}.rs",
        if module.is_empty() {
            "lib".to_owned()
        } else {
            module.replace("::", "/")
        }
    );
    if let Some(absolute) = qualified_reference_crate_path(&synthetic_source, "", target) {
        return format!("crate::{absolute}");
    }
    let prefix = target.split("::").next().unwrap();
    let scopes = token_scope_paths(tokens);
    let declared_local = tokens.windows(2).enumerate().any(|(index, window)| {
        scopes[index].is_empty()
            && matches!(window[0], "mod" | "struct" | "enum" | "type")
            && window[1] == prefix
    });
    if declared_local {
        format!("crate::{}", qualify_declaration(module, target))
    } else {
        target.to_owned()
    }
}

fn module_import_bindings(tokens: &[&str], module: &str) -> BTreeMap<String, String> {
    let scopes = token_scope_paths(tokens);
    let mut bindings = BTreeMap::new();
    for imported in scoped_import_aliases(tokens, &scopes)
        .into_iter()
        .filter(|imported| imported.scope.is_empty() && imported.alias != "*")
    {
        let target = anchored_import_target(tokens, module, &imported.target);
        let binding = qualify_declaration(module, &imported.alias);
        if let Some(previous) = bindings.insert(binding.clone(), target.clone()) {
            assert_eq!(previous, target, "conflicting module import {binding}");
        }
    }
    // A declared module occupies the type namespace. A same-named value
    // reexport (for example, `mod validate; use validate::validate;`) cannot
    // replace that module when resolving a qualified type or wrapper path.
    for (index, declaration) in tokens.windows(3).enumerate() {
        if declaration[0] == "mod"
            && scopes[index].is_empty()
            && matches!(declaration[2], "{" | ";")
            && !has_direct_cfg_test_attribute(tokens, index)
        {
            bindings.remove(&qualify_declaration(module, declaration[1]));
        }
    }
    let mut cursor = 0;
    while cursor < tokens.len() {
        if tokens[cursor] == "mod" && tokens.get(cursor + 2) == Some(&"{") {
            let open = cursor + 2;
            let close = matching_token(tokens, open, "{", "}");
            if !has_direct_cfg_test_attribute(tokens, cursor) {
                bindings.extend(module_import_bindings(
                    &tokens[open + 1..close],
                    &qualify_declaration(module, tokens[cursor + 1]),
                ));
            }
            cursor = close + 1;
        } else if tokens[cursor] == "{" {
            cursor = matching_token(tokens, cursor, "{", "}") + 1;
        } else {
            cursor += 1;
        }
    }
    bindings
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ScopedImportAlias {
    scope: Vec<usize>,
    alias: String,
    target: String,
    exported: bool,
    inherited: bool,
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
                inherited: false,
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
            inherited: false,
        });
    }

    let mut aliases = Vec::new();
    let mut cursor = 0usize;
    while cursor < tokens.len() {
        // Precise impl-Trait captures are not import declarations. Import
        // paths cannot start with `<`, so real use trees remain checked.
        if tokens[cursor] != "use" || tokens.get(cursor + 1) == Some(&"<") {
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

/// A type declaration in a nearer lexical scope shadows an imported name.
/// Keep that distinction before wrapper classification as well as owner lookup.
fn visible_type_import_aliases(
    tokens: &[&str],
    scopes: &[Vec<usize>],
    imports: &[ScopedImportAlias],
    scope: &[usize],
    module: &str,
) -> BTreeMap<String, String> {
    let mut aliases = visible_import_aliases(imports, scope);
    // Modules and values may share a name. Qualified type paths select the
    // declared module, while a nearer imported module alias may still shadow it.
    for (index, declaration) in tokens.windows(3).enumerate() {
        if declaration[0] != "mod"
            || !matches!(declaration[2], "{" | ";")
            || !scope.starts_with(&scopes[index])
            || has_direct_cfg_test_attribute(tokens, index)
        {
            continue;
        }
        let name = declaration[1];
        let selected = imports
            .iter()
            .filter(|imported| imported.alias == name && scope.starts_with(&imported.scope))
            .max_by_key(|imported| (imported.scope.len(), !imported.inherited));
        if selected.is_some_and(|imported| scopes[index].starts_with(&imported.scope)) {
            let lexical_scopes = tokens[..index]
                .iter()
                .enumerate()
                .filter(|(open, token)| {
                    **token == "{" && scopes[index].starts_with(&scopes[open + 1])
                })
                .map(|(open, _)| classify_lexical_scope(tokens, open, &scopes[open + 1]))
                .collect::<Vec<_>>();
            aliases.insert(
                name.to_owned(),
                format!(
                    "crate::{}",
                    qualify_lexical_declaration(module, &lexical_scopes, name)
                ),
            );
        }
    }
    for (index, window) in tokens.windows(2).enumerate() {
        if !matches!(window[0], "struct" | "enum" | "type") || !scope.starts_with(&scopes[index]) {
            continue;
        }
        let name = window[1];
        let selected = imports
            .iter()
            .filter(|imported| imported.alias == name && scope.starts_with(&imported.scope))
            .max_by_key(|imported| (imported.scope.len(), !imported.inherited));
        if let Some(selected) = selected {
            assert!(
                selected.inherited || scopes[index] != selected.scope,
                "a type declaration and import have the same lexical binding {name}",
            );
            if scopes[index].starts_with(&selected.scope) {
                aliases.remove(name);
            }
        }
    }
    aliases
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
    source_module: &str,
    inherited_imports: &BTreeMap<String, String>,
    wrapper_imports: &BTreeMap<String, String>,
) -> Vec<ProductionField> {
    let scopes = token_scope_paths(tokens);
    let mut imports = scoped_import_aliases(tokens, &scopes);
    let module = qualify_declaration(source_module, module_prefix);
    let nested_modules = tokens
        .windows(3)
        .enumerate()
        .filter(|(_, window)| window[0] == "mod" && window[2] == "{")
        .map(|(index, _)| scopes[index + 3].clone())
        .collect::<Vec<_>>();
    imports.retain(|imported| {
        !nested_modules
            .iter()
            .any(|module| imported.scope.starts_with(module))
    });
    for imported in &mut imports {
        imported.target = anchored_import_target(tokens, &module, &imported.target);
    }
    imports.extend(
        inherited_imports
            .iter()
            .map(|(alias, target)| ScopedImportAlias {
                scope: Vec::new(),
                alias: alias.clone(),
                target: target.clone(),
                exported: false,
                inherited: true,
            })
            .filter(|inherited| {
                !imports
                    .iter()
                    .any(|local| local.scope.is_empty() && local.alias == inherited.alias)
            })
            .collect::<Vec<_>>(),
    );
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
            module: default_source_module(path),
            module_imports: BTreeMap::new(),
            module_declarations: BTreeSet::new(),
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
                let mut aliases = visible_type_import_aliases(
                    tokens,
                    &scopes,
                    &imports,
                    &scopes[cursor],
                    &module,
                );
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
                            module: default_source_module(path),
                            module_imports: BTreeMap::new(),
                            module_declarations: BTreeSet::new(),
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
                            wrapper_imports,
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
                            wrapper_imports,
                        ));
                        cursor = close + 1;
                    }
                    ("enum", "{") => {
                        let close = matching_token(tokens, open, "{", "}");
                        let parsed = parse_enum_fields(
                            path,
                            &carrier,
                            &tokens[open + 1..close],
                            &aliases,
                            wrapper_imports,
                        );
                        if parsed.is_empty() {
                            fields.push(ProductionField {
                                source: path.to_owned(),
                                module: default_source_module(path),
                                module_imports: BTreeMap::new(),
                                module_declarations: BTreeSet::new(),
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
                let aliases = visible_type_import_aliases(
                    tokens,
                    &scopes,
                    &imports,
                    &scopes[cursor],
                    &module,
                );
                let tail = &tokens[cursor + 2..];
                let Some(semicolon_offset) = top_level_position(tail, ";") else {
                    break;
                };
                let declaration = &tail[..semicolon_offset];
                if !in_associated_item_scope(&lexical_scopes)
                    && let Some(equals) = top_level_position(declaration, "=")
                {
                    let reference_retentions = type_reference_retentions(
                        &declaration[equals + 1..],
                        &aliases,
                        wrapper_imports,
                    );
                    fields.push(ProductionField {
                        source: path.to_owned(),
                        module: default_source_module(path),
                        module_imports: BTreeMap::new(),
                        module_declarations: BTreeSet::new(),
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
                    source_module,
                    &visible_type_import_aliases(
                        tokens,
                        &scopes,
                        &imports,
                        &scopes[cursor],
                        &module,
                    ),
                    wrapper_imports,
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
    if name.is_empty() {
        module_prefix.to_owned()
    } else if module_prefix.is_empty() {
        name.to_owned()
    } else {
        format!("{module_prefix}::{name}")
    }
}

fn direct_attributes<'tokens, 'source>(
    tokens: &'tokens [&'source str],
    declaration: usize,
) -> Vec<&'tokens [&'source str]> {
    let mut cursor = declaration;
    if cursor > 0 && tokens[cursor - 1] == ")" {
        let mut open = cursor - 1;
        let mut depth = 1;
        while depth != 0 {
            open = open.checked_sub(1).expect("unbalanced visibility modifier");
            match tokens[open] {
                ")" => depth += 1,
                "(" => depth -= 1,
                _ => {}
            }
        }
        if open > 0 && tokens[open - 1] == "pub" {
            cursor = open - 1;
        }
    } else if cursor > 0 && tokens[cursor - 1] == "pub" {
        cursor -= 1;
    }
    let mut attributes = Vec::new();
    while cursor > 0 && tokens[cursor - 1] == "]" {
        let close = cursor - 1;
        let mut depth = 1;
        let mut open = close;
        while depth != 0 {
            open = open.checked_sub(1).expect("unbalanced attribute");
            match tokens[open] {
                "]" => depth += 1,
                "[" => depth -= 1,
                _ => {}
            }
        }
        if open == 0 || tokens[open - 1] != "#" {
            break;
        }
        attributes.push(&tokens[open + 1..close]);
        cursor = open - 1;
    }
    attributes
}

fn direct_attribute_tokens<'a>(tokens: &[&'a str], declaration: usize) -> Vec<&'a str> {
    direct_attributes(tokens, declaration)
        .into_iter()
        .flatten()
        .copied()
        .collect()
}

fn has_direct_cfg_test_attribute(tokens: &[&str], declaration: usize) -> bool {
    direct_attributes(tokens, declaration)
        .into_iter()
        .any(|attribute| attribute == ["cfg", "(", "test", ")"])
}

/// A repeated root-module reexport can consume a finite qualified suffix.
/// Same-sized or growing repeated bindings do not make resolution progress.
fn record_module_import_progress(binding: &str, remaining: usize, visited: &mut BTreeSet<String>) {
    let prefix = format!("$module::{binding}#");
    for prior in visited
        .iter()
        .filter_map(|entry| entry.strip_prefix(&prefix))
    {
        let prior = prior
            .parse::<usize>()
            .expect("recorded module suffix length");
        assert!(
            remaining < prior,
            "cyclic module import while resolving {binding}"
        );
    }
    visited.insert(format!("{prefix}{remaining}"));
}

/// Resolves a wrapper through exact crate module imports before assigning
/// ownership. A local declaration named Arc/Rc is never recognized by basename.
fn resolve_wrapper_import(path: &str, imports: &BTreeMap<String, String>) -> String {
    let mut current = path.to_owned();
    let mut visited = BTreeSet::new();
    loop {
        let Some(crate_path) = current.strip_prefix("crate::") else {
            return current;
        };
        let segments = crate_path.split("::").collect::<Vec<_>>();
        let mut expanded = None;
        for length in (1..=segments.len()).rev() {
            let binding = segments[..length].join("::");
            if let Some(target) = imports.get(&binding) {
                record_module_import_progress(&binding, segments.len() - length, &mut visited);
                expanded = Some(if length == segments.len() {
                    target.clone()
                } else {
                    format!("{target}::{}", segments[length..].join("::"))
                });
                break;
            }
        }
        match expanded {
            Some(next) => current = next,
            None => return current,
        }
    }
}

fn type_reference_retentions(
    tokens: &[&str],
    aliases: &BTreeMap<String, String>,
    wrapper_imports: &BTreeMap<String, String>,
) -> BTreeMap<String, RetentionSet> {
    fn compose(outer: RetentionSet, wrapper: RetentionSet) -> RetentionSet {
        transform_retention(outer, wrapper)
    }

    fn wrapper_mode(
        path: &str,
        aliases: &BTreeMap<String, String>,
        wrapper_imports: &BTreeMap<String, String>,
    ) -> RetentionSet {
        let first = path.split("::").next().unwrap_or(path);
        let resolved = aliases.get(first).map_or_else(
            || path.to_owned(),
            |target| {
                path.strip_prefix(first)
                    .map_or_else(|| target.clone(), |suffix| format!("{target}{suffix}"))
            },
        );
        let resolved = resolve_wrapper_import(&resolved, wrapper_imports);
        if matches!(
            resolved.as_str(),
            "std::sync::Arc" | "alloc::sync::Arc" | "std::rc::Rc" | "alloc::rc::Rc"
        ) {
            RetentionSet(RetentionSet::SHARED)
        } else if matches!(resolved.as_str(), "std::borrow::Cow" | "alloc::borrow::Cow") {
            RetentionSet(RetentionSet::OWNED | RetentionSet::BORROWED)
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
            RetentionSet(RetentionSet::BORROWED)
        } else {
            RetentionSet::owned()
        }
    }

    fn merge(
        references: &mut BTreeMap<String, RetentionSet>,
        reference: String,
        mode: RetentionSet,
    ) {
        references
            .entry(reference)
            .and_modify(|current| *current = current.union(mode))
            .or_insert(mode);
    }

    fn collect(
        mut tokens: &[&str],
        inherited: RetentionSet,
        aliases: &BTreeMap<String, String>,
        wrapper_imports: &BTreeMap<String, String>,
        references: &mut BTreeMap<String, RetentionSet>,
    ) {
        if tokens.first() == Some(&"pub") {
            tokens = &tokens[1..];
            if tokens.first() == Some(&"(") {
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
            collect(
                &tokens[equals + 1..],
                inherited,
                aliases,
                wrapper_imports,
                references,
            );
            return;
        }
        let comma_parts = split_top_level(tokens, ",");
        if comma_parts.len() > 1 {
            for part in comma_parts {
                collect(part, inherited, aliases, wrapper_imports, references);
            }
            return;
        }
        if tokens[0] == "(" {
            let close = matching_token(tokens, 0, "(", ")");
            if close == tokens.len() - 1 {
                for part in split_top_level(&tokens[1..close], ",") {
                    collect(part, inherited, aliases, wrapper_imports, references);
                }
                return;
            }
        }
        if tokens[0] == "[" {
            let close = matching_token(tokens, 0, "[", "]");
            if close == tokens.len() - 1 {
                let element_end = top_level_position(&tokens[1..close], ";")
                    .map_or(close - 1, |position| position);
                collect(
                    &tokens[1..1 + element_end],
                    inherited,
                    aliases,
                    wrapper_imports,
                    references,
                );
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
                compose(inherited, RetentionSet(RetentionSet::BORROWED)),
                aliases,
                wrapper_imports,
                references,
            );
            return;
        }
        if tokens[0] == "*" {
            let start = usize::from(matches!(tokens.get(1), Some(&"const" | &"mut"))) + 1;
            collect(
                &tokens[start..],
                compose(inherited, RetentionSet(RetentionSet::BORROWED)),
                aliases,
                wrapper_imports,
                references,
            );
            return;
        }
        if matches!(tokens[0], "dyn" | "impl") {
            for bound in split_top_level(&tokens[1..], "+") {
                collect(bound, inherited, aliases, wrapper_imports, references);
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
            let child_mode = compose(inherited, wrapper_mode(&path, aliases, wrapper_imports));
            for argument in split_top_level(&tokens[open + 1..close], ",") {
                collect(argument, child_mode, aliases, wrapper_imports, references);
            }
            if close + 1 < tokens.len() {
                collect(
                    &tokens[close + 1..],
                    inherited,
                    aliases,
                    wrapper_imports,
                    references,
                );
            }
        } else if end + 1 < tokens.len() {
            collect(
                &tokens[end + 1..],
                inherited,
                aliases,
                wrapper_imports,
                references,
            );
        }
    }

    let mut references = BTreeMap::new();
    collect(
        tokens,
        RetentionSet::owned(),
        aliases,
        wrapper_imports,
        &mut references,
    );
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
    wrapper_imports: &BTreeMap<String, String>,
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
                wrapper_imports,
            ));
        } else if let Some(open) = variant.iter().position(|token| *token == "(") {
            let close = matching_token(variant, open, "(", ")");
            fields.extend(parse_tuple_fields(
                path,
                carrier,
                &format!("{name}."),
                &variant[open + 1..close],
                aliases,
                wrapper_imports,
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
    wrapper_imports: &BTreeMap<String, String>,
) -> Vec<ProductionField> {
    split_top_level(body, ",")
        .into_iter()
        .filter_map(|field| {
            let colon = top_level_position(field, ":")?;
            let name =
                field[..colon].iter().rev().copied().find(|token| {
                    is_rust_identifier(token) && !matches!(*token, "pub" | "crate")
                })?;
            let reference_retentions =
                type_reference_retentions(&field[colon + 1..], aliases, wrapper_imports);
            Some(ProductionField {
                source: path.to_owned(),
                module: default_source_module(path),
                module_imports: BTreeMap::new(),
                module_declarations: BTreeSet::new(),
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
    wrapper_imports: &BTreeMap<String, String>,
) -> Vec<ProductionField> {
    split_top_level(body, ",")
        .into_iter()
        .enumerate()
        .filter(|(_, field)| !field.is_empty())
        .map(|(index, field)| {
            let reference_retentions = type_reference_retentions(field, aliases, wrapper_imports);
            ProductionField {
                source: path.to_owned(),
                module: default_source_module(path),
                module_imports: BTreeMap::new(),
                module_declarations: BTreeSet::new(),
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
fn resolved_modules_have_one_ordered_representation_and_kind_gate_before_construction() {
    const CONSTRUCTION: [&str; 5] = ["ResolvedModule", ":", ":", "new", "("];
    const GATES: [[&str; 2]; 3] = [
        ["prepare_module_representation_kinds", "("],
        ["check_newtype_representation_cycles", "("],
        ["check_remaining_module_kinds", "("],
    ];
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
    let gates = GATES.map(|gate| {
        let calls = tokens
            .windows(gate.len())
            .enumerate()
            .filter_map(|(index, window)| (window == gate).then_some(index))
            .collect::<Vec<_>>();
        assert_eq!(
            calls.len(),
            1,
            "resolution must invoke each admission stage exactly once: {gate:?}: {calls:?}"
        );
        calls[0]
    });
    let construction = tokens
        .windows(CONSTRUCTION.len())
        .position(|window| window == CONSTRUCTION)
        .expect("resolution must publish the checked module once");
    assert!(
        gates[0] < gates[1] && gates[1] < gates[2] && gates[2] < construction,
        "representation kinds, cycles and remaining kinds must complete in order before construction",
    );
}

#[test]
fn abstract_nominal_kind_publication_transfers_the_reserved_allocation() {
    const FUNCTION: [&str; 3] = ["fn", "with_abstract_nominal_facts", "("];
    const WHOLE_MAP_TRANSFER: [&str; 20] = [
        "discard_non_materialized_nominal_kind_facts",
        "(",
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
        ",",
        ")",
        ")",
    ];
    const PER_ENTRY_INSERT: [&str; 6] = ["self", ".", "abstract_nominal_kinds", ".", "insert", "("];
    const DISPOSAL_HELPER: [&str; 3] = ["fn", "discard_non_materialized_nominal_kind_facts", "("];
    const DISPLACED_VALUES: [&str; 5] = ["facts", ".", "into_values", "(", ")"];
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
    let helper = tokens
        .windows(DISPOSAL_HELPER.len())
        .position(|window| window == DISPOSAL_HELPER)
        .expect("the immediate displaced-map disposal helper should exist");
    let helper_open = tokens[helper..]
        .iter()
        .position(|token| *token == "{")
        .map(|offset| helper + offset)
        .expect("the displaced-map disposal helper should have a body");
    let helper_close = matching_token(&tokens, helper_open, "{", "}");
    let helper_body = &tokens[helper_open + 1..helper_close];

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
        helper_body
            .windows(DISPLACED_VALUES.len())
            .any(|window| window == DISPLACED_VALUES)
            && helper_body
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
    let forbidden = CORE_SOURCES
        .iter()
        .flat_map(|(path, source)| {
            production_rust_code_tokens(source)
                .into_iter()
                .filter(|token| is_rust_identifier(token))
                .filter(move |identifier| {
                    is_forbidden_interface_identifier(identifier)
                        && !is_allowed_private_core_method_evidence_identifier(path, identifier)
                })
                .map(move |identifier| format!("{path}::{identifier}"))
        })
        .collect::<BTreeSet<_>>();
    assert!(
        forbidden.is_empty(),
        "Core gained identifiers outside its closed inventory:\n{}",
        forbidden.into_iter().collect::<Vec<_>>().join("\n")
    );
}

#[test]
fn goal_key_argument_markers_reserve_fallibly_before_every_push() {
    let tokens = production_rust_code_tokens(EVIDENCE_SOURCE);
    let signature = ["fn", "goal_key", "("];
    let function = tokens
        .windows(signature.len())
        .position(|window| window == signature)
        .expect("goal_key exists");
    let open = tokens[function..]
        .iter()
        .position(|token| *token == "{")
        .unwrap()
        + function;
    let close = matching_token(&tokens, open, "{", "}");
    let body = &tokens[open + 1..close];
    let locate = |pattern: &[&str]| {
        body.windows(pattern.len())
            .position(|window| window == pattern)
            .unwrap_or_else(|| panic!("missing charged goal-key operation {pattern:?}"))
    };
    let staging_charge = locate(&["constraint_work", ".", "charge", "("]);
    let staging_reserve = locate(&["pending", ".", "try_reserve", "("]);
    let marker = locate(&[
        "pending", ".", "push", "(", "Task", ":", ":", "Cell", "(", "GoalCell", ":", ":",
        "Argument", "(", "position", ")",
    ]);
    assert!(
        staging_charge < staging_reserve && staging_reserve < marker,
        "ordered owner argument markers must be charged and reserved before staging"
    );
    assert!(
        body[staging_reserve..marker]
            .windows(3)
            .any(|window| window == ["checked_mul", "(", "2"]),
        "staging reserves both the complete tagged argument and its ordered marker"
    );
    let loop_start = locate(&["while", "let", "Some", "(", "task", ")"]);
    let output_charge = body[loop_start..]
        .windows(6)
        .position(|window| window == ["constraint_work", ".", "charge", "(", "1", ")"])
        .unwrap()
        + loop_start;
    let output_reserve = locate(&["cells", ".", "try_reserve", "(", "1", ")"]);
    let output_match = locate(&["match", "task", "{"]);
    let output_push = locate(&[
        "Task", ":", ":", "Cell", "(", "cell", ")", "=", ">", "cells", ".", "push", "(", "cell",
        ")",
    ]);
    assert!(
        loop_start < output_charge
            && output_charge < output_reserve
            && output_reserve < output_match
            && output_match < output_push,
        "every one-cell output path is charged and fallibly reserved before dispatch"
    );
    assert!(
        body[output_reserve..output_match].contains(&"ConstraintResource"),
        "output allocation failure preserves constraint-resource ownership"
    );
}

#[test]
fn determination_snapshot_has_no_uncharged_pending_prescan() {
    const FUNCTION: [&str; 3] = ["fn", "prepare_determination_snapshot", "<"];
    const ITERATOR_PRESCAN: [&str; 7] = [".", "iter", "(", ")", ".", "any", "("];

    let tokens = production_rust_code_tokens(EVIDENCE_SOURCE);
    let function = tokens
        .windows(FUNCTION.len())
        .position(|window| window == FUNCTION)
        .expect("determination snapshot preparation should exist");
    let body_open = tokens[function..]
        .iter()
        .position(|token| *token == "{")
        .map(|offset| function + offset)
        .expect("determination snapshot preparation should have a body");
    let body_close = matching_token(&tokens, body_open, "{", "}");
    let body = &tokens[body_open + 1..body_close];

    assert!(
        !body
            .windows(ITERATOR_PRESCAN.len())
            .any(|window| window == ITERATOR_PRESCAN),
        "determination snapshot eligibility must use the captured pending marker instead of an uncharged suffix pre-scan",
    );
}

#[test]
fn effect_instance_admission_charges_before_owned_argument_extraction() {
    const FUNCTION: [&str; 3] = ["fn", "admit_effect_instance", "("];
    const CHARGE: [&str; 15] = [
        "self",
        ".",
        "type_work",
        ".",
        "charge",
        "(",
        "instance",
        ".",
        "arguments",
        "(",
        ")",
        ".",
        "len",
        "(",
        ")",
    ];
    const SCAN: [&str; 2] = ["scan_type_admission", "("];
    const CLONE: [&str; 2] = ["clone_effect_instance_with_budget", "("];

    let tokens = production_rust_code_tokens(CORE_DIALECT_SOURCE);
    let function = tokens
        .windows(FUNCTION.len())
        .position(|window| window == FUNCTION)
        .expect("effect-instance admission should exist");
    let body_open = tokens[function..]
        .iter()
        .position(|token| *token == "{")
        .map(|offset| function + offset)
        .expect("effect-instance admission should have a body");
    let body_close = matching_token(&tokens, body_open, "{", "}");
    let body = &tokens[body_open + 1..body_close];
    let charge = body
        .windows(CHARGE.len())
        .position(|window| window == CHARGE)
        .expect("effect-instance admission should charge the borrowed argument count");
    let scan = body
        .windows(SCAN.len())
        .position(|window| window == SCAN)
        .expect("effect-instance admission scans the complete borrowed argument vector");
    let clone = body
        .windows(CLONE.len())
        .position(|window| window == CLONE)
        .expect("effect-instance admission clones only when normalization is required");

    assert!(
        charge < scan && scan < clone,
        "effect-instance admission must charge before scanning or allocating a normalized copy",
    );
}

#[test]
fn relational_vector_owners_charge_before_allocation() {
    fn function_body<'a>(tokens: &'a [&str], function: &[&str]) -> &'a [&'a str] {
        let function = tokens
            .windows(function.len())
            .position(|window| window == function)
            .expect("the guarded function should exist");
        let body_open = tokens[function..]
            .iter()
            .position(|token| *token == "{")
            .map(|offset| function + offset)
            .expect("the guarded function should have a body");
        let body_close = matching_token(tokens, body_open, "{", "}");
        &tokens[body_open + 1..body_close]
    }

    fn position(tokens: &[&str], pattern: &[&str]) -> usize {
        tokens
            .windows(pattern.len())
            .position(|window| window == pattern)
            .unwrap_or_else(|| panic!("missing ownership operation {pattern:?}"))
    }

    let evidence = production_rust_code_tokens(EVIDENCE_SOURCE);
    let ingress = function_body(&evidence, &["fn", "add_interface_fact_parts", "("]);
    let parameter_constraint_charge = position(
        ingress,
        &[
            "constraint_work",
            ".",
            "charge",
            "(",
            "fact",
            ".",
            "parameters",
            ".",
            "len",
            "(",
            ")",
            ")",
        ],
    );
    let parameter_type_charge = position(
        ingress,
        &[
            "type_work",
            ".",
            "charge",
            "(",
            "fact",
            ".",
            "parameters",
            ".",
            "len",
            "(",
            ")",
            ")",
        ],
    );
    let parameter_reserve = position(
        ingress,
        &[
            "parameters",
            ".",
            "try_reserve_exact",
            "(",
            "fact",
            ".",
            "parameters",
            ".",
            "len",
            "(",
            ")",
            ")",
        ],
    );
    assert!(
        parameter_constraint_charge < parameter_reserve
            && parameter_type_charge < parameter_reserve,
        "interface-parameter constraint and type owners must charge before retained-row allocation",
    );
    assert!(
        !ingress.contains(&"interface_parameter_ids"),
        "strict source-identity order must avoid a redundant duplicate-index allocation",
    );

    let elaboration_source =
        fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("src/elaborate.rs"))
            .expect("elaboration source should be readable");
    let elaboration = production_rust_code_tokens(&elaboration_source);
    let scheme_lowering = function_body(&elaboration, &["fn", "lower_constrained_scheme", "("]);
    let requirement_charge = position(
        scheme_lowering,
        &[
            "self",
            ".",
            "type_work",
            ".",
            "charge",
            "(",
            "scheme",
            ".",
            "requirements",
            ".",
            "len",
            "(",
            ")",
            ")",
        ],
    );
    let requirement_lowering = position(
        scheme_lowering,
        &["self", ".", "lower_evidence_requirements", "("],
    );
    assert!(
        requirement_charge < requirement_lowering,
        "scheme requirement ownership must charge before delegating to shared lowering",
    );
    let lowering = function_body(&elaboration, &["fn", "lower_evidence_requirements", "("]);
    let method_row_charge = position(
        lowering,
        &[
            "self",
            ".",
            "type_work",
            ".",
            "charge",
            "(",
            "lowered_interface",
            ".",
            "methods",
            ".",
            "len",
            "(",
            ")",
            ")",
        ],
    );
    let method_row_reserve = position(
        lowering,
        &[
            "methods",
            ".",
            "try_reserve",
            "(",
            "lowered_interface",
            ".",
            "methods",
            ".",
            "len",
            "(",
            ")",
            ")",
        ],
    );
    assert!(
        method_row_charge < method_row_reserve,
        "method-row ownership must charge before allocation",
    );

    let substitution_charge = position(
        lowering,
        &[
            "self",
            ".",
            "type_work",
            ".",
            "charge",
            "(",
            "method_fact",
            ".",
            "parameters",
            ".",
            "len",
            "(",
            ")",
            ")",
        ],
    );
    let substitution_insert = position(lowering, &["replacement", ".", "insert_cloned", "("]);
    assert!(
        substitution_charge < substitution_insert,
        "complete substitution entries must be charged before entering the shared owner gate"
    );
    let tagged_insert = function_body(&elaboration, &["fn", "insert_cloned", "("]);
    assert!(
        tagged_insert.windows(10).any(|window| {
            window
                == [
                    "self",
                    ".",
                    "insert_borrowed",
                    "(",
                    "parameter",
                    ",",
                    "argument",
                    ",",
                    "budget",
                    ")",
                ]
        }),
        "tagged owner arguments must enter the canonical borrowed insertion gate",
    );
    for operation in [
        "try_reserve",
        "clone_type_with_budget",
        "clone_effect_row_with_budget",
    ] {
        assert!(
            !tagged_insert.contains(&operation),
            "tagged owner delegation must not allocate or clone before the canonical charge",
        );
    }
    let owner_insert = function_body(&elaboration, &["fn", "insert_borrowed", "("]);
    let entry_charge = position(owner_insert, &["budget", ".", "charge", "(", "1", ")"]);
    let type_guard = position(
        owner_insert,
        &[
            "self",
            ".",
            "types",
            ".",
            "as_map",
            "(",
            ")",
            ".",
            "contains_key",
            "(",
        ],
    );
    let row_guard = position(
        owner_insert,
        &["self", ".", "rows", ".", "contains_key", "("],
    );
    assert!(
        entry_charge < type_guard && entry_charge < row_guard,
        "canonical owner insertion must charge before checking either tag storage",
    );
    for (storage, clone) in [
        ("types", "clone_type_with_budget"),
        ("rows", "clone_effect_row_with_budget"),
    ] {
        let reserve = position(
            owner_insert,
            &["self", ".", storage, ".", "try_reserve", "(", "1", ")"],
        );
        assert!(
            entry_charge < reserve && type_guard < reserve && row_guard < reserve,
            "each tagged owner substitution storage must charge and reject duplicate keys before fallible reservation"
        );
        assert!(
            reserve < position(owner_insert, &[clone, "("]),
            "owned replacement cloning must follow its charged fallible reservation",
        );
        assert!(
            owner_insert[reserve..].contains(&"type_resource"),
            "owner substitution allocation preserves type-resource ownership"
        );
    }
}

#[test]
fn implementation_prerequisite_containment_uses_the_canonical_owner_index() {
    const FUNCTION: [&str; 3] = [
        "fn",
        "authenticate_implementation_prerequisite_binders",
        "(",
    ];
    const NESTED_HEAD_SCAN: [&str; 10] = [
        "fact",
        ".",
        "head_parameters",
        ".",
        "iter",
        "(",
        ")",
        ".",
        "any",
        "(",
    ];
    const CANONICAL_LOOKUP: [&str; 7] = [
        "environments",
        ".",
        "summary_declared",
        "(",
        "*",
        "identity",
        ")",
    ];
    const EXACT_OWNER: &[&str] = &[
        "Some",
        "(",
        "(",
        "_",
        ",",
        "_",
        ",",
        "Some",
        "(",
        "SummaryBinderOwner",
        ":",
        ":",
        "Implementation",
        "(",
        "owner",
        ")",
        ")",
        ")",
        ")",
        "if",
        "owner",
        "=",
        "=",
        "fact",
        ".",
        "id",
    ];
    const HEAD_OWNER_SETUP: &[&str] = &[
        "register_summary_parameters",
        "(",
        "&",
        "fact",
        ".",
        "head_parameters",
        ",",
        "SummaryBinderOwner",
        ":",
        ":",
        "Implementation",
        "(",
        "fact",
        ".",
        "id",
        ")",
        ",",
        "&",
        "mut",
        "environments",
    ];

    let source = fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("src/resolved.rs"))
        .expect("resolved source should be readable");
    let tokens = production_rust_code_tokens(&source);
    let function = tokens
        .windows(FUNCTION.len())
        .position(|window| window == FUNCTION)
        .expect("implementation prerequisite binder authentication should exist");
    let body_open = tokens[function..]
        .iter()
        .position(|token| *token == "{")
        .map(|offset| function + offset)
        .expect("implementation prerequisite binder authentication should have a body");
    let body_close = matching_token(&tokens, body_open, "{", "}");
    let body = &tokens[body_open + 1..body_close];

    assert!(
        !body
            .windows(NESTED_HEAD_SCAN.len())
            .any(|window| window == NESTED_HEAD_SCAN),
        "charged prerequisite variables must not trigger an uncharged scan of every implementation head parameter",
    );
    assert!(
        body.windows(CANONICAL_LOOKUP.len())
            .any(|window| window == CANONICAL_LOOKUP),
        "prerequisite containment must use the canonical binder-owner index in the kind environment",
    );
    assert!(
        body.windows(EXACT_OWNER.len())
            .any(|window| window == EXACT_OWNER),
        "prerequisite membership must require the exact implementation owner, not only a declared binder",
    );
    assert!(
        tokens
            .windows(HEAD_OWNER_SETUP.len())
            .any(|window| window == HEAD_OWNER_SETUP),
        "head setup must retain its exact original implementation owner in the canonical kind environment",
    );
}

#[test]
fn private_core_allowlist_excludes_scalar_interface_carriers() {
    for identifier in [
        "CheckedImplementationFact",
        "CheckedRequirement",
        "ImplementationAuthorization",
        "ImportedImplementationFact",
    ] {
        for (path, _) in CORE_SOURCES {
            assert!(!is_allowed_private_core_method_evidence_identifier(
                path, identifier
            ));
        }
    }
    for identifier in [
        "expected_anchor_interface",
        "expected_interface",
        "interface_argument",
        "interface_parameter",
    ] {
        for path in [
            "src/core/dialect.rs",
            "src/core/transform.rs",
            "src/core/validate.rs",
        ] {
            assert!(
                !is_allowed_private_core_method_evidence_identifier(path, identifier),
                "the private Core allowlist must not retain dead scalar carrier {path}::{identifier}",
            );
        }
    }
}

#[test]
fn private_core_layout_and_family_authentication_is_path_confined() {
    let allowed: &[(&str, &[&str])] = &[
        (
            "with_registry_method_evidence_and_rewrite_work",
            &["src/core/dialect.rs", "src/core/transform.rs"],
        ),
        (
            "with_registry_method_evidence_and_arena_work",
            &["src/core/dialect.rs"],
        ),
        ("canonical_evidence_creation_row", &["src/core/validate.rs"]),
        (
            "LexicalEvidenceId",
            &[
                "src/core/dialect.rs",
                "src/core/validate.rs",
                "src/core/transform.rs",
            ],
        ),
    ];
    for (identifier, paths) in allowed {
        assert!(is_forbidden_interface_identifier(identifier));
        for (path, _) in CORE_SOURCES {
            assert_eq!(
                is_allowed_private_core_method_evidence_identifier(path, identifier),
                paths.contains(path),
                "private authentication allowance changed for {path}::{identifier}",
            );
        }
        for (path, _) in EVALUATOR_SOURCES {
            assert!(
                !is_allowed_private_core_method_evidence_identifier(path, identifier),
                "evaluator gained an authentication allowance for {path}::{identifier}",
            );
        }
    }
    for identifier in ["runtime_dictionary_dispatch", "interface_runtime_lookup"] {
        assert!(is_forbidden_interface_identifier(identifier));
        for (path, _) in CORE_SOURCES.iter().chain(EVALUATOR_SOURCES.iter()) {
            assert!(!is_allowed_private_core_method_evidence_identifier(
                path, identifier
            ));
        }
    }
}

fn is_allowed_private_core_method_evidence_identifier(path: &str, identifier: &str) -> bool {
    let shared = matches!(
        identifier,
        "InterfaceApplication"
            | "EvidenceNode"
            | "EvidenceNodeId"
            | "EvidenceSelection"
            | "Implementation"
            | "ImplementationOwner"
            | "Impl"
            | "ImplMethodId"
            | "RequirementId"
            | "actual_interface"
            | "checked_application"
            | "interface_parameters"
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
                // Canonical Layout/family authentication; no runtime selection.
                "MethodEvidenceResourceOwner"
                    | "MethodEvidenceAdapter"
                    | "MethodEvidenceLexicalOwner"
                    | "LexicalEvidenceId"
                    | "MethodEvidenceAdapterEdge"
                    | "MethodEvidenceConcretePrerequisite"
                    | "MethodEvidenceConcreteSource"
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
                    | "method_evidence_anchor_keys"
                    | "method_evidence_expectation_positions"
                    | "concrete_sources"
                    | "clone_interface_application_for_rebuild"
                    | "empty_method_evidence"
                    | "implementation_owner_count"
                    | "implementation_owners_mut_for_core_test"
                    | "method_evidence"
                    | "method_evidence_adapter_application_matches"
                    | "method_evidence_adapter_interface_matches"
                    | "method_evidence_anchor_matches_expectation"
                    | "method_evidence_anchor_identity_work"
                    | "method_evidence_anchors"
                    | "method_evidence_expected_producer_matches"
                    | "method_evidence_producer_matches"
                    | "requires_method_evidence_implementation_owner"
                    | "requirement_position"
                    | "same_interface_application_with_budget"
                    | "target_requirement"
                    | "with_registry_and_method_evidence"
                    | "with_registry_method_evidence_and_rewrite_work"
                    | "with_registry_method_evidence_and_type_work"
                    | "with_registry_method_evidence_and_arena_work"
            ),
            // These names reconstruct canonical imported catalogs and authenticate
            // the unpublished Core occurrence graph. None selects evaluator dispatch.
            "src/core/validate.rs" => matches!(
                identifier,
                // Canonical Layout/family authentication; no runtime selection.
                "LexicalEvidenceId"
                    | "canonical_evidence_creation_row"

                // Canonical owner-signature authentication, not selection or runtime dispatch.
                    | "MethodEvidenceResourceOwner"
                    | "Interface"

                    | "evidence"

                    | "MethodEvidenceAnchor"
                    | "MethodEvidenceAnchorRole"
                    | "MethodEvidenceLexicalOwner"
                    | "MethodEvidenceCatalog"
                    | "MethodEvidenceCatalogMutationForTest"
                    | "MethodEvidenceExpectedProducer"
                    | "MethodEvidenceExpectedRole"
                    | "MethodEvidenceOwner"
                    | "MethodEvidenceProducer"
                    | "ScopeRequirement"
                    | "ScopeRequirementKey"
                    // Diagnostic causes for lexical scope metadata, not interface machinery.
                    | "MissingCaptureRequirement"
                    | "MissingTypeRequirementSlot"
                    | "ScopeRequirements"
                    // Prepaid binary catalog lookup; no selection or runtime dispatch.
                    | "charge_method_catalog_binary_lookup"
                    | "authenticated_method_evidence"
                    | "enclosing_implementation_replacements"
                    | "implementation_owner_count"
                    | "implementation_replacements"
                    | "method_evidence"
                    | "method_evidence_anchor_matches_expectation"
                    | "method_evidence_anchors"
                    | "method_evidence_producer_matches"
                    | "method_evidence_scope_binder"
                    | "method_evidence_subtree_contains"
                    | "previous_interface_parameters"
                    | "same_interface_application"
                    | "substitute_interface_application"
                    | "validate_concrete_adapter_source"
                    | "validate_implementation_owner_anchor"
                    | "validate_method_evidence_authority"
                    | "validate_method_evidence_catalog_applications"
                    | "validate_method_evidence_carrier_incoming"
                    | "validate_method_evidence_domain"
                    | "validate_method_evidence_domain_order"
                    | "validate_method_evidence_owner_envelopes"
                    | "validate_method_evidence_type_owners"
            ),
            "src/core/transform.rs" => matches!(
                identifier,
                "LexicalEvidenceId"
                    | "interface"
                    | "MethodEvidenceCatalog"
                    | "MethodEvidenceAnchorRole"
                    | "authenticate_method_evidence"
                    | "clone_interface_application_for_rebuild"
                    | "method_evidence"
                    | "method_evidence_anchors"
                    | "requirement"
                    | "with_registry_and_method_evidence"
                    | "with_registry_method_evidence_and_rewrite_work"
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

#[test]
fn production_token_scanner_excludes_only_explicit_test_items() {
    let source = r#"
        #[cfg(test)] #[allow(dead_code)] fn hidden_test_helper() { interface_dispatch(); }
        fn interface_dispatch_for_test() { interface_dispatch(); }
        mod nested {
            #[cfg(test)] pub(crate) fn hidden_nested_helper() { interface_dispatch(); }
            #[cfg(test)] #[path = "absent.rs"] mod hidden_external_tests;
            fn retained_nested_helper() { interface_dispatch(); }
        }
        #[cfg(test)] struct HiddenTestCarrier { interface: () }
        struct RetainedCarrier { interface: () }
    "#;
    let tokens = production_rust_code_tokens(source);
    for omitted in [
        "hidden_test_helper",
        "hidden_nested_helper",
        "hidden_external_tests",
        "HiddenTestCarrier",
    ] {
        assert!(
            !tokens.contains(&omitted),
            "explicit test item {omitted} survived"
        );
    }
    for retained in [
        "interface_dispatch_for_test",
        "retained_nested_helper",
        "RetainedCarrier",
        "interface_dispatch",
        "interface",
    ] {
        assert!(
            tokens.contains(&retained),
            "production item {retained} was skipped"
        );
    }
    assert!(tokens.into_iter().any(is_forbidden_interface_identifier));
}

fn production_rust_code_tokens(source: &str) -> Vec<&str> {
    const CFG_TEST: [&str; 7] = ["#", "[", "cfg", "(", "test", ")", "]"];

    let tokens = rust_code_tokens(source);
    let mut production = Vec::with_capacity(tokens.len());
    let mut cursor = 0usize;
    while cursor < tokens.len() {
        if tokens[cursor..].starts_with(&CFG_TEST) {
            let mut item = cursor + CFG_TEST.len();
            while tokens.get(item) == Some(&"#") && tokens.get(item + 1) == Some(&"[") {
                item = matching_token(&tokens, item + 1, "[", "]") + 1;
            }
            if tokens.get(item) == Some(&"pub") {
                item += 1;
                if tokens.get(item) == Some(&"(") {
                    item = matching_token(&tokens, item, "(", ")") + 1;
                }
            }
            if !tokens.get(item).is_some_and(|token| {
                matches!(
                    *token,
                    "fn" | "struct"
                        | "enum"
                        | "mod"
                        | "impl"
                        | "use"
                        | "const"
                        | "static"
                        | "type"
                        | "trait"
                )
            }) {
                production.push(tokens[cursor]);
                cursor += 1;
                continue;
            }
            let mut end = cursor + CFG_TEST.len();
            let mut depths = [0usize; 4];
            while end < tokens.len() {
                if depths.iter().all(|depth| *depth == 0) && matches!(tokens[end], "{" | ";") {
                    cursor = if tokens[end] == "{" {
                        matching_token(&tokens, end, "{", "}") + 1
                    } else {
                        end + 1
                    };
                    break;
                }
                update_delimiter_depths(tokens[end], &mut depths);
                end += 1;
            }
            assert!(
                end < tokens.len(),
                "test-only item must have a closed body or declaration"
            );
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

fn owner_bindings(tokens: &[&str], scopes: &[Vec<usize>], owner: &str) -> Vec<OwnerBinding> {
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
                binding_owns_at(&bindings, scopes, alias, equals.saturating_sub(1))
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
        path: &str,
        source_owner: &str,
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
                    // This existing infallible factory transfers the whole
                    // heap and root-completion owner into Arc<ObservedHeap>.
                    if path == "src/eval/machine.rs"
                        && source_owner == "Machine"
                        && owners.contains("ObservedHeap")
                        && cursor >= 4
                        && tokens[cursor - 4..cursor]
                            == ["ObservedHeap", ":", ":", "with_root_completion"]
                    {
                        let close = matching_token(tokens, cursor, "(", ")");
                        let expected = production_rust_code_tokens(
                            "ObservedHeap::with_root_completion(
                                 Arc::clone(self.program.registry()),
                                 std::mem::take(&mut self.heap),
                                 self.root_completion.take(),
                             )",
                        );
                        let in_run_loop = tokens.windows(3).enumerate().any(|(at, window)| {
                            if window != ["fn", "run_loop", "("] {
                                return false;
                            }
                            let parameters = matching_token(tokens, at + 2, "(", ")");
                            let Some((open, "{")) = declaration_delimiter(tokens, parameters + 1)
                            else {
                                return false;
                            };
                            open < cursor && cursor < matching_token(tokens, open, "{", "}")
                        });
                        if in_run_loop && tokens[cursor - 4..=close] == expected {
                            return Some("ObservedHeap");
                        }
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

    fn proven_container_discard(tokens: &[&str], helper: &str) -> bool {
        let expected = match helper {
            "discard_resolved_effects_iteratively" => {
                "for effect in effects.into_vec() { discard_resolved_effect_iteratively(effect); }"
            }
            "discard_resolved_nominals_iteratively" => {
                "for nominal in nominals.into_vec() {
                    if let Some(representation) = nominal.representation {
                        discard_type_iteratively(representation);
                    }
                    discard_origin_iteratively(nominal.origin);
                }"
            }
            "discard_resolved_constructors_iteratively" => {
                "for constructor in constructors.into_vec() {
                    if let Some(payload) = constructor.payload {
                        discard_type_iteratively(payload);
                    }
                    discard_origin_iteratively(constructor.origin);
                }"
            }
            "discard_non_materialized_nominal_kind_facts" => {
                "for fact in facts.into_values() { discard_non_materialized_nominal_kind_fact(fact); }"
            }
            _ => return false,
        };
        let expected = production_rust_code_tokens(expected);
        let mut found = false;
        for function in tokens
            .windows(3)
            .enumerate()
            .filter_map(|(at, window)| (window == ["fn", helper, "("]).then_some(at))
        {
            let parameters_close = matching_token(tokens, function + 2, "(", ")");
            let Some((open, "{")) = declaration_delimiter(tokens, parameters_close + 1) else {
                return false;
            };
            let close = matching_token(tokens, open, "{", "}");
            if tokens[open + 1..close] != expected {
                return false;
            }
            found = true;
        }
        found
    }

    fn immediately_discarded_member(path: &str, owner: &str, tokens: &[&str], at: usize) -> bool {
        let Some(open) = at.checked_sub(3) else {
            return false;
        };
        if tokens.get(open..at) != Some(&["(", "&", "mut"][..]) || open == 0 {
            return false;
        }
        let operation = tokens[open - 1];
        if !matches!(operation, "take" | "replace") {
            return false;
        }
        let mut call_start = open - 1;
        while call_start >= 3
            && tokens[call_start - 1] == ":"
            && tokens[call_start - 2] == ":"
            && is_rust_identifier(tokens[call_start - 3])
        {
            call_start -= 3;
        }
        let qualifier = &tokens[call_start..open - 1];
        if !qualifier.is_empty()
            && qualifier != ["mem", ":", ":"]
            && qualifier != ["std", ":", ":", "mem", ":", ":"]
        {
            return false;
        }
        let Some(wrapper_open) = call_start.checked_sub(1) else {
            return false;
        };
        let Some(helper_at) = wrapper_open.checked_sub(1) else {
            return false;
        };
        let helper = tokens[helper_at];
        if tokens[wrapper_open] != "(" || !helper.starts_with("discard_") {
            return false;
        }
        let close = matching_token(tokens, open, "(", ")");
        let wrapper_close = matching_token(tokens, wrapper_open, "(", ")");
        if wrapper_close != close + 1 && !(wrapper_close == close + 2 && tokens[close + 1] == ",") {
            return false;
        }
        // The displaced value must be the whole sole argument. A preceding
        // unrelated discard or a later projection grants no transfer proof.
        let mut arguments = split_top_level(&tokens[open + 1..close], ",");
        if arguments.last().is_some_and(|argument| argument.is_empty()) {
            arguments.pop();
        }
        // Only the Core family contract may consume this opaque carrier.
        // Exact qualification and the whole returned carrier matter here.
        if path == "src/core/dialect.rs"
            && owner == "CoreBuilder"
            && helper == "discard_effects"
            && helper_at >= 3
            && tokens[helper_at - 3..helper_at] == ["F", ":", ":"]
            && (helper_at == 3 || tokens[helper_at - 4] != ":")
            && operation == "replace"
            && arguments.len() == 2
        {
            let stored = arguments[1];
            return stored.starts_with(&["F", ":", ":", "store_effects", "("])
                && matching_token(stored, 4, "(", ")") == stored.len() - 1;
        }
        if proven_container_discard(tokens, helper) {
            return arguments.len() == if operation == "replace" { 2 } else { 1 };
        }
        matches!(
            helper,
            "discard_type_iteratively" | "discard_origin_iteratively"
        ) && (operation == "take"
            || (arguments.len() == 2 && arguments[1] == ["Type", ":", ":", "Unit"]))
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
        let mut depths = [0usize; 4];
        while cursor + 1 < tail.len() {
            if depths.iter().all(|depth| *depth == 0)
                && matches!(tail[cursor], "=" | ";" | "," | ")" | "]" | "}")
            {
                break;
            }
            if depths.iter().all(|depth| *depth == 0)
                && tail[cursor] == "."
                && is_rust_identifier(tail[cursor + 1])
                && tail.get(cursor + 2) != Some(&"(")
            {
                terminal = tail[cursor + 1];
            }
            update_delimiter_depths(tail[cursor], &mut depths);
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
    let bindings = owner_bindings(tokens, &scopes, owner);
    let teardown_ranges = drop_teardown_ranges(tokens, owner);
    for index in 0..tokens.len().saturating_sub(2) {
        if tokens[index + 1] != "."
            || !fields.contains(tokens[index + 2])
            || teardown_ranges
                .iter()
                .any(|(open, close)| *open < index && index < *close)
            || !binding_owns_at(&bindings, &scopes, tokens[index], index)
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
        // The evaluator only refills a consumed control slot. Recognize the
        // complete existing handoff, including its release-mode precondition
        // before frame mutation; no other Machine field or method is exempt.
        let empty_control_handoff = path == "src/eval/machine.rs"
            && owner == "Machine"
            && tokens[index..index + 3] == ["self", ".", "control"]
            && tokens.windows(3).enumerate().any(|(at, window)| {
                if window != ["fn", "apply", "("] {
                    return false;
                }
                let parameters_close = matching_token(tokens, at + 2, "(", ")");
                let Some((open, "{")) = declaration_delimiter(tokens, parameters_close + 1) else {
                    return false;
                };
                let close = matching_token(tokens, open, "{", "}");
                let expected = production_rust_code_tokens(
                    "assert!(self.control.is_none());
                     if let Some(frame) = transition.frame {
                         self.frames.push(frame);
                         self.max_frame_depth = self.max_frame_depth.max(self.frames.len());
                     }
                     self.control = Some(transition.control);",
                );
                open < index && index < close && tokens[open + 1..close] == expected
            });
        if has_assignment_before_statement_end(tail) && !empty_control_handoff {
            panic!(
                "{path} must not assign through raw or nested {owner} backing storage via {}.{} near {:?}",
                tokens[index],
                tokens[index + 2],
                &tail[..tail.len().min(24)],
            );
        }
        // Capturing a continuation moves every selected frame into the
        // existing iterative owner, with no fallible step after the drain.
        let captured_frame_transfer = path == "src/eval/machine.rs"
            && owner == "Machine"
            && custom_drop_owners.contains("CapturedContinuation")
            && tokens[index..index + 3] == ["self", ".", "frames"]
            && index >= 4
            && tokens.windows(3).enumerate().any(|(at, window)| {
                if window != ["fn", "capture_from", "("] {
                    return false;
                }
                let parameters = matching_token(tokens, at + 2, "(", ")");
                let Some((open, "{")) = declaration_delimiter(tokens, parameters + 1) else {
                    return false;
                };
                let close = matching_token(tokens, open, "{", "}");
                let expected = production_rust_code_tokens(
                    "frames.extend(self.frames.drain(selected..));
                     self.captured_cells = retained;
                     Ok(CapturedContinuation { frames })",
                );
                open < index && index < close && tokens[index - 4..close] == expected
            });
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
            && !captured_frame_transfer
        {
            panic!(
                "{path} must not invoke destructive mutation through raw {owner} backing storage via {}.{}.{}",
                tokens[index],
                tokens[index + 2],
                tail[1],
            );
        }
        // This fallible transfer retains every complete quantified pair in
        // TypeContext. On failure the incoming Box and remaining map iterator
        // own only Kind roots, whose existing Drop is iterative.
        let quantified_owner_transfer = path == "src/elaborate.rs"
            && owner == "PreparedGlobals"
            && custom_drop_owners.contains("TypeContext")
            && tokens[index..index + 3] == ["prepared", ".", "quantifiers"]
            && tokens.windows(3).enumerate().any(|(at, window)| {
                if window != ["fn", "finish_prepared_definitions", "("] {
                    return false;
                }
                let parameters = matching_token(tokens, at + 2, "(", ")");
                let Some((open, "{")) = declaration_delimiter(tokens, parameters + 1) else {
                    return false;
                };
                let close = matching_token(tokens, open, "{", "}");
                let expected = production_rust_code_tokens(
                    "if !prepared.binders.is_empty() || prepared.globals.len() != prepared.quantifiers.len() {
                         return Err(invalid_state());
                     }
                     for (binder, quantified) in std::mem::take(&mut prepared.quantifiers) {
                         prepared.context.set_quantified(binder, quantified)?;
                     }
                     self.monomorphic_recursive.clear();
                     let globals = std::mem::take(&mut prepared.globals);
                     let context = std::mem::take(&mut prepared.context);
                     Ok((globals, context))",
                );
                open < index && index < close && tokens[open + 1..close] == expected
            });
        let prefix = &tokens[index.saturating_sub(12)..index];
        let immediately_discarded = immediately_discarded_member(path, owner, tokens, index);
        if prefix.ends_with(&["(", "&", "mut"])
            && prefix
                .iter()
                .any(|token| matches!(*token, "take" | "replace" | "swap"))
            && !immediately_discarded
            && !quantified_owner_transfer
            && !enclosing_struct_literal(tokens, index).is_some_and(|destination| {
                let destination = if destination == "Self" {
                    enclosing_impl_owner(tokens, index).unwrap_or(destination)
                } else {
                    destination
                };
                custom_drop_owners.contains(destination)
            })
            && enclosing_single_argument_owner(tokens, index, custom_drop_owners, path, owner)
                .is_none()
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
            "struct Type(Box<Type>); enum Kind { Type, EffectRow, Arrow(Box<Kind>, Box<Kind>) }",
        ));
    }
    if !sources.iter().any(|(path, _)| *path == "src/source.rs") {
        fields.extend(parse_top_level_fields(
            "src/source.rs",
            "struct Origin(Box<Origin>);",
        ));
    }
    fields.extend(fields_from_sources(sources));
    let recursive_fields = recursively_unsafe_backing_fields(&fields, sources);
    let custom_drop_owners = sources
        .iter()
        .flat_map(|(_, source)| custom_drop_owner_names(&production_rust_code_tokens(source)))
        .collect::<BTreeSet<_>>();

    let mut violations = Vec::new();
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
            // Report independent owner failures together so one defect cannot
            // hide another source file until the next build.
            let checked = std::panic::catch_unwind(|| {
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
            });
            if let Err(failure) = checked {
                let message = failure
                    .downcast_ref::<String>()
                    .map(String::as_str)
                    .or_else(|| failure.downcast_ref::<&str>().copied())
                    .unwrap_or("owner guard panicked without a diagnostic");
                violations.push(format!("{path}::{owner}: {message}"));
            }
        }
    }
    assert!(
        violations.is_empty(),
        "automatic owner API violations:\n{}",
        violations.join("\n"),
    );
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
        (
            "unrelated preceding discard cannot authorize replacement",
            "src/guard.rs",
            "struct Guard { value: Type } \
             impl Drop for Guard { fn drop(&mut self) {} } \
             use std::mem::replace; \
             fn discard_previous(value: Type) {} \
             fn bypass(owner: &mut Guard, previous: Type) { \
                 discard_previous(previous); \
                 replace(&mut owner.value, Type::Unit); }",
            &["Guard"][..],
        ),
        (
            "bare boxed replacement is not an owning transfer",
            "src/guard.rs",
            "struct Guard { values: Box<[Type]> } \
             impl Drop for Guard { fn drop(&mut self) {} } \
             fn bypass(owner: &mut Guard, values: Box<[Type]>) { \
                 std::mem::replace(&mut owner.values, values); }",
            &["Guard"][..],
        ),
        (
            "a named container discard must consume every displaced value",
            "src/guard.rs",
            "struct Guard { effects: Box<[Type]> } \
             impl Drop for Guard { fn drop(&mut self) {} } \
             fn discard_resolved_effects_iteratively(effects: Box<[Type]>) { \
                 effects.into_vec().into_iter().next(); } \
             fn bypass(owner: &mut Guard, effects: Box<[Type]>) { \
                 discard_resolved_effects_iteratively( \
                     std::mem::replace(&mut owner.effects, effects)); }",
            &["Guard"][..],
        ),
        (
            "control handoff without empty-slot assertion",
            "src/eval/machine.rs",
            "struct Machine { control: Option<Type> } \
             impl Drop for Machine { fn drop(&mut self) {} } \
             impl Machine { fn apply(&mut self, transition: Transition) { \
                 self.control = Some(transition.control); } }",
            &["Machine"][..],
        ),
        (
            "intervening control mutation invalidates empty-slot proof",
            "src/eval/machine.rs",
            "struct Machine { control: Option<Type> } \
             impl Drop for Machine { fn drop(&mut self) {} } \
             impl Machine { fn apply(&mut self, transition: Transition) { \
                 assert!(self.control.is_none()); \
                 self.control = Some(Type::Unit); \
                 self.control = Some(transition.control); } }",
            &["Machine"][..],
        ),
        (
            "another field cannot use the control-slot precondition",
            "src/eval/machine.rs",
            "struct Machine { control: Option<Type>, other: Type } \
             impl Drop for Machine { fn drop(&mut self) {} } \
             impl Machine { fn apply(&mut self, transition: Transition) { \
                 assert!(self.control.is_none()); \
                 self.other = transition.control; } }",
            &["Machine"][..],
        ),
        (
            "unqualified opaque-family consumer is not authenticated",
            "src/core/dialect.rs",
            "struct CoreBuilder { effects: Type } \
             impl Drop for CoreBuilder { fn drop(&mut self) {} } \
             fn bypass(owner: &mut CoreBuilder, row: Type) { \
                 discard_effects(std::mem::replace(&mut owner.effects, F::store_effects(row))); }",
            &["CoreBuilder"][..],
        ),
        (
            "another family cannot consume the Core carrier",
            "src/core/dialect.rs",
            "struct CoreBuilder { effects: Type } \
             impl Drop for CoreBuilder { fn drop(&mut self) {} } \
             fn bypass(owner: &mut CoreBuilder, row: Type) { \
                 Other::discard_effects(std::mem::replace(&mut owner.effects, F::store_effects(row))); }",
            &["CoreBuilder"][..],
        ),
        (
            "projected replacement is not whole-carrier disposal",
            "src/core/dialect.rs",
            "struct CoreBuilder { effects: Type } \
             impl Drop for CoreBuilder { fn drop(&mut self) {} } \
             fn bypass(owner: &mut CoreBuilder, row: Type) { \
                 F::discard_effects(std::mem::replace(&mut owner.effects, F::store_effects(row)).field); }",
            &["CoreBuilder"][..],
        ),
        (
            "a nested family path is not the exact Core family",
            "src/core/dialect.rs",
            "struct CoreBuilder { effects: Type } \
             impl Drop for CoreBuilder { fn drop(&mut self) {} } \
             fn bypass(owner: &mut CoreBuilder, row: Type) { \
                 Other::F::discard_effects(std::mem::replace(&mut owner.effects, F::store_effects(row))); }",
            &["CoreBuilder"][..],
        ),
        (
            "another owner cannot use the observation transfer",
            "src/eval/machine.rs",
            "struct OtherMachine { heap: Vec<Type> } \
             impl Drop for OtherMachine { fn drop(&mut self) {} } \
             struct ObservedHeap { cells: Vec<Type> } \
             impl Drop for ObservedHeap { fn drop(&mut self) {} } \
             impl OtherMachine { fn run_loop(&mut self) { \
                 ObservedHeap::with_root_completion(Arc::clone(self.program.registry()), std::mem::take(&mut self.heap), self.root_completion.take(),); } }",
            &["OtherMachine", "ObservedHeap"][..],
        ),
        (
            "a different heap argument is not the observation transfer",
            "src/eval/machine.rs",
            "struct Machine { heap: Vec<Type> } \
             impl Drop for Machine { fn drop(&mut self) {} } \
             struct ObservedHeap { cells: Vec<Type> } \
             impl Drop for ObservedHeap { fn drop(&mut self) {} } \
             impl Machine { fn run_loop(&mut self) { \
                 ObservedHeap::with_root_completion(Arc::clone(self.program.registry()), self.root_completion.take(), std::mem::take(&mut self.heap),); } }",
            &["Machine", "ObservedHeap"][..],
        ),
        (
            "a projected heap is not the whole observation transfer",
            "src/eval/machine.rs",
            "struct Machine { heap: Vec<Type> } \
             impl Drop for Machine { fn drop(&mut self) {} } \
             struct ObservedHeap { cells: Vec<Type> } \
             impl Drop for ObservedHeap { fn drop(&mut self) {} } \
             impl Machine { fn run_loop(&mut self) { \
                 ObservedHeap::with_root_completion(Arc::clone(self.program.registry()), std::mem::take(&mut self.heap).into_iter().skip(1).collect(), self.root_completion.take(),); } }",
            &["Machine", "ObservedHeap"][..],
        ),
        (
            "partial frame drain is not a whole continuation transfer",
            "src/eval/machine.rs",
            "struct Machine { frames: Vec<Type> } \
             impl Drop for Machine { fn drop(&mut self) {} } \
             struct CapturedContinuation { frames: Vec<Type> } \
             impl Drop for CapturedContinuation { fn drop(&mut self) {} } \
             impl Machine { fn capture_from(&mut self, selected: usize) { \
                 let mut frames = Vec::new(); \
                 frames.extend(self.frames.drain(selected..).take(1)); self.captured_cells = retained; Ok(CapturedContinuation { frames }); } }",
            &["Machine", "CapturedContinuation"][..],
        ),
        (
            "another consumer cannot own the captured frames",
            "src/eval/machine.rs",
            "struct Machine { frames: Vec<Type> } \
             impl Drop for Machine { fn drop(&mut self) {} } \
             struct CapturedContinuation { frames: Vec<Type> } \
             impl Drop for CapturedContinuation { fn drop(&mut self) {} } \
             impl Machine { fn capture_from(&mut self, selected: usize) { \
                 let mut frames = Vec::new(); \
                 discard_frames(self.frames.drain(selected..)); self.captured_cells = retained; Ok(CapturedContinuation { frames }); } }",
            &["Machine", "CapturedContinuation"][..],
        ),
        (
            "post-drain error is not an infallible ownership handoff",
            "src/eval/machine.rs",
            "struct Machine { frames: Vec<Type> } \
             impl Drop for Machine { fn drop(&mut self) {} } \
             struct CapturedContinuation { frames: Vec<Type> } \
             impl Drop for CapturedContinuation { fn drop(&mut self) {} } \
             impl Machine { fn capture_from(&mut self, selected: usize) { \
                 let mut frames = Vec::new(); \
                 frames.extend(self.frames.drain(selected..)); may_fail()?; self.captured_cells = retained; Ok(CapturedContinuation { frames }); } }",
            &["Machine", "CapturedContinuation"][..],
        ),
        (
            "quantifier transfer must use the owning context recipient",
            "src/elaborate.rs",
            "struct PreparedGlobals { quantifiers: HashMap<u32, Box<[Kind]>> } \
             impl Drop for PreparedGlobals { fn drop(&mut self) {} } \
             struct TypeContext { kinds: Vec<Kind> } \
             impl Drop for TypeContext { fn drop(&mut self) {} } \
             impl Elaborator { fn finish_prepared_definitions(&mut self, mut prepared: PreparedGlobals) { \
                 if !prepared.binders.is_empty() || prepared.globals.len() != prepared.quantifiers.len() { \
                     return Err(invalid_state()); } \
                 for (binder, quantified) in std::mem::take(&mut prepared.quantifiers) { \
                     prepared.context.ignore_quantified(binder, quantified)?; } \
                 self.monomorphic_recursive.clear(); \
                 let globals = std::mem::take(&mut prepared.globals); \
                 let context = std::mem::take(&mut prepared.context); \
                 Ok((globals, context)) } }",
            &["PreparedGlobals", "TypeContext"][..],
        ),
        (
            "quantifier transfer must retain the entire map",
            "src/elaborate.rs",
            "struct PreparedGlobals { quantifiers: HashMap<u32, Box<[Kind]>> } \
             impl Drop for PreparedGlobals { fn drop(&mut self) {} } \
             struct TypeContext { kinds: Vec<Kind> } \
             impl Drop for TypeContext { fn drop(&mut self) {} } \
             impl Elaborator { fn finish_prepared_definitions(&mut self, mut prepared: PreparedGlobals) { \
                 if !prepared.binders.is_empty() || prepared.globals.len() != prepared.quantifiers.len() { \
                     return Err(invalid_state()); } \
                 for (binder, quantified) in std::mem::take(&mut prepared.quantifiers).into_iter().take(1) { \
                     prepared.context.set_quantified(binder, quantified)?; } \
                 self.monomorphic_recursive.clear(); \
                 let globals = std::mem::take(&mut prepared.globals); \
                 let context = std::mem::take(&mut prepared.context); \
                 Ok((globals, context)) } }",
            &["PreparedGlobals", "TypeContext"][..],
        ),
        (
            "quantifier transfer must retain the complete quantified value",
            "src/elaborate.rs",
            "struct PreparedGlobals { quantifiers: HashMap<u32, Box<[Kind]>> } \
             impl Drop for PreparedGlobals { fn drop(&mut self) {} } \
             struct TypeContext { kinds: Vec<Kind> } \
             impl Drop for TypeContext { fn drop(&mut self) {} } \
             impl Elaborator { fn finish_prepared_definitions(&mut self, mut prepared: PreparedGlobals) { \
                 if !prepared.binders.is_empty() || prepared.globals.len() != prepared.quantifiers.len() { \
                     return Err(invalid_state()); } \
                 for (binder, quantified) in std::mem::take(&mut prepared.quantifiers) { \
                     prepared.context.set_quantified(binder, quantified.field)?; } \
                 self.monomorphic_recursive.clear(); \
                 let globals = std::mem::take(&mut prepared.globals); \
                 let context = std::mem::take(&mut prepared.context); \
                 Ok((globals, context)) } }",
            &["PreparedGlobals", "TypeContext"][..],
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
fn narrow_owner_guard_accepts_proven_immediate_box_and_map_disposal() {
    let source = "
        struct ResolvedEffectDeclaration { ty: Type }
        struct NonMaterializedNominalKindFact { ty: Type }
        impl Drop for NonMaterializedNominalKindFact { fn drop(&mut self) {} }
        struct Guard {
            effects: Box<[ResolvedEffectDeclaration]>,
            facts: HashMap<u32, NonMaterializedNominalKindFact>,
        }
        impl Drop for Guard { fn drop(&mut self) {} }
        fn discard_resolved_effects_iteratively(effects: Box<[ResolvedEffectDeclaration]>) {
            for effect in effects.into_vec() { discard_resolved_effect_iteratively(effect); }
        }
        fn discard_non_materialized_nominal_kind_facts(
            facts: HashMap<u32, NonMaterializedNominalKindFact>,
        ) {
            for fact in facts.into_values() { discard_non_materialized_nominal_kind_fact(fact); }
        }
        impl Guard {
            fn replace(&mut self, effects: Box<[ResolvedEffectDeclaration]>,
                facts: HashMap<u32, NonMaterializedNominalKindFact>) {
                discard_resolved_effects_iteratively(
                    std::mem::replace(&mut self.effects, effects,),);
                discard_non_materialized_nominal_kind_facts(
                    std::mem::replace(&mut self.facts, facts,));
            }
        }";
    assert_automatic_iterative_owner_apis_are_narrow(&[("src/guard.rs", source)], &["Guard"]);
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
    rust_tokens_with_literals(source, false)
}

fn rust_tokens_with_literals(source: &str, retain_literals: bool) -> Vec<&str> {
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
            if retain_literals {
                tokens.push(&source[cursor..end]);
            }
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
    String(ash::core::packed::StringNode),
    Intrinsic(ash::core::packed::IntrinsicNode),
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
    NewtypeConversion(NewtypeConversionNode),
    LocalNominalScope(ash::core::LocalNominalScopeNode),
    TypeAbstraction(TypeAbstractionNode),
    TypeApplication(TypeApplicationNode),
}

fn assemble_shadow(expression: &TypedExpr) -> ShadowTypedExpr {
    let kind = match &expression.kind {
        PureExprKind::Value(value) => ShadowExprKind::Value(match value {
            PureValue::String(node) => ShadowValue::String(node.clone()),
            PureValue::Intrinsic(node) => ShadowValue::Intrinsic(*node),
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
            PureComputation::NewtypeConversion(node) => {
                ShadowPureComputation::NewtypeConversion(*node)
            }
            PureComputation::LocalNominalScope(node) => {
                ShadowPureComputation::LocalNominalScope(*node)
            }
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
        ShadowValue::String(node) => {
            *ty == Type::String && std::str::from_utf8(node.bytes()).is_ok()
        }
        ShadowValue::Intrinsic(node) => *ty == node.expected_type(),
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
        ShadowPureComputation::NewtypeConversion(node) => {
            let Some(owner) = facts.program.registry().nominal(node.owner()) else {
                return false;
            };
            let Some(representation) = owner.representation.as_ref() else {
                return false;
            };
            owner.declaration_kind == ResolvedNominalDeclarationKind::Newtype
                && match node.direction() {
                    NewtypeConversionDirection::Wrap => {
                        facts.node_type(node.child()) == Some(representation)
                            && ty == &Type::Nominal(owner.id)
                    }
                    NewtypeConversionDirection::Unwrap => {
                        facts.node_type(node.child()) == Some(&Type::Nominal(owner.id))
                            && ty == representation
                    }
                }
        }
        ShadowPureComputation::LocalNominalScope(node) => {
            node.owner().is_lexical() && facts.node_type(node.body()) == Some(ty)
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
            ShadowValue::String(_)
            | ShadowValue::Intrinsic(_)
            | ShadowValue::Integer(_)
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
            ShadowPureComputation::NewtypeConversion(node) => vec![node.child()],
            ShadowPureComputation::LocalNominalScope(node) => vec![node.body()],
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
            ShadowValue::String(_)
            | ShadowValue::Intrinsic(_)
            | ShadowValue::Integer(_)
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
            ShadowPureComputation::NewtypeConversion(node) => {
                ShadowTransformPlan::Preserve(vec![node.child()])
            }
            ShadowPureComputation::LocalNominalScope(node) => {
                ShadowTransformPlan::Preserve(vec![node.body()])
            }
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
            ShadowValue::String(_) => "string",
            ShadowValue::Intrinsic(_) => "intrinsic",
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
            ShadowPureComputation::NewtypeConversion(_) => "newtype conversion",
            ShadowPureComputation::LocalNominalScope(_) => "local nominal scope",
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

static NEWTYPE_SHADOW_FIXTURE_IDS: AtomicU64 = AtomicU64::new(0);

fn validated_newtype_shadow_program() -> ValidatedProgram {
    let directory = loop {
        let id = NEWTYPE_SHADOW_FIXTURE_IDS.fetch_add(1, Ordering::Relaxed);
        let candidate =
            std::env::temp_dir().join(format!("ash-newtype-shadow-{}-{id}", std::process::id(),));
        match fs::create_dir(&candidate) {
            Ok(()) => break candidate,
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => panic!("newtype shadow fixture should be creatable: {error}"),
        }
    };
    let entry = directory.join("entry.ash");
    fs::write(
        &entry,
        concat!(
            "newtype Wrapped = Wrapped(Int)\n",
            "main : Unit -> Wrapped\n",
            "main () = Wrapped(42)\n",
        ),
    )
    .expect("newtype shadow fixture should be writable");
    let graph = load_module_graph(&entry, &ModuleRoots::empty())
        .expect("newtype shadow fixture should load");
    let mut checked = Vec::<CheckedModule>::new();
    for module in graph.modules() {
        let dependencies = module
            .dependencies()
            .iter()
            .map(|edge| {
                let dependency = checked
                    .iter()
                    .find(|dependency| dependency.module() == edge.target())
                    .expect("checked dependency should precede importer");
                DependencyExports::new(edge, dependency.exports())
                    .expect("exact defining summary should authenticate")
            })
            .collect::<Vec<_>>();
        checked.push(
            check_module(
                resolve_module(module, &dependencies).expect("newtype Source should resolve"),
            )
            .expect("newtype Source should check"),
        );
    }
    let entry_checked = checked
        .iter()
        .find(|module| module.module() == graph.entry())
        .unwrap();
    let registry = std::sync::Arc::clone(entry_checked.registry());
    let owners = registry
        .nominals()
        .iter()
        .filter(|nominal| nominal.id.module() == graph.entry() && nominal.spelling == "Wrapped")
        .collect::<Vec<_>>();
    let [owner] = owners.as_slice() else {
        panic!("one defining Wrapped nominal")
    };
    assert_eq!(
        owner.declaration_kind,
        ResolvedNominalDeclarationKind::Newtype
    );
    let owner = owner.id;
    let linked = link_modules(checked, graph.entry()).expect("complete Source graph should link");
    let linked = validate_interface_evidence(linked)
        .expect("newtype shadow fixture has no interface evidence");
    let mut elaborator =
        EffectElaborator::for_module_program(&linked).expect("newtype shadow namespace should fit");
    let typed = elaborator
        .synthesize_effect_module_program(&linked)
        .expect("newtype Source should lower to Effect Core");
    let unchecked = elaborator
        .finish(typed.node)
        .expect("newtype shadow Core should finish");
    let sources = graph
        .modules()
        .iter()
        .map(|module| module.source())
        .collect::<Vec<_>>();
    let module_sources = graph
        .modules()
        .iter()
        .map(|module| (module.id(), module.source().id()))
        .collect::<Vec<_>>();
    let source_program = ash::core::validate_effect_modules(unchecked, &sources, &module_sources)
        .expect("complete Source should independently validate");
    assert_eq!(
        source_program.node(source_program.root()).unwrap().ty,
        Type::Nominal(owner)
    );
    assert_eq!(
        ash::eval::evaluate_effect(&source_program)
            .unwrap()
            .value
            .to_string(),
        "42"
    );
    // The closed Pure-family shadow control is an isolated erased conversion,
    // authenticated by the original defining registry, rather than Source lowering.
    let source = graph.module(graph.entry()).unwrap().source();
    let start = source.text().find("Wrapped(42)").unwrap();
    let span = source
        .span(
            ByteRange::new(
                start.try_into().unwrap(),
                (start + "Wrapped(42)".len()).try_into().unwrap(),
            )
            .unwrap(),
        )
        .unwrap();
    let origin = Origin::Source(span);
    let mut builder = CoreBuilder::with_registry(registry);
    let value = builder
        .integer(
            Integer::parse_decimal("42").unwrap(),
            Type::Int,
            origin.clone(),
        )
        .unwrap();
    let root = builder
        .newtype_conversion(
            owner,
            NewtypeConversionDirection::Wrap,
            value,
            Type::Nominal(owner),
            origin,
        )
        .unwrap();
    let program =
        ash::core::validate_modules(builder.finish(root).unwrap(), &sources, &module_sources)
            .expect("the original registry should authenticate the isolated Pure conversion");
    assert_eq!(
        ash::eval::evaluate(&program).unwrap().value.to_string(),
        "42"
    );
    drop(graph);
    fs::remove_dir_all(directory).expect("newtype shadow fixture should clean up");
    program
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
fn effect_dialect_adds_one_operation_family_without_changing_pure_families() {
    assert_eq!(AshEffectDialect::NAME, "ash.effect");
    let source = include_str!("../src/core/dialect.rs");
    assert!(!production_rust_code_tokens(source).contains(&"EffectOperation"));
    let _: Option<EffectExprKind> = None;
    let _: Option<EffectOperation> = None;
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

    let newtype_program = validated_newtype_shadow_program();
    let newtype_facts = ShadowFacts {
        program: &newtype_program,
        binders: &HashMap::new(),
    };
    let mut pending = vec![newtype_program.root()];
    let mut conversion_count = 0;
    while let Some(id) = pending.pop() {
        let expression = newtype_program
            .node(id)
            .expect("newtype shadow node should remain validated");
        pending.extend(
            (0..expression.kind.child_count()).filter_map(|index| expression.kind.child_at(index)),
        );
        if !matches!(
            expression.kind,
            PureExprKind::Computation(PureComputation::NewtypeConversion(_))
        ) {
            continue;
        }
        let shadow = assemble_shadow(expression);
        assert!(validate_shadow(&shadow, &newtype_facts));
        assert_eq!(
            transform_shadow(&shadow),
            ShadowTransformPlan::Preserve(traverse_shadow(&shadow))
        );
        assert_eq!(consume_shadow(&shadow), "newtype conversion");
        conversion_count += 1;
    }
    assert_eq!(conversion_count, 1);

    let mock = mock_shadow();
    assert!(validate_shadow(&mock, &facts));
    assert_eq!(traverse_shadow(&mock), Vec::<NodeId>::new());
    assert_eq!(
        transform_shadow(&mock),
        ShadowTransformPlan::ReplaceWithMockUnit
    );
    assert_eq!(consume_shadow(&mock), "mock");
}
