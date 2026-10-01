import CoreCallablePairedOrigin
import CoreCallableCallerBarriers
namespace Ash.OneShot.CoreCallableRuntimeBindingOrigins
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreValueRelation CoreCallablePairedOrigin CoreCallableCallerBarriers
open CoreCallableContractAdmission CoreCallableContractSource CoreCallableReceiverRefinement
open SourceDeclarationPlans SourcePlanSignatures SourceDependencyAnnotations
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
local instance : SourcePlannedChecks.DeclarationPolicy :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

/-- Recover successful SAME original initializer outputs, never a new annotation. -/
theorem Origins.nearest_initializer
    (origin : Origins registry declarations outward owners world allowed scope receiver root body
      ((parameter,input) :: richBindings) storageBindings lexical (record :: records)) :
    record.name = parameter ∧
    ∃ beforeRich beforeStorage beforeLexical demand, ∃ requirements : RecursiveRequirements.Requirements demand,
      ∃ dependencies, ∃ plan : Plan dependencies, ∃ rows : Rows (signature plan),
      ∃ source : IndexedSource registry outward owners world allowed scope
        (CoreCallableStaticProducer.environment beforeRich) record.initializer input demand requirements plan rows,
        beforeRich = richBindings ∧
        Authenticated registry outward source beforeLexical receiver ∧
        CallableContracts.Derives declarations (CoreCallableReturnStorageProducer.environment beforeStorage)
          world .none record.initializer record.expected ∧
        record.expected.storageOf ⊆ receiver ∧
        storageBindings = CoreCallableReturnStorageProducer.extend beforeStorage parameter record.expected ∧
        lexical = beforeLexical.extend parameter receiver := by
  cases origin with
  | @bind parameter initializer body beforeRich beforeStorage beforeLexical beforeRecords richInput initialDemand initialReq dependencies initialPlan initialRows storageInput storageAnnotation previous source authenticated storage bounded =>
    exact ⟨rfl,richBindings,beforeStorage,beforeLexical,initialDemand,initialReq,dependencies,initialPlan,initialRows,source,rfl,authenticated,storage,bounded,rfl,rfl⟩

/-- Actual value-ready installation has no nonvalue focus. The target bind
remains unchanged during this administrative Core entry. -/
theorem value_ready_bind_enter {base : CoreMachine.State} {plain : PlainData}
    (history : CoreCallableGeneralHistory.GeneralHistory graph base.heap physical target)
    (scopeOrigin : CoreCallableReachableResume.CurrentScopeOrigin graph owners plain.scope physical)
    (postorder : CoreTranslationFuel.Postorder graph)
    (lineage : CoreCallableSiteLineage.SiteLineage graph owners plain.scope bindSite)
    (known : graph.node bindSite = some node) (kind : node.kind = .bind binder initializer bodySite)
    (it : CoreTranslation.translateFuel graph fuel owners initializer = .ok rawInitializer)
    (bt : CoreTranslation.translateFuel graph fuel owners bodySite = .ok rawBody)
    (current : EnvCloses graph owners base.heap environment
      (.bind binder.id rawInitializer rawBody) (.bind binder.id initializerCode suffix))
    (closed : ClosedValue initializerCode) (ready : ClosedExcept binder.id suffix)
    (context : plain.context = .bind binder.id suffix) :
    CoreMachine.next graph {base with control := .evaluate bindSite environment,frames := physical} =
      .stepped {base with control := .evaluate initializer environment, frames := .bind binder.id bodySite environment :: physical,observations := base.observations ++ [.entered bindSite]} ∧
    ∃ _saved : CoreCallableSiteLineage.SavedBindSite graph owners base.heap binder.id bodySite environment plain physical,
    ∃ _installed : CoreCallableGeneralHistory.GeneralHistory graph base.heap
      (.bind binder.id bodySite environment :: physical) (.push (.plain plain) target),
    ClosedValue initializerCode ∧
    CoreTranslation.translateFuel graph fuel owners initializer = .ok rawInitializer ∧
    EnvCloses graph owners base.heap environment rawInitializer initializerCode := by
  obtain ⟨initial,saved⟩ := CoreOrdinaryCompletion.bind_components current
  have frame : CoreStrictFrames.PlainFrameRel graph owners base.heap (.bind binder.id bodySite environment) plain := by
    change CoreStrictFrames.FrameRel graph owners base.heap _ plain.context
    rw [context]; exact .bind bt saved ready
  have actual : CoreMachine.next graph {base with control := .evaluate bindSite environment,frames := physical} =
      .stepped {base with control := .evaluate initializer environment, frames := .bind binder.id bodySite environment :: physical,observations := base.observations ++ [.entered bindSite]} := by
    cases node with
    | mk original type effects source nodeKind => cases kind; simp only [CoreMachine.next,known]
  exact ⟨actual,⟨⟨frame,scopeOrigin⟩,(CoreCallableSiteLineage.bind_sites lineage postorder known kind).2⟩,
    .push (.ordinary frame) (by trivial) history,closed,it,initial⟩

/-- Derive the returned original initializer from the actual checked lambda
entry, then perform actual bind return and one positive target bind reduction.
Closed original readiness is CURRENT; a future ValueRel is never an input. -/
theorem checked_lambda_initializer_binding {base : CoreMachine.State} {plain : PlainData}
    (history : CoreCallableGeneralHistory.GeneralHistory graph base.heap physical target)
    (scopeOrigin : CoreCallableReachableResume.CurrentScopeOrigin graph coreOwners plain.scope physical)
    (postorder : CoreTranslationFuel.Postorder graph)
    (lineage : CoreCallableSiteLineage.SiteLineage graph coreOwners plain.scope bindSite)
    (known : graph.node bindSite = some node) (kind : node.kind = .bind binder initializer bodySite)
    (it : CoreTranslation.translateFuel graph fuel coreOwners initializer = .ok (.lambda certificate.parameter certificate.rawBody))
    (bt : CoreTranslation.translateFuel graph fuel coreOwners bodySite = .ok rawBody)
    (current : EnvCloses graph coreOwners base.heap environment
      (.bind binder.id (.lambda certificate.parameter certificate.rawBody) rawBody) (.bind binder.id initializerCode suffix))
    (closed : ClosedValue initializerCode) (ready : ClosedExcept binder.id suffix)
    (context : plain.context = .bind binder.id suffix)
    (checked : CoreCallableChecks.checkAmbient graph initializer coreOwners = .ok certificate)
    (origin : Origins registry declarations outward richOwners world allowed plain.scope receiver root body
      ((binder.id,input) :: richBindings) storageBindings lexical (record :: records))
    (same : record.initializer = initializerCode) (bodySame : body = suffix) :
    record.initializer = initializerCode ∧ body = suffix ∧
    ClosedValue record.initializer ∧ record.name = binder.id ∧
    (∃ beforeRich beforeStorage beforeLexical demand, ∃ requirements : RecursiveRequirements.Requirements demand,
      ∃ dependencies, ∃ plan : Plan dependencies, ∃ rows : Rows (signature plan),
      ∃ source : IndexedSource registry outward richOwners world allowed plain.scope
        (CoreCallableStaticProducer.environment beforeRich) record.initializer input demand requirements plan rows,
        beforeRich = richBindings ∧ Authenticated registry outward source beforeLexical receiver ∧
        CallableContracts.Derives declarations (CoreCallableReturnStorageProducer.environment beforeStorage)
          world .none record.initializer record.expected ∧
        record.expected.storageOf ⊆ receiver ∧
        storageBindings = CoreCallableReturnStorageProducer.extend beforeStorage binder.id record.expected ∧
        lexical = beforeLexical.extend binder.id receiver) ∧
    ∃ entered evaluated completed : CoreMachine.State,
      CoreMachine.next graph {base with control := .evaluate bindSite environment,frames := physical} = .stepped entered ∧
      CoreMachine.next graph entered = .stepped evaluated ∧
      CoreMachine.next graph evaluated = .stepped completed ∧
      CoreAdministrativeSteps.rank graph evaluated < CoreAdministrativeSteps.rank graph entered ∧
      entered.control = .evaluate initializer environment ∧
      evaluated.control = .returned (.closure certificate.parameter certificate.body environment) ∧
      completed.control = .evaluate bodySite (.binding binder.id (.closure certificate.parameter certificate.body environment) environment) ∧
      completed.frames = physical ∧
      ValueRel graph coreOwners evaluated.heap (.closure certificate.parameter certificate.body environment) record.initializer ∧
      RawStep ⟨.bind binder.id record.initializer suffix,plain.scope,target⟩
        ⟨suffix.subst binder.id record.initializer,plain.scope,target⟩ [] [] ∧
      EnvCloses graph coreOwners completed.heap (.binding binder.id (.closure certificate.parameter certificate.body environment) environment)
        rawBody (suffix.subst binder.id record.initializer) ∧
      CoreCallableSiteLineage.SiteLineage graph coreOwners plain.scope bodySite ∧
      CoreCallableReachableResume.CurrentScopeOrigin graph coreOwners plain.scope physical ∧
      (∃ retained : CoreCallableGeneralHistory.GeneralHistory graph completed.heap physical target,HEq retained history) := by
  obtain ⟨name,initialOrigin⟩ := Origins.nearest_initializer origin
  obtain ⟨entry,saved,_,_,_,initialSaved⟩ := value_ready_bind_enter history scopeOrigin postorder lineage known kind it bt current closed ready context
  let entered : CoreMachine.State := {base with control := .evaluate initializer environment, frames := .bind binder.id bodySite environment :: physical, observations := base.observations ++ [.entered bindSite]}
  let evaluated : CoreMachine.State := {entered with control := .returned (.closure certificate.parameter certificate.body environment), observations := entered.observations ++ [.entered initializer]}
  let completed : CoreMachine.State := {evaluated with control := .evaluate bodySite (.binding binder.id (.closure certificate.parameter certificate.body environment) environment),frames := physical}
  obtain ⟨witness,_⟩ := CoreCallableChecks.checked_lambda_evaluate (base := entered) checked initialSaved closed
    (.bind binder.id bodySite environment :: physical)
  obtain ⟨value,returned,related⟩ := witness.returned
  have valueSame : value = .closure certificate.parameter certificate.body environment := by
    injection returned.symm
  subst value
  have bodySaved := (CoreOrdinaryCompletion.bind_components current).2
  obtain ⟨actual,step,closing,_⟩ := CoreStrictSteps.bind_complete (base := evaluated) bt bodySaved related ready physical plain.scope target
  exact ⟨same,bodySame,by simpa only [same] using related.closed,name,initialOrigin,
    entered,evaluated,completed,entry,witness.core,actual,witness.decreasing,rfl,rfl,rfl,rfl,
    by simpa only [same] using related,by simpa only [same] using step,
    by simpa only [same] using closing,saved.site,scopeOrigin,history,HEq.rfl⟩

#print axioms Origins.nearest_initializer
#print axioms value_ready_bind_enter
#print axioms checked_lambda_initializer_binding
end Ash.OneShot.CoreCallableRuntimeBindingOrigins
