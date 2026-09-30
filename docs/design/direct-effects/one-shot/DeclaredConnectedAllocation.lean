import DeclaredConnectedCaptureSplit

/-! Allocate a concrete continuation interface at the actual source cut. The
contract retains the selected declaration's effect bounds and the source's
exact demand/requirement indices. Independent usage allocation and the closing
summary are separate inputs to this local construction; it does not assert
that a disposing capture has an admitted closing plan.
-/
namespace Ash.OneShot.DeclaredConnectedSources
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals CoherentSourceTypes
open RecursiveRequirements (Requirements Store evaluate)
open OwnerPhaseTransitions (spendAll)

theorem allocate_capture_interfaces
    (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables actions world whole input output demand requirements records incoming outgoing)
    (selected : ClauseAt operation handler.clauses parameter binder body)
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase) = some row)
    (operationKnown : operations requested operation = some (argument, input))
    (fresh : contracts owner = none)
    (actionExtension : Syntax.UsageExtension actions nextActions)
    (actionKnown : nextActions owner = some body.requiredActions) :
    ∃ (answer : Value) (residual : List Instance) (capDemand tailDemand : List Nat)
      (capReq : Requirements capDemand) (tailReq : Requirements tailDemand)
      (capRecords tailRecords : Store) (resumeEffects closeEffects : List Instance),
      demand = capDemand ++ tailDemand ∧ records = capRecords ++ tailRecords ∧
      (∀ store receiving before, evaluate store receiving before requirements =
        merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) before capReq)
          (evaluate store receiving (spendAll before capDemand) tailReq)) ∧
      ∀ (captureRow : Footprint) (closeDemand : List Nat) (closeRow : Option Footprint),
        closeDemand.Perm capDemand →
        let contract : Owners.Contract := ⟨input, answer, ProtectionContexts.protectedMode capture.erase,
          capDemand, captureRow, closeDemand, closeRow, resumeEffects, closeEffects⟩
        DeclaredSources.Body operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
          (Environment.empty.extend parameter argument) body answer ⟨owner, contract, offered.dispose, row⟩ ∧
        Segment operations policy (contracts.insert owner contract) tables nextActions world
          (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
          answer output tailDemand (.sequence (.spent owner) tailReq)
          ((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) residual outgoing := by
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, resumeEffects, closeEffects,
    annotation, scope, saved, savedInterface, waiting, resume, close, family, sameDemand, sameRecords, evaluation⟩ :=
    capture_interfaces cut source selected found available operationKnown
  refine ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords,
    resumeEffects, closeEffects, sameDemand, sameRecords, evaluation, ?_⟩
  intro captureRow closeDemand closeRow balanced
  let contract : Owners.Contract := ⟨input, answer, ProtectionContexts.protectedMode capture.erase,
    capDemand, captureRow, closeDemand, closeRow, resumeEffects, closeEffects⟩
  have extension := Owners.insert_extends (contract := contract) contracts fresh
  have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
  refine ⟨family owner contract fresh rfl rfl rfl rfl rfl balanced, ?_⟩
  rw [sameRecords]
  exact Segment.live known actionKnown (ScopedPorts.erase_embed_port input.port).symm annotation
    (ScopedPorts.effect_scope_known_extension scope (Owners.port_contracts_extension extension)) rfl
    (DeclaredSourceFrames.segment_extension saved extension)
    (fun used => ((savedInterface used).contract_extension extension).action_extension actionExtension)
    ((waiting.contract_extension extension).action_extension actionExtension) resume close (List.Subset.refl _)

end Ash.OneShot.DeclaredConnectedSources

#print axioms Ash.OneShot.DeclaredConnectedSources.allocate_capture_interfaces
