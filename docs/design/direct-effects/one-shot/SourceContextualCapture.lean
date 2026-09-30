import SourceContextualForest
import SourceContextualRechecking

/-! Join contextual stored certificates to the rich source decomposition at
one actual handler cut. This reuses the established source, declaration and
allocation proofs; no independent annotation witness is selected. -/
namespace Ash.OneShot.SourceContextualCapture
open ScopedExpressions ScopedExecution ProtectionContracts
open ProtectionResiduals
open SourceDependencyCapture
open SourceDependencyAnnotations (Dependencies)
open SourceDependencySchemes (Checked Retained)
abbrev Receiving := SourceDependencyCapture.Scope

/-- Exact lookup aligns the stored and typed decompositions. The selected
clause and new live forest retain the same contextual certificate. -/
theorem capture_checked_interfaces
    (cut : HandlerCut requested whole capture tail handler)
    (source : SourceDependencyFrames.Segment operations policy contracts tables families actions world
      whole input output demand requirements records wholeScope incoming outgoing)
    (certificates : SourceContextualForest.Forest outward tables families whole wholeScope .nil)
    (checked : Checked outward actions phases world (.request requested operation) wholeScope)
    (retained : Retained outward actions phases world wholeScope .nil)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase) = some row)
    (operationKnown : operations requested operation = some (argument, input))
    (fresh : actions owner = none) (consumed : phases owner = .consumed) :
    ∃ (answer : SourceDependencyAnnotations.Value) (residual : List Instance) (capDemand tailDemand : List Nat)
      (capReq : RecursiveRequirements.Requirements capDemand) (tailReq : RecursiveRequirements.Requirements tailDemand)
      (capRecords tailRecords : RecursiveRequirements.Store) (capScope tailScope : Receiving)
      (resumeEffects closeEffects : List Instance) (family : Nat → Dependencies),
      answer.erase.port = ScopedPorts.eraseType handler.answer ∧
      ScopedPorts.EffectScopeKnown contracts.erase.ports handler.scope ∧
      DeclaredSourceFrames.Frame operations.erase policy contracts.erase tables world
        (.handler handler) answer.erase answer.erase [] (.request [] []) ∧
      SourceDependencyFrames.Segment operations policy contracts tables families actions world
        capture input answer capDemand capReq capRecords capScope incoming residual ∧
      SourceDependencyFrames.Segment operations policy contracts tables families actions world
        tail answer output tailDemand tailReq tailRecords tailScope residual outgoing ∧
      wholeScope = capScope.append tailScope ∧ demand = capDemand ++ tailDemand ∧ records = capRecords ++ tailRecords ∧
      (code.requiredActions.resume = true → resumeEffects = residual) ∧
      (code.requiredActions.dispose = true → closeEffects = residual) ∧
      (lookupDependencies operation (families handler)).bind (modeDependencies capScope.held) = some family ∧
      Checked outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.introduce phases owner)
        world (family owner) (.live owner capScope tailScope) ∧
      Retained outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.introduce phases owner)
        world (.live owner capScope tailScope) .nil ∧
      SourceContextualForest.Forest outward tables families
        (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)
        (.live owner capScope tailScope) .nil ∧
      (∀ store receiving before, RecursiveRequirements.evaluate store receiving before requirements =
        ProtectionResiduals.merge
          (RecursiveRequirements.evaluate store (OwnerPhases.ofStack tables tail ++ receiving) before capReq)
          (RecursiveRequirements.evaluate store receiving (OwnerPhaseTransitions.spendAll before capDemand) tailReq)) ∧
      ∀ (contract : SourceDependencyAnnotations.Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = capScope.held → contract.closeDemand.Perm contract.resumeDemand →
        SourceDependencyAnnotations.Body operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
          (SourceDependencyAnnotations.Environment.empty.extend parameter argument) code answer
          ⟨owner, contract.erase, offered.dispose, row⟩ (family owner) := by
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
    annotation, frame, saved, waiting, scopeSame, demandSame, recordsSame, selection, evaluation⟩ :=
    SourceDependencyFrames.capture_segments cut source
  obtain ⟨storedSaved, storedWaiting, storedSchemes⟩ :=
    certificates.cut_aligned cut (selection operation) found (SourceDependencySchemes.checked_request checked)
  have schemes : SourceContextualClauses.DeclarationsAt outward tailScope handler.clauses (families handler) := by
    simpa only [SourceDependencyProjection.scope_append_nil] using storedSchemes
  have effectSame := ScopedTyping.handler_cut_instance cut
  have scopedCheck : Checked outward actions phases world (.request handler.effectInst operation) (capScope.append tailScope) := by
    simpa only [effectSame, ← scopeSame] using checked
  have scopedRetained : Retained outward actions phases world (capScope.append tailScope) .nil := scopeSame ▸ retained
  have scopedSelection : select handler.effectInst operation (capScope.append tailScope) =
      chosen operation (tables handler) (families handler) capScope tailScope := by
    simpa only [effectSame, ← scopeSame] using selection operation
  have scopedRow : offered.row capScope.held = some row := by simpa only [saved.realizes.held] using available
  have declaration := frame.erase.source
  cases frame with
  | handler scope annotation clauses coverage unique declarations capabilities modes =>
      obtain ⟨actualArgument, actualInput, resumeEffects, closeEffects, family, signature, resume, close, located,
        bodyChecked, liveRetained, body⟩ :=
        SourceContextualClauses.allocate_declared_clause declarations modes schemes selected found scopedRow scopedSelection scopedCheck scopedRetained fresh consumed
      rw [effectSame] at signature
      rcases Prod.mk.inj (Option.some.inj (signature.symm.trans operationKnown)) with ⟨rfl, rfl⟩
      exact ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
        resumeEffects, closeEffects, family, annotation, scope, declaration, saved, waiting, scopeSame, demandSame, recordsSame, resume, close, located,
        bodyChecked, liveRetained, SourceContextualForest.Forest.live storedSaved storedWaiting, evaluation, body⟩


/-- The common allocation theorem supplies the actual step, exact owner
increment, rich payload substitution and independent resume/closing interfaces.
Only capture preparation changes to consume the contextual stored forest. -/
theorem allocate_capture_source
    (cut : HandlerCut requested whole capture tail handler)
    (source : SourceDependencyFrames.Segment operations policy contracts tables families actions world
      whole input output demand requirements records wholeScope incoming outgoing)
    (certificates : SourceContextualForest.Forest outward tables families whole wholeScope .nil)
    (checked : Checked outward actions (OwnerPhaseTransitions.available (ownedTickets whole)) world (.request requested operation) wholeScope)
    (retained : Retained outward actions (OwnerPhaseTransitions.available (ownedTickets whole)) world wholeScope .nil)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase) = some row)
    (operationKnown : operations requested operation = some (argument, input))
    (payload : SourceDependencyAnnotations.ValueSummary operations policy contracts world
      SourceDependencyAnnotations.Environment.empty payloadAllowed operand argument)
    (closed : ClosedValue operand)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (layout : DeclaredSourceClosing.Records operations.erase policy contracts.erase tables world whole disposals)
    (closingRecords : SourceDependencySchemes.Closing.Records operations policy contracts tables annotations world whole disposals)
    (annotationBound : SourceDependencySchemes.Closing.Bound annotations wholeScope) (freshAnnotation : annotations owner = none)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (pendingCheck : RecursiveRequirements.Checked (records ++ disposals) []
      (OwnerPhaseTransitions.available (ownedTickets whole)) requirements pendingRow)
    (unique : (ownedTickets whole).Nodup)
    (requestCheck : RecursiveRequirements.Checked (records ++ disposals) (OwnerPhases.ofStack tables whole)
      (OwnerPhaseTransitions.available (ownedTickets whole))
      (.request [] [⟨requested, operation, false⟩]) requestRow) :
    ∃ (answer : SourceDependencyAnnotations.Value) (residual : List Instance) (capDemand tailDemand : List Nat)
      (capReq : RecursiveRequirements.Requirements capDemand) (tailReq : RecursiveRequirements.Requirements tailDemand)
      (capScope tailScope : Receiving) (resumeEffects closeEffects : List Instance) (family : Nat → Dependencies) (captureRow tailRow raw : Footprint)
      (closingRequirements : RecursiveRequirements.Requirements (OwnerClosingSource.retirements plan)),
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩
        ⟨code.subst parameter operand, .ticket binder owner,
          .live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail⟩ [.ticket owner] [] ∧
      ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail) =
        owner :: ownedTickets whole ∧
      (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)).Nodup ∧
      wholeScope = capScope.append tailScope ∧ demand = capDemand ++ tailDemand ∧
      Checked outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)))
        world (family owner) (.live owner capScope tailScope) ∧
      Retained outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)))
        world (.live owner capScope tailScope) .nil ∧
      SourceContextualForest.Forest outward tables families
        (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)
        (.live owner capScope tailScope) .nil ∧
      pendingRow = captureRow ++ tailRow ∧
      RecursiveRequirements.Checked (records ++ disposals) (OwnerPhases.ofStack tables tail)
        (OwnerPhaseTransitions.available (ownedTickets whole)) capReq captureRow ∧
      RecursiveRequirements.Checked (records ++ disposals) []
        (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets whole)) capDemand) tailReq tailRow ∧
      (OwnerClosingSource.retirements plan).Perm capDemand ∧
      let closeRow := RecursiveRequirements.evaluate [] (OwnerPhases.ofStack tables tail)
        (OwnerPhaseTransitions.available (ownedTickets whole)) closingRequirements;
      let contract : SourceDependencyAnnotations.Contract := ⟨input, answer, capScope.held,
          capDemand, captureRow, OwnerClosingSource.retirements plan, closeRow, resumeEffects, closeEffects⟩;
        SourceDependencyAnnotations.Body operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
          SourceDependencyAnnotations.Environment.empty (code.subst parameter operand) answer
          ⟨owner, contract.erase, offered.dispose, row⟩ (family owner) ∧
        SourceDependencyFrames.Segment operations policy (contracts.insert owner contract) tables families
          (actions.insert owner code.requiredActions) world
          (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)
          answer output tailDemand (.sequence (.spent owner) tailReq)
          ((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) (.live owner capScope tailScope) residual outgoing ∧
        let nextAnnotations := fun other => if other = owner then some capScope else annotations other;
        SourceDependencySchemes.Closing.Bound nextAnnotations (.live owner capScope tailScope) ∧
          SourceDependencySchemes.Closing.Template operations policy (contracts.insert owner contract) tables world .none
            plan raw closingRequirements capScope.forClosing ∧
          DeclaredSourceClosing.Records operations.erase policy (contracts.insert owner contract).erase tables world
            (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)
            ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩) :: disposals) ∧
          SourceDependencySchemes.Closing.Records operations policy (contracts.insert owner contract) tables nextAnnotations world
            (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)
            ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩) :: disposals) ∧
          let store := ((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) ++
            ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩) :: disposals);
          RecursiveRequirements.Checked store (OwnerPhases.ofStack tables tail)
            (OwnerPhaseTransitions.available (ownedTickets whole)) capReq captureRow ∧
          RecursiveRequirements.Checked store []
            (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets whole)) capDemand) tailReq tailRow ∧
          RecursiveRequirements.Checked store
            (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail))
            (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)))
            (.invoke ⟨owner, .resume⟩ capDemand []) captureRow ∧
          (∀ closingRow, closeRow = some closingRow → RecursiveRequirements.Checked store
            (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail))
            (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)))
            (.invoke ⟨owner, .dispose⟩ (OwnerClosingSource.retirements plan) []) closingRow) ∧
          ((offered.dispose = true → DeclaredCallbackAdmission.checkClosing (CallableProtectionFrames.contextOf tables tail) outside
            raw (requestRow ++ captureRow) = true) →
            ∃ (clauseDemand : List Nat) (clauseRequirements : RecursiveRequirements.Requirements clauseDemand) (clauseRow : Footprint),
              SourceDependencyAnnotations.Expression operations policy (contracts.insert owner contract) world residual
                (.ticket binder owner) SourceDependencyAnnotations.Environment.empty (code.subst parameter operand)
                answer clauseDemand clauseRequirements (family owner) ∧
              RecursiveRequirements.Checked store
                (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail))
                (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)))
                clauseRequirements clauseRow ∧
              EffectBounds.Covers (requestRow ++ captureRow) clauseRow) := by
  have freshErased : contracts.erase owner = none := by
    simp [SourceDependencyAnnotations.Contracts.erase, freshContract]
  have absent := RecursiveCapture.fresh_unowned source.erase.source.erase freshErased
  have consumed : OwnerPhaseTransitions.available (ownedTickets whole) owner = .consumed := by
    simp [OwnerPhaseTransitions.available, absent]
  have interfaces := capture_checked_interfaces cut source certificates checked retained selected found available operationKnown freshAction consumed
  exact SourceDependencySchemes.allocate_capture_source_from_interfaces cut source interfaces selected found available operationKnown
    payload closed freshContract freshAction layout closingRecords annotationBound freshAnnotation built internal pendingCheck unique requestCheck


end Ash.OneShot.SourceContextualCapture

#print axioms Ash.OneShot.SourceContextualCapture.capture_checked_interfaces

#print axioms Ash.OneShot.SourceContextualCapture.allocate_capture_source


namespace Ash.OneShot.SourceContextualCapture.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyCapture
open SourceDependencyAnnotations (Dependencies)
open SourceDependencyChecks.Lexical (Local Pending)
abbrev Receiving := SourceDependencyCapture.Scope
/-- Exact lookup aligns the stored and typed decompositions. The selected
clause and new live forest retain the same contextual certificate. -/
theorem capture_checked_interfaces
    (cut : HandlerCut requested whole capture tail handler)
    (source : SourceDependencyFrames.LexicalSegment operations policy contracts tables families actions world
      whole input output demand requirements records wholeScope incoming outgoing)
    (certificates : SourceContextualForest.Lexical.Forest outward tables families whole wholeScope .nil)
    (checked : Local outward actions phases world (.request requested operation) wholeScope)
    (retained : Pending outward actions phases world wholeScope .nil)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase) = some row)
    (operationKnown : operations requested operation = some (argument, input))
    (fresh : actions owner = none) (consumed : phases owner = .consumed) :
    ∃ (answer : SourceDependencyAnnotations.Value) (residual : List Instance) (capDemand tailDemand : List Nat)
      (capReq : RecursiveRequirements.Requirements capDemand) (tailReq : RecursiveRequirements.Requirements tailDemand)
      (capRecords tailRecords : RecursiveRequirements.Store) (capScope tailScope : Receiving)
      (resumeEffects closeEffects : List Instance) (family : Nat → Dependencies),
      answer.erase.port = ScopedPorts.eraseType handler.answer ∧
      ScopedPorts.EffectScopeKnown contracts.erase.ports handler.scope ∧
      DeclaredSourceFrames.Frame operations.erase policy contracts.erase tables world
        (.handler handler) answer.erase answer.erase [] (.request [] []) ∧
      SourceDependencyFrames.LexicalSegment operations policy contracts tables families actions world
        capture input answer capDemand capReq capRecords capScope incoming residual ∧
      SourceDependencyFrames.LexicalSegment operations policy contracts tables families actions world
        tail answer output tailDemand tailReq tailRecords tailScope residual outgoing ∧
      wholeScope = capScope.append tailScope ∧ demand = capDemand ++ tailDemand ∧ records = capRecords ++ tailRecords ∧
      (code.requiredActions.resume = true → resumeEffects = residual) ∧
      (code.requiredActions.dispose = true → closeEffects = residual) ∧
      (lookupDependencies operation (families handler)).bind (modeDependencies capScope.held) = some family ∧
      Local outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.introduce phases owner)
        world (family owner) (.live owner capScope tailScope) ∧
      Pending outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.introduce phases owner)
        world (.live owner capScope tailScope) .nil ∧
      SourceContextualForest.Lexical.Forest outward tables families
        (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)
        (.live owner capScope tailScope) .nil ∧
      (∀ store receiving before, RecursiveRequirements.evaluate store receiving before requirements =
        ProtectionResiduals.merge
          (RecursiveRequirements.evaluate store (OwnerPhases.ofStack tables tail ++ receiving) before capReq)
          (RecursiveRequirements.evaluate store receiving (OwnerPhaseTransitions.spendAll before capDemand) tailReq)) ∧
      ∀ (contract : SourceDependencyAnnotations.Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = capScope.held → contract.closeDemand.Perm contract.resumeDemand →
        SourceDependencyAnnotations.Body operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
          (SourceDependencyAnnotations.Environment.empty.extend parameter argument) code answer
          ⟨owner, contract.erase, offered.dispose, row⟩ (family owner) := by
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
    annotation, frame, saved, waiting, scopeSame, demandSame, recordsSame, selection, evaluation⟩ :=
    SourceDependencyFrames.lexical_capture_segments cut source
  obtain ⟨storedSaved, storedWaiting, storedSchemes⟩ :=
    certificates.cut_aligned cut (selection operation) found (Local.request_guard checked)
  have schemes : SourceContextualClauses.Lexical.DeclarationsAt outward tailScope handler.clauses (families handler) := by
    simpa only [SourceDependencyProjection.scope_append_nil] using storedSchemes
  have effectSame := ScopedTyping.handler_cut_instance cut
  have scopedCheck : Local outward actions phases world (.request handler.effectInst operation) (capScope.append tailScope) := by
    simpa only [effectSame, ← scopeSame] using checked
  have scopedRetained : Pending outward actions phases world (capScope.append tailScope) .nil := scopeSame ▸ retained
  have scopedSelection : select handler.effectInst operation (capScope.append tailScope) =
      chosen operation (tables handler) (families handler) capScope tailScope := by
    simpa only [effectSame, ← scopeSame] using selection operation
  have scopedRow : offered.row capScope.held = some row := by simpa only [saved.realizes.held] using available
  have declaration := frame.erase.source
  cases frame with
  | handler scope annotation clauses coverage unique declarations capabilities modes =>
      obtain ⟨actualArgument, actualInput, resumeEffects, closeEffects, family, signature, resume, close, located,
        bodyChecked, liveRetained, body⟩ :=
        SourceContextualClauses.Lexical.allocate_declared_clause declarations modes schemes selected found scopedRow scopedSelection scopedCheck scopedRetained fresh consumed
      rw [effectSame] at signature
      rcases Prod.mk.inj (Option.some.inj (signature.symm.trans operationKnown)) with ⟨rfl, rfl⟩
      exact ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
        resumeEffects, closeEffects, family, annotation, scope, declaration, saved, waiting, scopeSame, demandSame, recordsSame, resume, close, located,
        bodyChecked, liveRetained, SourceContextualForest.Lexical.Forest.live storedSaved storedWaiting, evaluation, body⟩



end Ash.OneShot.SourceContextualCapture.Lexical

#print axioms Ash.OneShot.SourceContextualCapture.Lexical.capture_checked_interfaces


namespace Ash.OneShot.SourceContextualCapture.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts SourceDependencyCapture
open SourceDependencyChecks.Lexical
open SourceDependencyFrames (UnwindTemplate)
open RecursiveRequirements (Requirements)

/-- The actual disposing request constructs closing requirements from its
    selected typed capture. Their demand is its physical continuation ownership;
    equality with ordinary source demand remains a separate balance obligation. -/
theorem disposing_capture_summary
    (cut : HandlerCut requested whole capture tail handler)
    (source : SourceDependencyFrames.LexicalSegment operations policy contracts tables families actions world
      whole input output demand requirements records wholeScope incoming outgoing)
    (checked : Local outward actions phases world (.request requested operation) wholeScope)
    (found : lookup operation (tables handler) = some offered)
    (disposes : offered.dispose = true) :
    ProtectionContexts.protectedMode capture.erase = false ∧
      InternalUses capture.erase.liveTickets capture.erase.pending ∧
      ∃ closingDemand, ∃ closingRequirements : Requirements closingDemand,
        UnwindTemplate operations policy contracts tables world capture closingDemand closingRequirements ∧
        closingDemand.Perm (ownedTickets capture) := by
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
    annotation, frame, saved, waiting, scopeSame, demandSame, recordsSame, selection, evaluation⟩ :=
    SourceDependencyFrames.lexical_capture_segments cut source
  have guarded := Local.request_guard checked
  have selected : ∃ modes, select requested operation wholeScope = some (.handler capScope tailScope offered modes) := by
    cases modesFound : lookupDependencies operation (families handler) with
    | none =>
        have absent : select requested operation wholeScope = none := by
          simpa only [chosen, found, modesFound] using selection operation
        cases guarded with
        | builtin actual => rw [absent] at actual; cases actual
        | handler actual permission row body => rw [absent] at actual; cases actual
    | some modes => exact ⟨modes, by simpa only [chosen, found, modesFound] using selection operation⟩
  obtain ⟨modes, selected⟩ := selected
  have unprotected : ProtectionContexts.protectedMode capture.erase = false :=
    saved.realizes.held.symm.trans (guarded.disposing_unprotected selected disposes)
  obtain ⟨closingDemand, closingRequirements, summary⟩ := saved.unwind_template unprotected
  have bounded : SourceDependencyOwners.PendingWithin world
      (SourceDependencyOwners.owners capScope) capScope := by
    cases checked with
    | request guard callbacks owners => exact owners _ _ _ _ selected disposes
  have internal : InternalUses capture.erase.liveTickets capture.erase.pending := by
    simpa only [SourceDependencyOwners.realized_owners saved.realizes] using
      (SourceDependencyOwners.lexical_segment_pending_stack saved bounded).internal
  exact ⟨unprotected, internal, closingDemand, closingRequirements, summary, summary.ownership⟩

end Ash.OneShot.SourceContextualCapture.Lexical
#print axioms Ash.OneShot.SourceContextualCapture.Lexical.disposing_capture_summary

namespace Ash.OneShot.SourceContextualCapture.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations SourceDependencyFrames
open SourceDependencyChecks.Lexical (Local Pending)
open RecursiveRequirements (Requirements Store evaluate)
open OwnerPhaseTransitions (available spendAll)

/-- Actual source dispatch supplies the split and selected clause. A finite
cleanup-effect annotation completes the typed allocating runtime transition. -/
theorem allocate_disposing_capture
    (cut : HandlerCut requested whole capture tail handler)
    (source : LexicalSegment operations policy contracts tables families actions world
      whole input output demand requirements records wholeScope incoming outgoing)
    (certificates : SourceContextualForest.Lexical.Forest outward tables families whole wholeScope .nil)
    (checked : Local outward actions (available (ownedTickets whole)) world (.request requested operation) wholeScope)
    (retained : Pending outward actions (available (ownedTickets whole)) world wholeScope .nil)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (offeredRow : offered.row (ProtectionContexts.protectedMode capture.erase) = some advertised)
    (operationKnown : operations requested operation = some (argument, input))
    (disposes : offered.dispose = true)
    (fresh : contracts owner = none) (freshAction : actions owner = none)
    (payload : ValueSummary operations policy contracts world Environment.empty payloadAllowed operand argument)
    (closed : ClosedValue operand)
    (closing : UnwindRecords operations policy contracts tables world whole disposals)
    (recorded : ∀ key body, (key, body) ∈ disposals →
      SourceDependencySchemes.Lexical.UnwindAnnotated operations policy contracts tables families annotations world whole key body)
    (bound : SourceDependencySchemes.Closing.Bound annotations wholeScope)
    (freshAnnotation : annotations owner = none)
    (unique : (ownedTickets whole).Nodup)
    (pendingCheck : RecursiveRequirements.Checked (records ++ disposals) []
      (available (ownedTickets whole)) requirements pendingRow)
    (requestCheck : RecursiveRequirements.Checked (records ++ disposals) (OwnerPhases.ofStack tables whole)
      (available (ownedTickets whole)) (.request [] [⟨requested, operation, false⟩]) requestRow) :
    ∃ (answer : Value) (residual : List Instance) (capDemand tailDemand : List Nat)
      (capReq : Requirements capDemand) (tailReq : Requirements tailDemand)
      (capScope tailScope : Receiving) (resumeEffects closeEffects : List Instance)
      (family : Nat → Dependencies) (capRow tailRow : Footprint)
      (closingDemand : List Nat) (closingRequirements : Requirements closingDemand),
      wholeScope = capScope.append tailScope ∧ demand = capDemand ++ tailDemand ∧ pendingRow = capRow ++ tailRow ∧
      UnwindSource operations policy contracts tables families world capture closingDemand closingRequirements capScope ∧
      let closingRow := evaluate [] (OwnerPhases.ofStack tables tail) (available (ownedTickets whole)) closingRequirements
      let contract : Contract := ⟨input, answer, capScope.held,
        capDemand, capRow, closingDemand, closingRow, resumeEffects, closeEffects⟩
      let nextStack := Stack.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail
      let nextResumes : Store := (⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records
      let nextDisposals : Store := (⟨owner, .dispose⟩, ⟨closingDemand, closingRequirements⟩) :: disposals
      let entries := nextResumes ++ nextDisposals
      let nextAnnotations := fun other => if other = owner then some capScope else annotations other
      SourceDependencySchemes.Closing.Bound nextAnnotations (.live owner capScope tailScope) ∧
      (∀ key body, (key, body) ∈ nextDisposals →
        SourceDependencySchemes.Lexical.UnwindAnnotated operations policy (contracts.insert owner contract)
          tables families nextAnnotations world nextStack key body) ∧
      Local outward (actions.insert owner code.requiredActions) (available (ownedTickets nextStack))
        world (family owner) (.live owner capScope tailScope) ∧
      Pending outward (actions.insert owner code.requiredActions) (available (ownedTickets nextStack))
        world (.live owner capScope tailScope) .nil ∧
      SourceContextualForest.Lexical.Forest outward tables families nextStack (.live owner capScope tailScope) .nil ∧
      (ClosingEffects (requestRow ++ capRow) (OwnerPhases.ofStack tables tail)
        (available (ownedTickets whole)) closingRequirements →
        UnwindSource operations policy (contracts.insert owner contract) tables families world
          capture closingDemand closingRequirements capScope ∧
        RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩
          ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩ [.ticket owner] [] ∧
        ownedTickets nextStack = owner :: ownedTickets whole ∧
        (ownedTickets nextStack).Nodup ∧ closingDemand.Perm capDemand ∧
        LexicalSegment operations policy (contracts.insert owner contract) tables families
          (actions.insert owner code.requiredActions) world nextStack answer output tailDemand
          (.sequence (.spent owner) tailReq) nextResumes (.live owner capScope tailScope) residual outgoing ∧
        UnwindRecords operations policy (contracts.insert owner contract) tables world nextStack nextDisposals ∧
        RecursiveRequirements.Checked entries [] (spendAll (available (ownedTickets whole)) capDemand) tailReq tailRow ∧
        ∃ clauseDemand, ∃ clauseRequirements : Requirements clauseDemand, ∃ clauseRow,
          Expression operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
            Environment.empty (code.subst parameter operand) answer clauseDemand clauseRequirements (family owner) ∧
          RecursiveRequirements.Checked entries (OwnerPhases.ofStack tables nextStack)
            (available (ownedTickets nextStack)) clauseRequirements clauseRow ∧
          EffectBounds.Covers (requestRow ++ capRow) clauseRow ∧
          clauseDemand.Perm (owner :: capDemand) ∧
          RecursiveRequirements.Checked entries [] (available (ownedTickets nextStack))
            (.sequence (clauseRequirements.prepend (OwnerPhases.ofStack tables nextStack))
              (.sequence (.spent owner) tailReq)) (clauseRow ++ tailRow) ∧
          (clauseDemand ++ tailDemand).Perm (ownedTickets nextStack)) := by
  have consumed : available (ownedTickets whole) owner = .consumed := by
    simp [available, source.fresh_unowned fresh]
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
    resumeEffects, closeEffects, family, annotation, scope, declaration, saved, waiting, scopeSame, demandSame, recordsSame,
    resume, close, located, clauseChecked, liveRetained, liveCertificates, evaluation, body⟩ :=
    capture_checked_interfaces cut source certificates checked retained selected found offeredRow operationKnown freshAction consumed
  have evaluated := RecursiveRequirements.checked_complete pendingCheck
  rw [evaluation] at evaluated
  obtain ⟨capRow, tailRow, inside, outside, rowSame⟩ := PhaseRechecking.merge_split evaluated
  have savedCheck := RecursiveRequirements.evaluate_sound inside
  have tailCheck := RecursiveRequirements.evaluate_sound outside
  obtain ⟨unprotected, internal, _⟩ :=
    disposing_capture_summary cut source checked found disposes
  obtain ⟨closingDemand, closingRequirements, closingSource⟩ := saved.unwind_source unprotected
  have requestExport := RecursiveRequirements.checked_complete requestCheck
  simp only [RecursiveContexts.evaluate_request, OwnerSource.exportAt,
    OwnerPhaseTransitions.project_actual] at requestExport
  obtain ⟨actualOffer, actualAdvertised, offerKnown, mode, rowKnown, advertisedExport⟩ :=
    RecursiveDispatch.cut_residual cut requestExport
  have sameOffer := Option.some.inj (offerKnown.symm.trans found)
  subst actualOffer
  simp only [Bool.false_or] at rowKnown
  have sameAdvertised := Option.some.inj (rowKnown.symm.trans offeredRow)
  subst actualAdvertised
  let allocated : Contract := ⟨input, answer, capScope.held, capDemand, capRow, closingDemand,
    evaluate [] (OwnerPhases.ofStack tables tail) (available (ownedTickets whole)) closingRequirements,
    resumeEffects, closeEffects⟩
  have nextAnnotated := SourceDependencySchemes.Lexical.capture_annotated_records
    (input := ScopedPorts.embedPort input.erase.port) (answer := handler.answer) (caller := handler.scope)
    cut closingSource unprotected scopeSame bound freshAnnotation recorded
    (SourceDependencyAnnotations.insert_extends (contract := allocated) contracts fresh)
  refine ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capScope, tailScope,
    resumeEffects, closeEffects, family, capRow, tailRow, closingDemand, closingRequirements,
    scopeSame, demandSame, rowSame, closingSource, nextAnnotated.1, nextAnnotated.2, ?_, ?_, liveCertificates, ?_⟩
  · simpa only [OwnerPhaseTransitions.capture_map cut] using clauseChecked
  · simpa only [OwnerPhaseTransitions.capture_map cut] using liveRetained
  · intro effects
    refine ⟨closingSource.transport (SourceDependencyAnnotations.insert_extends contracts fresh) (List.Subset.refl _), ?_⟩
    exact SourceDependencySchemes.Lexical.allocate_disposing_clause_from_split cut source annotation scope saved waiting
      recordsSame (by simpa only [List.append_nil] using savedCheck) tailCheck unique fresh freshAction
      resume close closing unprotected internal closingSource.template declaration selected body payload closed advertisedExport effects

end Ash.OneShot.SourceContextualCapture.Lexical
#print axioms Ash.OneShot.SourceContextualCapture.Lexical.allocate_disposing_capture

namespace Ash.OneShot.SourceContextualCapture.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations SourceDependencyFrames
open SourceDependencyChecks.Lexical (Local Pending)
open RecursiveRequirements (Requirements Store evaluate)
open OwnerPhaseTransitions (available spendAll)

/-- Resume-only dispatch uses the actual source split without imposing
disposal readiness or internal-use restrictions on the captured segment. -/
theorem allocate_resuming_capture
    (cut : HandlerCut requested whole capture tail handler)
    (source : LexicalSegment operations policy contracts tables families actions world
      whole input output demand requirements records wholeScope incoming outgoing)
    (certificates : SourceContextualForest.Lexical.Forest outward tables families whole wholeScope .nil)
    (checked : Local outward actions (available (ownedTickets whole)) world (.request requested operation) wholeScope)
    (retained : Pending outward actions (available (ownedTickets whole)) world wholeScope .nil)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (offeredRow : offered.row (ProtectionContexts.protectedMode capture.erase) = some advertised)
    (operationKnown : operations requested operation = some (argument, input))
    (noDispose : offered.dispose = false)
    (fresh : contracts owner = none) (freshAction : actions owner = none)
    (payload : ValueSummary operations policy contracts world Environment.empty payloadAllowed operand argument)
    (closed : ClosedValue operand)
    (closing : UnwindRecords operations policy contracts tables world whole disposals)
    (recorded : ∀ key body, (key, body) ∈ disposals →
      SourceDependencySchemes.Lexical.UnwindAnnotated operations policy contracts tables families annotations world whole key body)
    (annotationBound : SourceDependencySchemes.Closing.Bound annotations wholeScope)
    (freshAnnotation : annotations owner = none)
    (unique : (ownedTickets whole).Nodup)
    (pendingCheck : RecursiveRequirements.Checked (records ++ disposals) []
      (available (ownedTickets whole)) requirements pendingRow)
    (requestCheck : RecursiveRequirements.Checked (records ++ disposals) (OwnerPhases.ofStack tables whole)
      (available (ownedTickets whole)) (.request [] [⟨requested, operation, false⟩]) requestRow) :
    ∃ (answer : Value) (residual : List Instance) (capDemand tailDemand : List Nat)
      (capReq : Requirements capDemand) (tailReq : Requirements tailDemand)
      (capScope tailScope : Receiving) (resumeEffects closeEffects : List Instance)
      (family : Nat → Dependencies) (capRow tailRow : Footprint),
      wholeScope = capScope.append tailScope ∧ demand = capDemand ++ tailDemand ∧ pendingRow = capRow ++ tailRow ∧
      let contract : Contract := ⟨input, answer, capScope.held,
        capDemand, capRow, capDemand, none, resumeEffects, closeEffects⟩
      let nextStack := Stack.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail
      let nextResumes : Store := (⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records
      Local outward (actions.insert owner code.requiredActions) (available (ownedTickets nextStack))
        world (family owner) (.live owner capScope tailScope) ∧
      Pending outward (actions.insert owner code.requiredActions) (available (ownedTickets nextStack))
        world (.live owner capScope tailScope) .nil ∧
      SourceContextualForest.Lexical.Forest outward tables families nextStack (.live owner capScope tailScope) .nil ∧
      let nextAnnotations := fun other => if other = owner then some capScope else annotations other
      ∃ nextDisposals : Store,
        SourceDependencySchemes.Closing.Bound nextAnnotations (.live owner capScope tailScope) ∧
        (∀ key body, (key, body) ∈ nextDisposals →
          SourceDependencySchemes.Lexical.UnwindAnnotated operations policy (contracts.insert owner contract)
            tables families nextAnnotations world nextStack key body) ∧
        RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩
          ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩ [.ticket owner] [] ∧
        ownedTickets nextStack = owner :: ownedTickets whole ∧
        (ownedTickets nextStack).Nodup ∧
        LexicalSegment operations policy (contracts.insert owner contract) tables families
          (actions.insert owner code.requiredActions) world nextStack answer output tailDemand
          (.sequence (.spent owner) tailReq) nextResumes (.live owner capScope tailScope) residual outgoing ∧
        UnwindRecords operations policy (contracts.insert owner contract) tables world nextStack nextDisposals ∧
        RecursiveRequirements.Checked (nextResumes ++ nextDisposals) [] (spendAll (available (ownedTickets whole)) capDemand) tailReq tailRow ∧
        ∃ clauseDemand, ∃ clauseRequirements : Requirements clauseDemand, ∃ clauseRow,
          Expression operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
            Environment.empty (code.subst parameter operand) answer clauseDemand clauseRequirements (family owner) ∧
          RecursiveRequirements.Checked (nextResumes ++ nextDisposals) (OwnerPhases.ofStack tables nextStack)
            (available (ownedTickets nextStack)) clauseRequirements clauseRow ∧
          EffectBounds.Covers (requestRow ++ capRow) clauseRow ∧
          clauseDemand.Perm (owner :: capDemand) ∧
          RecursiveRequirements.Checked (nextResumes ++ nextDisposals) [] (available (ownedTickets nextStack))
            (.sequence (clauseRequirements.prepend (OwnerPhases.ofStack tables nextStack))
              (.sequence (.spent owner) tailReq)) (clauseRow ++ tailRow) ∧
          (clauseDemand ++ tailDemand).Perm (ownedTickets nextStack) := by
  have consumed : available (ownedTickets whole) owner = .consumed := by
    simp [available, source.fresh_unowned fresh]
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
    resumeEffects, closeEffects, family, annotation, scope, declaration, saved, waiting, scopeSame, demandSame, recordsSame,
    resume, close, located, clauseChecked, liveRetained, liveCertificates, evaluation, body⟩ :=
    capture_checked_interfaces cut source certificates checked retained selected found offeredRow operationKnown freshAction consumed
  have evaluated := RecursiveRequirements.checked_complete pendingCheck
  rw [evaluation] at evaluated
  obtain ⟨capRow, tailRow, inside, outside, rowSame⟩ := PhaseRechecking.merge_split evaluated
  have savedCheck := RecursiveRequirements.evaluate_sound inside
  have tailCheck := RecursiveRequirements.evaluate_sound outside
  have requestExport := RecursiveRequirements.checked_complete requestCheck
  simp only [RecursiveContexts.evaluate_request, OwnerSource.exportAt,
    OwnerPhaseTransitions.project_actual] at requestExport
  obtain ⟨actualOffer, actualAdvertised, offerKnown, mode, rowKnown, advertisedExport⟩ :=
    RecursiveDispatch.cut_residual cut requestExport
  have sameOffer := Option.some.inj (offerKnown.symm.trans found)
  subst actualOffer
  simp only [Bool.false_or] at rowKnown
  have sameAdvertised := Option.some.inj (rowKnown.symm.trans offeredRow)
  subst actualAdvertised
  refine ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capScope, tailScope,
    resumeEffects, closeEffects, family, capRow, tailRow,
    scopeSame, demandSame, rowSame, ?_, ?_, liveCertificates, ?_⟩
  · simpa only [OwnerPhaseTransitions.capture_map cut] using clauseChecked
  · simpa only [OwnerPhaseTransitions.capture_map cut] using liveRetained
  · exact SourceDependencySchemes.Lexical.allocate_resuming_clause_from_split cut source annotation scope saved waiting
      recordsSame (by simpa only [List.append_nil] using savedCheck) tailCheck unique fresh freshAction
      resume close closing recorded (scopeSame ▸ annotationBound) freshAnnotation declaration selected body payload closed advertisedExport noDispose

end Ash.OneShot.SourceContextualCapture.Lexical
#print axioms Ash.OneShot.SourceContextualCapture.Lexical.allocate_resuming_capture

namespace Ash.OneShot.SourceContextualCapture.Lexical
open ScopedExpressions ScopedExecution
open SourceDependencyAnnotations (Operations Contracts)
open SourceDependencyFrames (UnwindSource UnwindTemplate ClosingEffects UnwindRecords LexicalSegment unwindStore)
open SourceDependencyChecks.Lexical (Unwind)
open SourceContextualRechecking (handlers checkForest)
open SourceContextualRequirements (DeclarationRecipes)
open OwnerPhaseTransitions (available spendAll)
open RecursiveRequirements (Requirements Checked)
open SourceDependencySchemes.Lexical (UnwindAnnotated)
open SourceDependencySchemes.Closing (Bound)

/-- Join the active lexical unwind prefix's source, effect, handler, access and
owner facts for the same administrative transition, with an arbitrary retained
caller suffix. No successor check or certificate is a premise. This concerns
administrative unwinding; callback evaluation remains a separate component of
the complete machine invariant. The waiting source and its records are retained,
and its requirement check is preserved under the exact store update. -/
theorem advance_unwind_components
    (step : LexicalUnwind.Advance active nextPrefix discharged)
    (source : UnwindSource operations policy contracts tables families world active demand requirements prefixScope)
    (waiting : LexicalSegment operations policy contracts tables families actions world
      suffix waitingInput output waitingDemand waitingRequirements waitingResumes outsideScope incoming outgoing)
    (effects : ClosingEffects budget (OwnerPhases.ofStack tables suffix)
      (available (ownedTickets (active.append suffix))) requirements)
    (callbacks : Unwind outward actions (available (ownedTickets (active.append suffix)))
      world prefixScope outsideScope)
    (modeChecks : SourceDependencyChecks.Lexical.ModePending outward actions
      (available (ownedTickets (active.append suffix))) world tables families
      (active.append suffix) (prefixScope.append outsideScope) .nil .unwind finalMode)
    (annotationBound : Bound annotations (prefixScope.append outsideScope))
    (annotated : ∀ key body, (key, body) ∈ (disposals : RecursiveRequirements.Store) →
      UnwindAnnotated operations policy contracts tables families annotations world (active.append suffix) key body)
    (recipes : ∀ handler ∈ handlers (active.append suffix),
      DeclarationRecipes outward handler.clauses (families handler) (required handler))
    (checked : checkForest required (active.append suffix) (prefixScope.append outsideScope) .nil = true)
    (supported : Supported (active.append suffix).erase ambient)
    (unique : (ownedTickets (active.append suffix)).Nodup)
    (resumeSources : ∀ key body, (key, body) ∈ resumes →
      SourceDependencyOwners.Lexical.ResumeCertified operations policy contracts tables families actions world
        (active.append suffix) key body)
    (closing : UnwindRecords operations policy contracts tables world (active.append suffix) disposals)
    (keysUnique : (RecursiveTransport.recordKeys (resumes ++ disposals)).Nodup)
    (waitingCheck : Checked (resumes ++ disposals) []
      (spendAll (available (ownedTickets (active.append suffix))) demand) waitingRequirements waitingRow) :
    ∃ nextDemand, ∃ nextRequirements : Requirements nextDemand, ∃ nextScope,
      UnwindSource operations policy contracts tables families world nextPrefix nextDemand nextRequirements nextScope ∧
      SourceDependencyChecks.Lexical.ModePending outward actions
        (available (ownedTickets (nextPrefix.append suffix))) world tables families
        (nextPrefix.append suffix) (nextScope.append outsideScope) .nil .unwind finalMode ∧
      Bound annotations (nextScope.append outsideScope) ∧
      (∀ key body, (key, body) ∈ unwindStore active disposals →
        UnwindAnnotated operations policy contracts tables families annotations world (nextPrefix.append suffix) key body) ∧
      ClosingEffects budget (OwnerPhases.ofStack tables suffix)
        (available (ownedTickets (nextPrefix.append suffix))) nextRequirements ∧
      SourceDependencyCapture.Realizes tables families nextScope nextPrefix ∧
      Unwind outward actions (available (ownedTickets (nextPrefix.append suffix)))
        world nextScope outsideScope ∧
      (∀ handler ∈ handlers (nextPrefix.append suffix),
        DeclarationRecipes outward handler.clauses (families handler) (required handler)) ∧
      checkForest required (nextPrefix.append suffix) (nextScope.append outsideScope) .nil = true ∧
      SourceContextualForest.Lexical.Forest outward tables families
        (nextPrefix.append suffix) (nextScope.append outsideScope) .nil ∧
      Supported (nextPrefix.append suffix).erase ambient ∧
      (ownedTickets (nextPrefix.append suffix)).Nodup ∧
      nextDemand.Perm (ownedTickets nextPrefix) ∧
      spendAll (available (ownedTickets (active.append suffix))) (discharged.filterMap Syntax.ticketProjection) =
        available (ownedTickets (nextPrefix.append suffix)) ∧
      (∀ key body, (key, body) ∈ unwindStore active resumes →
        SourceDependencyOwners.Lexical.ResumeCertified operations policy contracts tables families actions world
          (nextPrefix.append suffix) key body) ∧
      UnwindRecords operations policy contracts tables world (nextPrefix.append suffix) (unwindStore active disposals) ∧
      (RecursiveTransport.recordKeys (unwindStore active resumes ++ unwindStore active disposals)).Nodup ∧
      unwindStore active waitingResumes = waitingResumes ∧
      Checked (unwindStore active resumes ++ unwindStore active disposals) []
        (spendAll (available (ownedTickets (nextPrefix.append suffix))) nextDemand) waitingRequirements waitingRow ∧
      ∃ closingRow, closingRow ⊆ budget ∧
        Checked (unwindStore active resumes ++ unwindStore active disposals) []
          (available (ownedTickets (nextPrefix.append suffix)))
          (.sequence (nextRequirements.prepend (OwnerPhases.ofStack tables suffix)) waitingRequirements)
          (closingRow ++ waitingRow) := by
  have summary := source.template
  have realized := source.realizes
  have outside := waiting.realizes
  have wholeStep := LexicalUnwind.append step suffix
  obtain ⟨nextUnique, phases⟩ := SourceDependencyFrames.unwind_owner_phases wholeStep unique
  have prefixUnique : (ownedTickets active).Nodup := by
    rw [owned_tickets_append] at unique
    exact (List.nodup_append.mp unique).1
  have ownership := OwnerPhaseTransitions.trace_of_available
    (summary.ownership.nodup_iff.mpr prefixUnique)
    (before := available (ownedTickets (active.append suffix))) (by
      intro owner member
      apply if_pos
      rw [owned_tickets_append]
      exact List.mem_append_left _ (summary.ownership.mem_iff.mp member))
  obtain ⟨nextDemand, nextRequirements, nextSource, nextEffects⟩ :=
    source.advance_effects effects ownership step
  have nextSummary := nextSource.template
  let nextScope := prefixScope.afterUnwind
  rw [phases] at nextEffects
  rw [SourceContextualRechecking.Lexical.check_forest_append realized outside,
    SourceDependencyProjection.scope_append_nil, Bool.and_eq_true] at checked
  obtain ⟨nextRealized, nextCheck, nextCallbacks⟩ :=
    SourceContextualRechecking.Lexical.advance_unwind_checked step realized checked.1 callbacks
  have oldBounds := Bound.append_iff.mp annotationBound
  have nextBound := Bound.append_iff.mpr
    ⟨SourceDependencySchemes.Lexical.bound_advance step realized oldBounds.1, oldBounds.2⟩
  have nextAnnotated : ∀ key body, (key, body) ∈ unwindStore active disposals →
      UnwindAnnotated operations policy contracts tables families annotations world (nextPrefix.append suffix) key body := by
    simpa only [SourceDependencyFrames.unwind_store_outside step] using
      SourceDependencySchemes.Lexical.annotated_records_advance wholeStep annotated
  have nextRoot := nextRealized.append outside
  have scopeStep : (prefixScope.append outsideScope).afterUnwind =
      prefixScope.afterUnwind.append outsideScope := by
    cases step with
    | plain | handler | cell | retire => cases realized with
        | push frame tail => cases frame <;> rfl
    | spent => cases realized <;> rfl
    | live => cases realized with
        | @live capturedScope captured restScope rest owner input answer caller saved tail =>
            exact (SourceDependencyChecks.scope_append_assoc capturedScope (.running restScope) outsideScope).symm
  have nextModes := modeChecks.advance wholeStep
  rw [scopeStep] at nextModes
  have restrictedModes := SourceDependencySchemes.Lexical.mode_pending_restrict nextModes
    (by simpa only [SourceDependencyProjection.scope_append_nil] using
      SourceConsumingCleanupAdmission.realized_available nextRoot)
  have callbackPhases := SourceDependencySchemes.Lexical.unwind_restrict nextCallbacks
    (SourceConsumingCleanupAdmission.realized_available nextRoot)
  have nextRecipes : ∀ handler ∈ handlers (nextPrefix.append suffix),
      DeclarationRecipes outward handler.clauses (families handler) (required handler) :=
    fun handler member => recipes handler (SourceContextualRechecking.Lexical.advance_handlers wholeStep member)
  have rootCheck : checkForest required (nextPrefix.append suffix) (nextScope.append outsideScope) .nil = true := by
    rw [SourceContextualRechecking.Lexical.check_forest_append nextRealized outside,
      SourceDependencyProjection.scope_append_nil, Bool.and_eq_true]
    exact ⟨nextCheck, checked.2⟩
  have nextResumeSources : ∀ key body, (key, body) ∈ unwindStore active resumes →
      SourceDependencyOwners.Lexical.ResumeCertified operations policy contracts tables families actions world
        (nextPrefix.append suffix) key body := by
    simpa only [SourceDependencyFrames.unwind_store_outside step] using
      SourceDependencyOwners.Lexical.resume_records_advance wholeStep resumeSources
  have nextClosing : UnwindRecords operations policy contracts tables world
      (nextPrefix.append suffix) (unwindStore active disposals) := by
    simpa only [SourceDependencyFrames.unwind_store_outside step] using closing.advance wholeStep unique
  have nextKeys : (RecursiveTransport.recordKeys
      (unwindStore active resumes ++ unwindStore active disposals)).Nodup := by
    rw [← SourceDependencyFrames.unwind_store_combined]
    cases active <;> first | exact keysUnique | exact RecursiveTransport.remove_owner_unique keysUnique
  have waitingRecords := SourceDependencyFrames.unwind_waiting_records step unique
    waiting.record_owners_sublist.subset
  rw [summary.waiting_phases unique] at waitingCheck
  have updatedWaiting := SourceDependencyFrames.unwind_waiting_checked step unique waitingCheck
  rw [SourceDependencyFrames.unwind_store_combined] at updatedWaiting
  have nextWaiting : Checked (unwindStore active resumes ++ unwindStore active disposals) []
      (spendAll (available (ownedTickets (nextPrefix.append suffix))) nextDemand) waitingRequirements waitingRow := by
    rw [nextSummary.waiting_phases nextUnique]
    exact updatedWaiting
  have activeUnique : (ownedTickets nextPrefix).Nodup := by
    rw [owned_tickets_append] at nextUnique
    exact (List.nodup_append.mp nextUnique).1
  obtain ⟨closingRow, evaluated, bounded⟩ := nextSummary.checked_effects
    (entries := unwindStore active resumes ++ unwindStore active disposals) nextEffects activeUnique (by
      intro owner member
      apply if_pos
      rw [owned_tickets_append]
      exact List.mem_append_left _ member)
  have closingCheck : Checked (unwindStore active resumes ++ unwindStore active disposals) []
      (available (ownedTickets (nextPrefix.append suffix)))
      (nextRequirements.prepend (OwnerPhases.ofStack tables suffix)) closingRow :=
    RecursiveRequirements.checked_prepend_iff.mpr
      (by simpa only [List.append_nil] using RecursiveRequirements.evaluate_sound evaluated)
  exact ⟨nextDemand, nextRequirements, nextScope, nextSource, restrictedModes, nextBound, nextAnnotated, nextEffects, nextRealized, callbackPhases,
    nextRecipes, rootCheck, SourceContextualRechecking.Lexical.recheck_forest nextRoot nextRecipes rootCheck,
    LexicalUnwind.administrative_access wholeStep supported, nextUnique, nextSummary.ownership, phases,
    nextResumeSources, nextClosing, nextKeys, waitingRecords, nextWaiting,
    closingRow, bounded, .sequence closingCheck nextWaiting⟩
end Ash.OneShot.SourceContextualCapture.Lexical
#print axioms Ash.OneShot.SourceContextualCapture.Lexical.advance_unwind_components


namespace Ash.OneShot.SourceContextualCapture.Lexical
open ScopedExpressions ScopedExecution
open SourceDependencyAnnotations (Expression Environment)
open SourceDependencyFrames (UnwindSource ClosingEffects)
open SourceDependencyChecks.Lexical (Local Unwind)
open SourceContextualForest.Lexical (Forest)
open RecursiveRequirements (Requirements Checked)
open SourceDependencySchemes.Lexical (UnwindAnnotated)
open SourceDependencySchemes.Closing (Bound)
open OwnerPhaseTransitions (Trace)

/-- Enter the actual callback with its shared source annotation, effect check,
lexical dependency check, retained handlers and resource support. The suffix is
an arbitrary actual caller stack; no callback evaluation is assumed. -/
theorem start_unwind_cleanup_components
    (source : UnwindSource operations policy contracts tables families world
      (.push (.armed action) rest) demand requirements dependencyScope)
    (effects : ClosingEffects budget (OwnerPhases.ofStack tables suffix) phases requirements)
    (ownership : Trace phases demand completed)
    (callbacks : Unwind outward actions phases world dependencyScope outsideScope)
    (modeChecks : SourceDependencyChecks.Lexical.ModePending outward actions phases world tables families
      ((Stack.push (.armed action) rest).append suffix) (dependencyScope.append outsideScope) .nil .unwind finalMode)
    (forest : Forest outward tables families ((Stack.push (.armed action) rest).append suffix)
      (dependencyScope.append outsideScope) .nil)
    (supported : Supported ((Stack.push (.armed action) rest).append suffix).erase ambient)
    (resumeSources : ∀ key body, (key, body) ∈ (resumes : RecursiveRequirements.Store) →
      SourceDependencyOwners.Lexical.ResumeCertified operations policy contracts tables families actions world
        ((Stack.push (.armed action) rest).append suffix) key body)
    (closing : SourceDependencyFrames.UnwindRecords operations policy contracts tables world
      ((Stack.push (.armed action) rest).append suffix) disposals)
    (annotationBound : Bound annotations (dependencyScope.append outsideScope))
    (annotated : ∀ key body, (key, body) ∈ disposals →
      UnwindAnnotated operations policy contracts tables families annotations world
        ((Stack.push (.armed action) rest).append suffix) key body)
    (ledger : Ledger ⟨((Stack.push (.armed action) rest).append suffix).erase, issued, completedOwners⟩) :
    ∃ latent dependencies callbackRow nextScope, ∃ tailRequirements : Requirements demand,
      dependencyScope = .cleanup action.requests dependencies nextScope ∧
      Expression operations policy contracts world action.requests .none Environment.empty
        (.app action.action .unit) .unit []
        (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent)
        (.sequence .pure (.sequence .pure dependencies)) ∧
      UnwindSource operations policy contracts tables families world rest demand tailRequirements nextScope ∧
      Checked (resumes ++ disposals) (OwnerPhases.ofStack tables (.push (.unwinding action) (rest.append suffix))) phases
        (.emitAfter (.sequence (.request [] []) (.request [] [])) [] latent) callbackRow ∧
      callbackRow ⊆ budget ∧
      ClosingEffects budget (OwnerPhases.ofStack tables suffix) phases tailRequirements ∧
      Local outward actions phases world (.sequence .pure (.sequence .pure dependencies))
        (.running (nextScope.append outsideScope)) ∧
      Unwind outward actions phases world nextScope outsideScope ∧
      SourceDependencyChecks.Lexical.ModePending outward actions phases world tables families
        (.push (.unwinding action) (rest.append suffix)) (.running (nextScope.append outsideScope)) .nil .ordinary finalMode ∧
      Forest outward tables families (.push (.unwinding action) (rest.append suffix))
        (.running (nextScope.append outsideScope)) .nil ∧
      LexicalUnwind.Transition (.unwind runtimeScope ((Stack.push (.armed action) rest).append suffix))
        (.eval ⟨.app action.action .unit, .none, .push (.unwinding action) (rest.append suffix)⟩) [] [] ∧
      LexicalUnwind.MachineAccess ambient
        (.eval ⟨.app action.action .unit, .none, .push (.unwinding action) (rest.append suffix)⟩) ∧
      (∀ key body, (key, body) ∈ (resumes : RecursiveRequirements.Store) →
        SourceDependencyOwners.Lexical.ResumeCertified operations policy contracts tables families actions world
          (.push (.unwinding action) (rest.append suffix)) key body) ∧
      SourceDependencyFrames.UnwindRecords operations policy contracts tables world
        (.push (.unwinding action) (rest.append suffix)) disposals ∧
      Bound annotations (.running (nextScope.append outsideScope)) ∧
      (∀ key body, (key, body) ∈ disposals →
        UnwindAnnotated operations policy contracts tables families annotations world
          (.push (.unwinding action) (rest.append suffix)) key body) ∧
      Ledger ⟨(Stack.push (.unwinding action) (rest.append suffix)).erase, issued, completedOwners⟩ := by
  obtain ⟨latent, dependencies, callbackRow, nextScope, tailRequirements,
    annotation, callback, tail, callbackCheck, bounded, tailEffects⟩ :=
    source.start_cleanup_effects (entries := resumes ++ disposals) effects ownership
  subst dependencyScope
  have nextModes : SourceDependencyChecks.Lexical.ModePending outward actions phases world tables families
      (.push (.unwinding action) (rest.append suffix)) (.running (nextScope.append outsideScope)) .nil .ordinary finalMode := by
    obtain ⟨checkedDependencies, checkedScope, same, _, next⟩ := modeChecks.start_cleanup
    cases same
    exact next
  cases callbacks with
  | cleanup localCheck tailCheck =>
      have nextForest := forest.start_cleanup
      have step : LexicalUnwind.Transition
          (.unwind runtimeScope ((Stack.push (.armed action) rest).append suffix))
          (.eval ⟨.app action.action .unit, .none, .push (.unwinding action) (rest.append suffix)⟩) [] [] :=
        .startCleanup
      refine ⟨latent, dependencies, callbackRow, nextScope, tailRequirements, rfl,
        callback, tail, ?_, bounded, tailEffects,
        .sequence .pure (.sequence .pure localCheck), tailCheck, nextModes, nextForest, step,
        LexicalUnwind.transition_access step (.unwind supported) trivial, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [← OwnerPhases.stack_append, Stack.append] using callbackCheck
      · intro key body member
        exact (resumeSources key body member).transport (by
          intro owner capture located
          cases located with | push inner => exact .push inner)
      · cases closing with | push tail => exact .push tail
      · cases annotationBound with | cleanup tail => exact .running tail
      · intro key body member
        exact (annotated key body member).transport (fun _ _ known => known)
          (fun _ _ known => known) (List.Subset.refl _) (by
            intro owner capture located
            cases located with | push inner => exact .push inner)
      · simpa only [LexicalUnwind.Machine.stack, List.append_nil, List.nil_append] using
          LexicalUnwind.transition_preserves_ledger step ledger
            (by simpa only [List.append_nil] using ledger.2)
end Ash.OneShot.SourceContextualCapture.Lexical
#print axioms Ash.OneShot.SourceContextualCapture.Lexical.start_unwind_cleanup_components


namespace Ash.OneShot.SourceContextualCapture.Lexical
open ScopedExpressions ScopedExecution
open SourceDependencyChecks.Lexical (Unwind)
open SourceContextualForest.Lexical (Forest)
open SourceDependencyFrames (UnwindRecords)
open SourceDependencyOwners.Lexical (ResumeCertified)
open SourceDependencySchemes.Lexical (UnwindAnnotated)
open SourceDependencySchemes.Closing (Bound)
variable {rest suffix : Stack}

/-- Returning from the actual unwind callback preserves the retained records
and lexical checks, and discharges only that callback's cleanup owner. These
are pre-step facts at Unit return; this does not assume callback termination. -/
theorem finish_unwind_cleanup_components
    (callbacks : Unwind outward actions phases world (.running dependencyScope) outsideScope)
    (modeChecks : SourceDependencyChecks.Lexical.ModePending outward actions phases world tables families
      (.push (.unwinding action) (rest.append suffix)) (.running (dependencyScope.append outsideScope)) .nil .ordinary finalMode)
    (forest : Forest outward tables families (.push (.unwinding action) (rest.append suffix))
      (.running (dependencyScope.append outsideScope)) .nil)
    (access : LexicalUnwind.MachineAccess ambient
      (.eval ⟨.unit, runtimeScope, .push (.unwinding action) (rest.append suffix)⟩))
    (resumeSources : ∀ key body, (key, body) ∈ (resumes : RecursiveRequirements.Store) →
      ResumeCertified operations policy contracts tables families actions world
        (.push (.unwinding action) (rest.append suffix)) key body)
    (closing : UnwindRecords operations policy contracts tables world
      (.push (.unwinding action) (rest.append suffix)) disposals)
    (annotationBound : Bound annotations (.running (dependencyScope.append outsideScope)))
    (annotated : ∀ key body, (key, body) ∈ disposals →
      UnwindAnnotated operations policy contracts tables families annotations world
        (.push (.unwinding action) (rest.append suffix)) key body)
    (ledger : Ledger ⟨(Stack.push (.unwinding action) (rest.append suffix)).erase, issued, completed⟩) :
    LexicalUnwind.Transition
      (.eval ⟨.unit, runtimeScope, .push (.unwinding action) (rest.append suffix)⟩)
      (.unwind action.scope (rest.append suffix)) [] [.cleanup action.identity] ∧
    Unwind outward actions phases world dependencyScope outsideScope ∧
    SourceDependencyChecks.Lexical.ModePending outward actions phases world tables families
      (rest.append suffix) (dependencyScope.append outsideScope) .nil .unwind finalMode ∧
    Forest outward tables families (rest.append suffix) (dependencyScope.append outsideScope) .nil ∧
    LexicalUnwind.MachineAccess ambient (.unwind action.scope (rest.append suffix)) ∧
    (∀ key body, (key, body) ∈ resumes →
      ResumeCertified operations policy contracts tables families actions world (rest.append suffix) key body) ∧
    UnwindRecords operations policy contracts tables world (rest.append suffix) disposals ∧
    Bound annotations (dependencyScope.append outsideScope) ∧
    (∀ key body, (key, body) ∈ disposals →
      UnwindAnnotated operations policy contracts tables families annotations world (rest.append suffix) key body) ∧
    Ledger ⟨(rest.append suffix).erase, issued, .cleanup action.identity :: completed⟩ := by
  have step : LexicalUnwind.Transition
      (.eval ⟨.unit, runtimeScope, .push (.unwinding action) (rest.append suffix)⟩)
      (.unwind action.scope (rest.append suffix)) [] [.cleanup action.identity] := .finishCleanup
  have nextModes : SourceDependencyChecks.Lexical.ModePending outward actions phases world tables families
      (rest.append suffix) (dependencyScope.append outsideScope) .nil .unwind finalMode := by
    obtain ⟨checkedScope, same, next⟩ := modeChecks.finish_cleanup
    cases same
    exact next
  refine ⟨step, ?_, nextModes, forest.finish_cleanup, LexicalUnwind.transition_access step access (by
    constructor
    · intro identity payload answer savedScope scope value tail same
      cases same
    · intro requested operation operand scope whole cap tail handler same
      cases same), ?_, ?_, ?_, ?_, ?_⟩
  · cases callbacks with | running tail => exact tail
  · intro key body member
    exact (resumeSources key body member).transport (by
      intro owner capture located
      cases located with | push inner => exact inner)
  · cases closing with | push tail => exact tail
  · cases annotationBound with | running tail => exact tail
  · intro key body member
    exact (annotated key body member).transport (fun _ _ known => known)
      (fun _ _ known => known) (List.Subset.refl _) (by
        intro owner capture located
        cases located with | push inner => exact inner)
  · simpa only [LexicalUnwind.Machine.stack, List.append_nil, List.cons_append, List.nil_append] using
      LexicalUnwind.transition_preserves_ledger step ledger
        (by simpa only [List.append_nil] using ledger.2)
end Ash.OneShot.SourceContextualCapture.Lexical
#print axioms Ash.OneShot.SourceContextualCapture.Lexical.finish_unwind_cleanup_components


namespace Ash.OneShot.SourceContextualCapture.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations
open SourceDependencyCapture (lookupDependencies modeDependencies)
open SourceDependencyFrames (UnwindSource)
open SourceContextualClauses.Lexical (FamilyAt)
open SourceContextualForest.Lexical (Forest)

/-- A request from an executing prefix selects the typed declaration from
its mixed-mode source and the contextual family from that same installation. -/
theorem mode_selected_body
    (cut : HandlerCut requested whole capture tail handler)
    (source : SourceDependencyFrames.ModeSource operations policy contracts tables families actions world
      whole inputBoundary outputBoundary demand requirements dependencyScope)
    (forest : Forest outward tables families whole dependencyScope outside)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row held = some row) :
    ∃ (capturedScope tailScope : SourceDependencyCapture.Scope) (answer : Value) (residual : List Instance)
      (argument input : Value) (resumeEffects closeEffects : List Instance) (family : Nat → Dependencies),
      dependencyScope = capturedScope.append tailScope ∧
      answer.erase.port = ScopedPorts.eraseType handler.answer ∧
      operations requested operation = some (argument, input) ∧
      (code.requiredActions.resume = true → resumeEffects = residual) ∧
      (code.requiredActions.dispose = true → closeEffects = residual) ∧
      (lookupDependencies operation (families handler)).bind (modeDependencies held) = some family ∧
      FamilyAt outward code.requiredActions family (tailScope.append outside) ∧
      ∀ owner (contract : Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = held → contract.closeDemand.Perm contract.resumeDemand →
        Body operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
          (Environment.empty.extend parameter argument) code answer ⟨owner, contract.erase, offered.dispose, row⟩ (family owner) := by
  obtain ⟨answer, residual, _, _, _, _, _, _, _, declaration, _⟩ := source.handler_cut cut
  obtain ⟨capturedScope, tailScope, saved, waiting, same, schemes, selection⟩ := forest.cut cut
  cases declaration with
  | handler scope annotation clauses coverage unique declarations capabilities modes =>
      obtain ⟨argument, input, resumeEffects, closeEffects, family, signature, resume, close, located, checked, body⟩ :=
        SourceContextualClauses.Lexical.selected_checked_body declarations schemes selected found available
      have actual := ScopedTyping.handler_cut_instance cut
      rw [actual] at signature
      exact ⟨capturedScope, tailScope, answer, residual, argument, input, resumeEffects, closeEffects, family,
        same, annotation, signature, resume, close, located, checked, body⟩
/-- Requests from a running callback can select a retained handler inside an
abandoned suffix. Its rich clause source and contextual capability certificate
come from that actual handler and its actual remaining interpretation scope. -/
theorem unwind_selected_body
    (cut : HandlerCut requested whole capture tail handler)
    (source : UnwindSource operations policy contracts tables families world whole demand requirements dependencyScope)
    (forest : Forest outward tables families whole dependencyScope outside)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row held = some row) :
    ∃ (capturedScope tailScope : SourceDependencyCapture.Scope) (answer : Value) (residual : List Instance)
      (argument input : Value) (resumeEffects closeEffects : List Instance) (family : Nat → Dependencies),
      dependencyScope = capturedScope.append tailScope ∧
      answer.erase.port = ScopedPorts.eraseType handler.answer ∧
      operations requested operation = some (argument, input) ∧
      (code.requiredActions.resume = true → resumeEffects = residual) ∧
      (code.requiredActions.dispose = true → closeEffects = residual) ∧
      (lookupDependencies operation (families handler)).bind (modeDependencies held) = some family ∧
      FamilyAt outward code.requiredActions family (tailScope.append outside) ∧
      ∀ owner (contract : Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = held → contract.closeDemand.Perm contract.resumeDemand →
        Body operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
          (Environment.empty.extend parameter argument) code answer ⟨owner, contract.erase, offered.dispose, row⟩ (family owner) := by
  obtain ⟨requirements, retained, _⟩ := source.mode_source (actions := fun _ => none)
  exact mode_selected_body cut retained forest selected found available
end Ash.OneShot.SourceContextualCapture.Lexical
#print axioms Ash.OneShot.SourceContextualCapture.Lexical.unwind_selected_body

#print axioms Ash.OneShot.SourceContextualCapture.Lexical.mode_selected_body

namespace Ash.OneShot.SourceContextualCapture.Lexical.Recursive
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyCapture (Scope Realizes select chosen lookupDependencies modeDependencies)
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceDependencyChecks.Lexical.ReturnHints.Recursive (Local Pending)
open SourceContextualRechecking (handlers frameHandlers checkForest checkFrame check_forest_push)
open SourceContextualRequirements (DeclarationRecipes checkRequirements)
open OwnerPhaseTransitions (Phases spend introduce)

theorem handler_member (cut : HandlerCut requested whole captured tail handler) : handler ∈ handlers whole := by
  induction cut with
  | hit => simp [handlers, frameHandlers]
  | push entry rest captured tail handler miss next ih => exact List.mem_append_right _ ih
  | live owner input answer saved caller rest captured tail handler next ih => exact List.mem_append_right _ ih
  | spent owner answer caller rest captured tail handler next ih => exact ih

/-- The existing finite forest test supplies the selected handler's requirement
check at its exact lexical tail. No separately chosen receiving annotation is
used; the same cut determines the source pieces and operation selection. -/
theorem checked_handler_cut
    (cut : HandlerCut requested whole captured tail handler)
    (realized : Realizes tables families scope whole)
    (checked : checkForest required whole scope outside = true) :
    ∃ capturedScope tailScope,
      Realizes tables families capturedScope captured ∧ Realizes tables families tailScope tail ∧
      scope = capturedScope.append tailScope ∧
      checkRequirements (tailScope.append outside) (required handler) = true ∧
      ∀ operation, select requested operation scope =
        chosen operation (tables handler) (families handler) capturedScope tailScope := by
  induction cut generalizing scope with
  | hit handler tail same => cases realized with
    | push frame rest => cases frame with
      | handler =>
        rw [checkForest, Bool.and_eq_true] at checked
        refine ⟨_, _, .push .handler .nil, rest, rfl, checked.1, ?_⟩
        intro operation
        simp only [select, if_pos same.symm, chosen]
        rfl
  | push entry rest captured tail handler miss next ih => cases realized with
    | push frame rest =>
      rw [check_forest_push frame, Bool.and_eq_true] at checked
      obtain ⟨capturedScope, tailScope, inside, remaining, recomposed, supplied, selected⟩ := ih rest checked.2
      refine ⟨_, _, .push frame inside, remaining, ?_, supplied, ?_⟩
      · rw [frame.append, ← recomposed]
      · intro operation
        rw [frame.select_miss miss, selected operation, SourceDependencyCapture.chosen_prepend]
  | live owner input answer saved caller rest captured tail handler next ih => cases realized with
    | live inside rest =>
      rw [checkForest, Bool.and_eq_true] at checked
      obtain ⟨capturedScope, tailScope, captured, remaining, recomposed, supplied, selected⟩ := ih rest checked.2
      refine ⟨_, _, .live inside captured, remaining, ?_, supplied, ?_⟩
      · simp only [Scope.append, ← recomposed]
      · intro operation
        rw [select, selected operation, SourceDependencyCapture.chosen_prepend]
  | spent owner answer caller rest captured tail handler next ih => cases realized with
    | spent rest =>
      obtain ⟨capturedScope, tailScope, captured, remaining, recomposed, supplied, selected⟩ := ih rest checked
      refine ⟨_, _, .spent captured, remaining, ?_, supplied, ?_⟩
      · simp only [Scope.append, ← recomposed]
      · intro operation
        rw [select, selected operation, SourceDependencyCapture.chosen_prepend]

/-- Derive the primitive continuation interface at the actual selected clause.
This factors capture mechanics from the structural clause grammar. It assumes
neither a selected-clause check nor a successful successor computation. -/
theorem capture_clause_interface {hints : ReturnHints wholeScope}
    (cut : HandlerCut requested whole capture tail handler)
    (matching : ReturnHints.Matches tables families hints whole)
    (retained : Pending outward actions phases world hints .nil .ordinary finalMode)
    (request : Local outward actions phases world (.request requested operation) hints)
    (checked : checkForest required whole wholeScope .nil = true)
    (modes : SourceTemplates.ClauseModes handler.clauses (tables handler))
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (offeredKnown : lookup operation (tables handler) = some offered)
    (fresh : actions owner = none) (consumed : phases owner = .consumed) :
    ∃ capturedScope tailScope, ∃ capturedHints : ReturnHints capturedScope,
    ∃ tailHints : ReturnHints tailScope, ∃ family,
      wholeScope = capturedScope.append tailScope ∧
      (lookupDependencies operation (families handler)).bind (modeDependencies capturedScope.held) = some family ∧
      ReturnHints.Matches tables families (.live (owner := owner) capturedHints tailHints)
        (.live owner input answer capture caller tail) ∧
      (code.requiredActions.resume = true →
        Local outward (actions.insert owner code.requiredActions) (introduce phases owner) world
          (.invoke ⟨owner, .resume⟩) (.live (owner := owner) capturedHints tailHints)) ∧
      (code.requiredActions.dispose = true →
        Local outward (actions.insert owner code.requiredActions) (introduce phases owner) world
          (.invoke ⟨owner, .dispose⟩) (.live (owner := owner) capturedHints tailHints)) ∧
      Pending outward (actions.insert owner code.requiredActions) (introduce phases owner) world
        (.live (owner := owner) capturedHints tailHints) .nil .ordinary finalMode ∧
      checkRequirements tailScope (required handler) = true ∧
      checkForest required (.live owner input answer capture caller tail) (.live owner capturedScope tailScope) .nil = true := by
  obtain ⟨capturedScope, tailScope, saved, waiting, sameScope, supplied, selection⟩ :=
    checked_handler_cut cut matching.erases checked
  obtain ⟨localCapture, localTail, capHints, tailHints, middle, localScope, localHints,
    capMatched, tailMatched, capChecked, tailChecked⟩ := retained.handler_cut matching cut
  obtain ⟨rfl, rfl⟩ := saved.append_scopes_unique capMatched.erases (sameScope.symm.trans localScope)
  have guard := request.request_guard
  obtain ⟨alternatives, selectedScope⟩ : ∃ alternatives,
      select requested operation wholeScope = some (.handler capturedScope tailScope offered alternatives) := by
    cases found : lookupDependencies operation (families handler) with
    | none =>
      have missing : select requested operation wholeScope = none := by
        simpa only [chosen, offeredKnown, found] using selection operation
      cases guard with
      | builtin actual | handler actual => rw [missing] at actual; cases actual
    | some alternatives => exact ⟨alternatives, by simpa only [chosen, offeredKnown, found] using selection operation⟩
  obtain ⟨family, familyKnown⟩ : ∃ family,
      (lookupDependencies operation (families handler)).bind (modeDependencies capturedScope.held) = some family := by
    cases guard with
    | builtin actual => cases Option.some.inj (selectedScope.symm.trans actual)
    | handler actual permitted row body =>
      cases Option.some.inj (selectedScope.symm.trans actual)
      cases found : lookupDependencies operation (families handler) with
      | none =>
        have impossible := (selection operation).symm.trans selectedScope
        simp only [chosen, offeredKnown, found] at impossible
        cases impossible
      | some actualModes =>
        have equal := (selection operation).symm.trans selectedScope
        simp only [chosen, offeredKnown, found] at equal
        cases Option.some.inj equal
        exact ⟨_, by simpa only [found, Option.bind_some] using body⟩
  have permissions := Syntax.fresh_usage_insert_extends (rights := code.requiredActions) fresh
  have oldRetained : Pending outward (actions.insert owner code.requiredActions) phases world
      (.live (owner := owner) capHints tailHints) .nil .ordinary finalMode :=
    .live (SourceDependencySchemes.Lexical.Recursive.pending_transport capChecked
      (fun _ ready => ready) permissions (List.Subset.refl _))
      (SourceDependencySchemes.Lexical.Recursive.pending_transport tailChecked
        (fun _ ready => ready) permissions (List.Subset.refl _))
  have phaseSame := OwnerCaptureContracts.spend_introduced (owner := owner) consumed
  have consumedRetained : Pending outward (actions.insert owner code.requiredActions)
      (spend (introduce phases owner) owner) world (.live (owner := owner) capHints tailHints) .nil .ordinary finalMode :=
    phaseSame.symm ▸ oldRetained
  have known : (actions.insert owner code.requiredActions) owner = some code.requiredActions := by simp [Syntax.UsageTickets.insert]
  have ready : introduce phases owner owner = .available := by simp [introduce]
  have resumeLocal := fun permission => SourceDependencyNeutral.Lexical.Recursive.resume_clause_from_retained
    known permission ready consumedRetained
  have disposeLocal : code.requiredActions.dispose = true → Local outward (actions.insert owner code.requiredActions)
      (introduce phases owner) world (.invoke ⟨owner, .dispose⟩) (.live (owner := owner) capHints tailHints) := by
    intro permission
    obtain ⟨actual, declared, permitted⟩ := SourceTemplates.selected_clause_mode selected modes
    cases Option.some.inj (offeredKnown.symm.trans declared)
    have disposes := permitted permission
    apply SourceDependencyNeutral.Lexical.Recursive.dispose_clause_from_retained known permission ready
      (guard.disposing_unprotected selectedScope disposes) consumedRetained
    rw [phaseSame]
    cases request with
    | request guard callbacks bounded =>
      exact SourceDependencySchemes.Lexical.Recursive.pending_transport
        (callbacks capHints tailHints _ _ localHints selectedScope disposes)
        (fun _ ready => ready) permissions (List.Subset.refl _)
  have forestChecked : checkForest required (.live owner input answer capture caller tail)
      (.live owner capturedScope tailScope) .nil = true := by
    rw [handler_cut_reconstructs cut, sameScope,
      SourceContextualRechecking.Lexical.check_forest_append saved waiting] at checked
    exact checked
  exact ⟨_, _, capHints, tailHints, family, sameScope, familyKnown, .live capMatched tailMatched,
    resumeLocal, disposeLocal,
    SourceDependencySchemes.Lexical.Recursive.pending_transport oldRetained
      SourceDependencySchemes.introduce_extends (fun _ _ known => known) (List.Subset.refl _),
    by simpa only [SourceDependencyProjection.scope_append_nil] using supplied, forestChecked⟩

/-- Compile the selected structural recipe using the independently derived
capture interface. Installed evidence and its finite scope check survive. -/
theorem capture_selected_recipe {hints : ReturnHints wholeScope}
    (cut : HandlerCut requested whole capture tail handler)
    (matching : ReturnHints.Matches tables families hints whole)
    (retained : Pending outward actions phases world hints .nil .ordinary finalMode)
    (request : Local outward actions phases world (.request requested operation) hints)
    (recipes : ∀ installed ∈ handlers whole,
      DeclarationRecipes outward installed.clauses (families installed) (required installed))
    (checked : checkForest required whole wholeScope .nil = true)
    (modes : SourceTemplates.ClauseModes handler.clauses (tables handler))
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (offeredKnown : lookup operation (tables handler) = some offered)
    (fresh : actions owner = none) (consumed : phases owner = .consumed) :
    ∃ capturedScope tailScope, ∃ capturedHints : ReturnHints capturedScope,
    ∃ tailHints : ReturnHints tailScope, ∃ family,
      wholeScope = capturedScope.append tailScope ∧
      (lookupDependencies operation (families handler)).bind (modeDependencies capturedScope.held) = some family ∧
      ReturnHints.Matches tables families (.live (owner := owner) capturedHints tailHints)
        (.live owner input answer capture caller tail) ∧
      Local outward (actions.insert owner code.requiredActions) (introduce phases owner) world
        (family owner) (.live (owner := owner) capturedHints tailHints) ∧
      Pending outward (actions.insert owner code.requiredActions) (introduce phases owner) world
        (.live (owner := owner) capturedHints tailHints) .nil .ordinary finalMode ∧
      checkForest required (.live owner input answer capture caller tail) (.live owner capturedScope tailScope) .nil = true ∧
      (∀ installed ∈ handlers (.live owner input answer capture caller tail),
        DeclarationRecipes outward installed.clauses (families installed) (required installed)) := by
  obtain ⟨capturedScope, tailScope, capturedHints, tailHints, family, sameScope, familyKnown,
    matched, resumeLocal, disposeLocal, nextPending, supplied, forestChecked⟩ :=
    capture_clause_interface cut matching retained request checked modes selected offeredKnown fresh consumed
  refine ⟨_, _, capturedHints, tailHints, family, sameScope, familyKnown, matched,
    SourceContextualRequirements.Lexical.Recursive.selected_clause_local
      (recipes handler (handler_member cut)) selected familyKnown supplied resumeLocal disposeLocal,
    nextPending, forestChecked, ?_⟩
  intro installed member
  apply recipes installed
  rw [handler_cut_reconstructs cut, SourceContextualRechecking.handlers_append]
  exact member

end Ash.OneShot.SourceContextualCapture.Lexical.Recursive
#print axioms Ash.OneShot.SourceContextualCapture.Lexical.Recursive.checked_handler_cut
#print axioms Ash.OneShot.SourceContextualCapture.Lexical.Recursive.capture_selected_recipe

#print axioms Ash.OneShot.SourceContextualCapture.Lexical.Recursive.capture_clause_interface
