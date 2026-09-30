import CoreInitialExample

/-! Finite admission construction for the full normalized kernel example.
This does not identify the exported Rust graph with the normalization target. -/
namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreKernelAdmission
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Contracts Contract Value Environment)
open SourceDeclarationPlans
open SourcePlanSignatures (signature)
open RecursiveRequirements (Requirements)
open InstallationSupport
open CoreInitialExample

variable {world : List Nat} {environment : Environment} {contracts : Contracts}
  {owners : ContractRows contracts} {environmentRows : EnvironmentRows environment}

def clause (identity : Nat) : Code :=
  .branch (.variable 6) (.bind 8 (.resume 7 .unit) (write identity 11)) (.discard 7)
def clauseDependencies (identity owner : Nat) : SourceDependencyAnnotations.Dependencies :=
  .sequence .pure (.choice
    (.sequence (.sequence .pure (.invoke ⟨owner, .resume⟩))
      (.sequence .pure (.request (.cell identity) 1)))
    (.invoke ⟨owner, .dispose⟩))
def clausePlan (identity owner : Nat) : Plan (clauseDependencies identity owner) :=
  Plan.sequence Plan.pure
    (Plan.choice (Plan.sequence (Plan.sequence Plan.pure (Plan.invoke (key := ⟨owner, .resume⟩)))
      (writePlan identity)) (Plan.invoke (key := ⟨owner, .dispose⟩)))

theorem clauseSource (issued : identity ∈ world) (contract : Contract)
    (input : contract.input = .unit) (answer : contract.answer = .unit)
    (resume : contract.resumeEffects = [.cell identity])
    (close : contract.closeEffects = [.cell identity]) (held : contract.held = false)
    (balance : contract.closeDemand.Perm contract.resumeDemand) :
    SourcePlannedSources.Expression operations policy (contracts.insert owner contract) world [.cell identity]
      (.ticket 7 owner) (environment.extend 6 .boolean) (clause identity) .unit
      ([] ++ (([] ++ (owner :: contract.resumeDemand)) ++ []))
      (clauseRequirements identity owner contract.erase.erase balance) (signature (clausePlan identity owner)) := by
  rcases contract with ⟨inputType, answerType, protectedMode, resumeDemand, resumeRow, closeDemand, closeRow, resumeEffects, closeEffects⟩
  cases input; cases answer
  apply SourcePlannedSources.Expression.branch
  · exact .variable (by simp [Environment.extend]) (by intro resource member; cases member)
  · apply SourcePlannedSources.Expression.bind
    · exact .resume (by simp [Contracts.insert]) rfl rfl .unit
        (by rw [resume]; exact List.Subset.refl _) (by intro resource member; cases member)
    · exact writeSource issued List.mem_cons_self 11
  · exact .discard (by simp [Contracts.insert]) rfl rfl held (by rw [close]; exact List.Subset.refl _)

theorem clauseAuth (issued : identity ∈ world) (contract : Contract)
    (input : contract.input = .unit) (answer : contract.answer = .unit)
    (resume : contract.resumeEffects = [.cell identity])
    (close : contract.closeEffects = [.cell identity]) (held : contract.held = false)
    (balance : contract.closeDemand.Perm contract.resumeDemand) :
    Auth operations policy ports
      (owners.insert owner (input.symm ▸ ValueRows.unit) (answer.symm ▸ ValueRows.unit))
      (environmentRows.extend 6 .boolean)
      (clauseSource (contracts := contracts) issued contract input answer resume close held balance)
      .unit (.sequence .pure (.choice (.sequence (.sequence .pure .invoke)
        (.sequence .pure .request)) .invoke)) := by
  rcases contract with ⟨inputType, answerType, protectedMode, resumeDemand, resumeRow, closeDemand, closeRow, resumeEffects, closeEffects⟩
  cases input; cases answer
  apply Auth.branch
  · exact Auth.variable (known := by simp [Environment.extend]) (formed := by intro resource member; cases member)
  · apply Auth.bind
    · apply Auth.resume (known := by simp [Contracts.insert]) (resolved := rfl) (permission := rfl)
        (admitted := by rw [resume]; exact List.Subset.refl _) (formed := by intro resource member; cases member)
      simp only [ContractRows.insert]
      exact .unit
    · exact writeAuth issued List.mem_cons_self 11
  · exact Auth.discard (known := by simp [Contracts.insert]) (resolved := rfl)
      (permission := rfl) (unprotected := held) (admitted := by rw [close]; exact List.Subset.refl _)


def clauses (identity : Nat) : Clauses := .cons 0 6 7 (clause identity) .nil
def table (identity : Nat) : List (Nat × ClauseContract) :=
  [(0, ⟨true, some (callbackFootprint identity), none⟩)]
def declarationPlans (identity : Nat) :=
  ClausePlans.cons (operation := 0) (parameter := 6) (binder := 7) (body := clause identity)
    (ModePlans.available (clausePlan identity)) ModePlans.unavailable ClausePlans.nil

theorem ordinaryBody (issued : identity ∈ world) (owner : Nat) (contract : Contract)
    (_fresh : contracts owner = none) (input : contract.input = .unit) (answer : contract.answer = .unit)
    (resume : contract.resumeEffects = [.cell identity]) (close : contract.closeEffects = [.cell identity])
    (held : contract.held = false) (balance : contract.closeDemand.Perm contract.resumeDemand) :
    SourcePlannedSources.Body operations policy (contracts.insert owner contract) world [.cell identity]
      (.ticket 7 owner) (environment.extend 6 .boolean) (clause identity) .unit
      ⟨owner, contract.erase.erase, true, callbackFootprint identity⟩ (signature (clausePlan identity owner)) :=
  .typed (clauseSource issued contract input answer resume close held balance)
    (clauseRows balance) (clauseProtectedRows balance)

theorem ordinary (issued : identity ∈ world) :
    SourcePlannedSources.Offer operations policy contracts world environment [.cell identity]
      6 7 .boolean .unit .unit [.cell identity] [.cell identity] (clause identity)
      false true (some (callbackFootprint identity)) (.available (clausePlan identity)) :=
  .available (fun _ => rfl) (fun _ => rfl) (ordinaryBody issued)

theorem declarations (issued : identity ∈ world) :
    SourcePlannedSources.Declarations operations policy contracts world environment [.cell identity]
      effect .unit (clauses identity) (table identity) (declarationPlans identity) :=
  .cons rfl (ordinary issued) .unavailable .nil

theorem clausesTyped (issued : identity ∈ world) :
    ScopedPorts.ClausesTyped operations.erase.erase.ports world environment.erase.erase.ports
      effect .unit [.cell identity] (clauses identity) := by
  apply ScopedPorts.ClausesTyped.cons rfl
  · apply ScopedPorts.Typed.branch
    · exact .variable (by simp [ScopedPorts.TypeEnv.extend, Value.erase, SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port]) (by intro resource member; cases member)
    · apply ScopedPorts.Typed.bind
      · exact .resume .unit (List.Subset.refl _) (by intro resource member; cases member)
      · exact .perform rfl List.mem_cons_self (.pair (.reference issued) .integer)
          (by intro resource member; cases member)
    · exact .discard (List.Subset.refl _)
  · exact .nil

theorem capabilities : ClausesUse policy (clauses identity) :=
  .cons (.branch .variable (.bind (.resume rfl .unit) (.perform (.pair .resourceRef .integer)))
    (.discard rfl)) .nil

theorem coverage : ScopedPorts.Covers operations.erase.erase.ports effect (clauses identity) := by
  intro operation input output known
  cases operation with
  | zero => simp [clauses, ScopedTyping.clauseKeys]
  | succ operation => simp [operations, effect, SourcePlannedTyping.Operations.erase,
      SourceDependencyAnnotations.Operations.erase, CoherentSourceTypes.Operations.ports] at known

def declarationRows (identity : Nat) : ClauseRows (SourcePlanSignatures.clauseSignatures (declarationPlans identity)) :=
  .cons (.available (fun _ => .sequence .pure
    (.choice (.sequence (.sequence .pure .invoke) (.sequence .pure .request)) .invoke)))
    .unavailable .nil [identity]

def handled (identity : Nat) : Code :=
  .handle (Instantiation.freezeEffect effect) (guardedBody identity) (clauses identity)
def handledPlan (identity : Nat) := Plan.handler (effect := effect) (table := table identity)
  [(.cell identity, 1)] (declarationPlans identity) (guardedPlan identity)
def handledRequirements (identity : Nat) : Requirements [] :=
  (guardedRequirements identity).prepend [.ordinary (.handler effect 0 (table identity))]
def handledRows (identity : Nat) : Rows (signature (handledPlan identity)) :=
  .handler (declarationRows identity) (.sequence .pure
    (.cleanup (callbackFootprint identity) (.sequence .pure .request)
      (.sequence (.sequence .pure .request)
        (.sequence (.sequence .pure .request) (.sequence .pure .request)))))

theorem handledSource (issued : identity ∈ world) :
    SourcePlannedSources.Expression operations policy contracts world [.cell identity] .none environment
      (handled identity) .unit [] (handledRequirements identity) (signature (handledPlan identity)) :=
  .handler (guardedSource issued (by simp) List.mem_cons_self) (clausesTyped issued)
    capabilities coverage (by simp [clauses, ScopedTyping.clauseKeys]) (List.Subset.refl _) (table identity)
    (.cons (fun _ => rfl) .nil) (declarations issued)

theorem handledAuth (issued : identity ∈ world) :
    Auth operations policy ports owners environmentRows (handledSource issued) .unit (handledRows identity) := by
  apply Auth.handler (body := guardedSource issued (by simp) List.mem_cons_self)
    (declarations := declarations issued) (clauses := clausesTyped issued)
    (capabilities := capabilities) (coverage := coverage) (unique := by simp [clauses, ScopedTyping.clauseKeys])
    (admitted := List.Subset.refl _) (modes := .cons (fun _ => rfl) .nil)
  · exact guardedAuth issued (by simp) List.mem_cons_self
  · apply AuthDeclarations.cons (known := (rfl : operations effect 0 = some (.boolean, .unit)))
      (supportBound := [identity]) (ordinary := ordinary issued)
      (protectedMode := .unavailable) (rest := .nil)
    · apply AuthOffer.available (source := ordinaryBody issued)
        (resumeInterface := fun _ => rfl) (closeInterface := fun _ => rfl)
      intro owner contract fresh input answer resume close held balance
      exact AuthBody.typed (rows := clauseRows balance) (closingRows := clauseProtectedRows balance)
        (clauseAuth issued contract input answer resume close held balance)
    · exact .unavailable
    · exact .nil
    · simp [clause, write, Code.dependencies, Syntax.without,
        LambdaPortCaptureSupport.portSupport, ScopedPorts.Support.evaluate, Instance.resources,
        Environment.extend, Value.erase, SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port,
        ScopedPorts.Port.resources]


def cellBody (identity : Nat) : Code := .bind 20 (handled identity) (read identity)
def cellBodyPlan (identity : Nat) := Plan.sequence (handledPlan identity) (readPlan identity)
def cellBodyRequirements (identity : Nat) : Requirements [] :=
  .sequence (handledRequirements identity) (readRequirements identity)
def emptyRequest : Requirements [] := .emitAfter empty [] []
def hiddenBodyRequirements : Requirements [] :=
  .sequence
    (.emitAfter (.sequence empty (.sequence emptyRequest (.sequence emptyRequest emptyRequest))) [] [])
    emptyRequest

theorem cellBodySource (identity : Nat) :
    SourcePlannedSources.Expression operations policy InitialAdmission.contracts [identity] [.cell identity] .none
      (fun _ => none) (cellBody identity) .integer [] (cellBodyRequirements identity) (signature (cellBodyPlan identity)) :=
  .bind (handledSource List.mem_cons_self) (readSource List.mem_cons_self List.mem_cons_self)

theorem cellBodyAuth (identity : Nat) :
    Auth operations policy ports InitialAdmission.owners emptyRows (cellBodySource identity) .integer
      (.sequence (handledRows identity) (.sequence .pure .request)) :=
  .bind (handledAuth List.mem_cons_self) (readAuth List.mem_cons_self List.mem_cons_self)

theorem cellBodyHidden (identity : Nat) :
    ResourceRequirements.Hides identity (cellBodyRequirements identity) hiddenBodyRequirements := by
  let layers : ProtectionContracts.Context := [.handler effect 0 (table identity)]
  have pure : ResourceRequirements.Hides identity
      (.request [OwnerPhases.Entry.ordinary (.handler effect 0 (table identity))] []) empty :=
    .requestThrough (layers := [.handler effect 0 (table identity)]) (raw := []) (interpreted := []) rfl
  have user : ResourceRequirements.Hides identity
      ((requestRequirements).prepend [OwnerPhases.Entry.ordinary (.handler effect 0 (table identity))]) emptyRequest := by
    simpa [layers, requestRequirements, emptyRequest, empty, Requirements.prepend,
      callbackFootprint, CallableProtection.outsideCell] using
      (ResourceRequirements.Hides.emitThrough (identity := identity) pure
        (layers := layers) (raw := [⟨effect, 0, false⟩]) (interpreted := callbackFootprint identity) rfl)
  have writeHidden : ResourceRequirements.Hides identity
      ((writeRequirements identity).prepend [OwnerPhases.Entry.ordinary (.handler effect 0 (table identity))]) emptyRequest := by
    simpa [layers, writeRequirements, emptyRequest, empty, Requirements.prepend,
      CallableProtection.outsideCell] using
      (ResourceRequirements.Hides.emitThrough (identity := identity) pure
        (layers := layers) (raw := [⟨.cell identity, 1, false⟩])
        (interpreted := [⟨.cell identity, 1, false⟩]) rfl)
  have guarded : ResourceRequirements.Hides identity (handledRequirements identity)
      (.emitAfter (.sequence empty (.sequence emptyRequest (.sequence emptyRequest emptyRequest))) [] []) := by
    simpa [layers, empty, handledRequirements, guardedRequirements, guardedPlan, callbackFootprint,
      ProtectionContracts.qualify, Requirements.prepend, protectedRequirements, CallableProtection.outsideCell] using
      (ResourceRequirements.Hides.emitThrough (identity := identity)
        (.sequence pure (.sequence user (.sequence user writeHidden)))
        (layers := layers) (raw := [⟨.cell identity, 1, true⟩])
        (interpreted := [⟨.cell identity, 1, true⟩]) rfl)
  exact .sequence guarded (by
    simpa [empty, readRequirements, emptyRequest, CallableProtection.outsideCell] using
      (ResourceRequirements.Hides.emitAfter (identity := identity)
        (raw := [⟨.cell identity, 0, false⟩]) (ResourceRequirements.Hides.request (raw := []))))

def template : Code :=
  .bind 20
    (.handle (Instantiation.freezeEffect effect)
      (.cleanup (.lambda 10 (writeAt (.bound 0) 7))
        (.bind 4 (request true) (.bind 5 (request false) (writeAt (.bound 0) 99))))
      (.cons 0 6 7 (.branch (.variable 6)
        (.bind 8 (.resume 7 .unit) (writeAt (.bound 0) 11)) (.discard 7)) .nil))
    (readAt (.bound 0))

theorem instantiated (identity : Nat) :
    template.instantiate (Instantiation.Environment.empty.bind 0 identity) = cellBody identity := rfl

def resourcePlan := Plan.sequence Plan.pure (Plan.resource cellBodyPlan)
def resourceRequirements : Requirements [] := .sequence empty hiddenBodyRequirements

theorem resourceSource :
    SourcePlannedSources.Expression operations policy InitialAdmission.contracts [] [] .none (fun _ => none)
      normalized .integer [] resourceRequirements (signature resourcePlan) := by
  apply SourcePlannedSources.Expression.resource (code := template) (residual := []) .integer
    (body := fun identity _ => by simpa only [instantiated, List.nil_append] using cellBodySource identity)
    (formed := by intro resource member; cases member)
    (effectsBound := List.nil_subset _) (admitted := List.nil_subset _)
    (hidden := fun identity _ => cellBodyHidden identity)

theorem resourceAuth : Auth operations policy ports InitialAdmission.owners emptyRows resourceSource .integer
    (.sequence .pure (.resource (fun identity =>
      .sequence (handledRows identity) (.sequence .pure .request)))) := by
  apply Auth.resource (code := template) (residual := []) .integer
    (body := fun identity _ => by simpa only [instantiated, List.nil_append] using cellBodySource identity)
    (formed := by intro resource member; cases member)
    (effectsBound := List.nil_subset _) (admitted := List.nil_subset _)
    (hidden := fun identity _ => cellBodyHidden identity)
  intro identity fresh
  simpa only [instantiated, List.nil_append] using cellBodyAuth identity


/-- A consuming resume crosses the retained plain write suffix, whose request
is discharged by the actual cell receiver. -/
theorem effectfulPlainResume :
    SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local []
      Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.Examples.actions
      (OwnerPhaseTransitions.available [7]) [42]
      (.sequence (.invoke ⟨7, .resume⟩) (.sequence .pure (.request (.cell 42) 1)))
      Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.Examples.receiver := by
  apply SourcePlainSuffixTransport.plain_suffix_admission
    (SourceRequestFootprints.Footprint.sequence .pure .request) (by decide)
  apply SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local.resume
    (rights := ⟨true, true⟩) (front := .nil) .hit
  · simp [Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.Examples.actions]
  · rfl
  · simp [OwnerPhaseTransitions.available]
  · exact .spent (.cell .nil)

/-- The resume branch retains its actual write suffix; its finite requirement
is checked at the receiver after the continuation has been consumed. -/
theorem clauseRecipe :
    ClauseRecipe outward (clause identity).requiredActions [(.cell identity, 1)]
      (clauseDependencies identity) := by
  apply ClauseRecipe.sequence SourceRequestFootprints.Footprint.pure
  apply ClauseRecipe.choice (firstRequired := [(.cell identity, 1)]) (secondRequired := [])
  · have consumingRecipe : ClauseRecipe outward (clause identity).requiredActions []
        (fun owner => .sequence .pure (.invoke ⟨owner, .resume⟩)) :=
      .sequence .pure (.existing (.resume rfl))
    have continuedRecipe := ClauseRecipe.suffix consumingRecipe
      (SourceRequestFootprints.Footprint.sequence .pure
        (SourceRequestFootprints.Footprint.request (effect := .cell identity) (operation := 1)))
    simpa [externalRequirements, SourceContextualRequirements.providerScope,
      SourceHandlerRequirements.outwardRequirements, SourceHandlerRequirements.reaches] using continuedRecipe
  · exact .existing (.dispose rfl)

theorem declarationRecipe :
    ClauseDeclarations outward (clauses identity)
      [(0, some (clauseDependencies identity), none)] [(.cell identity, 1)] :=
  .cons (.available clauseRecipe) .unavailable .nil

/-- Omitting the actual receiver fails the finite suffix check. -/
theorem suffixMissingReceiver :
    SourceContextualHints.checkRequirements SourceDependencyCapture.Scope.nil
      [(.cell identity, 1)] = false := by
  rfl

theorem resourceCertified :
    SourcePlannedChecks.Certified (evidence := declarationPolicy) [] [] resourcePlan := by
  letI : SourcePlannedChecks.DeclarationPolicy := declarationPolicy
  unfold resourcePlan
  apply SourcePlannedChecks.Certified.sequence .pure
  apply SourcePlannedChecks.Certified.resource
  intro identity fresh
  unfold cellBodyPlan handledPlan
  apply SourcePlannedChecks.Certified.sequence
  · apply SourcePlannedChecks.Certified.handler declarationRecipe
    · apply SourcePlannedChecks.CertifiedClauses.cons
      · apply SourcePlannedChecks.CertifiedModes.available
        intro owner
        exact .sequence .pure (.choice (.sequence (.sequence .pure .invoke)
          (.sequence .pure .request)) .invoke)
      · exact .unavailable
      · exact .nil
    · exact .sequence .pure (.cleanup (.sequence .pure .request)
        (.sequence (.sequence .pure .request)
          (.sequence (.sequence .pure .request) (.sequence .pure .request))))
  · exact .sequence .pure .request

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreKernelAdmission

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreKernelAdmission.resourceSource
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreKernelAdmission.resourceAuth
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreKernelAdmission.effectfulPlainResume
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreKernelAdmission.clauseRecipe

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreKernelAdmission.resourceCertified
