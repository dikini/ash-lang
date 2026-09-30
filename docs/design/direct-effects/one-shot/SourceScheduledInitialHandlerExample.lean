import SourceScheduledInitialAdmission

/-! A closed initial program installs a handler, performs its operation, and
consumes the captured continuation by lexical disposal. Every admission field
is constructed from the finite source and its structural annotations. -/
namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Value)
open RecursiveRequirements (Requirements)
open SourceDeclarationPlans
open SourcePlanSignatures (signature)
open InstallationSupport

def effect : Instance := .user 0 []
def policy : Syntax.TicketPolicy := fun _ => ⟨false, true⟩
def operations : Operations := fun requested operation =>
  if requested = effect ∧ operation = 0 then some (.unit, .unit) else none

theorem builtinSignatures : SourceScheduledBuiltinSignatures.Compatible operations := by
  intro identity operation input output known
  simp [operations, SourcePlannedTyping.Operations.erase,
    SourceDependencyAnnotations.Operations.erase, CoherentSourceTypes.Operations.ports, effect] at known

def ports : OperationRows operations := by
  intro requested operation input output known
  simp only [operations] at known
  split at known
  · cases known; exact ⟨.unit, .unit⟩
  · cases known

def expression : ScopedExpressions.Code :=
  .handle (Instantiation.freezeEffect effect)
    (.perform (Instantiation.freezeEffect effect) 0 .unit) (HandledRequest.clauses 0)

def declarationRows : ClauseRows (SourcePlanSignatures.clauseSignatures (HandledRequest.declarations 0)) :=
  .cons (.available (fun _ => .invoke)) .unavailable .nil

def rows : Rows (signature (HandledRequest.plan effect 0)) :=
  .handler declarationRows (.sequence .pure .request)

theorem ordinaryBody (owner : Nat) (contract : SourcePlannedTyping.Contract)
    (_fresh : contracts owner = none) (_input : contract.input = .unit) (_answer : contract.answer = .unit)
    (_resume : contract.resumeEffects = []) (close : contract.closeEffects = []) (held : contract.held = false)
    (_demands : contract.closeDemand.Perm contract.resumeDemand) :
    SourcePlannedSources.Body operations policy (contracts.insert owner contract) [] [] (.ticket 1 owner)
      (SourcePlannedTyping.Environment.extend (fun _ => none) 0 .unit) (.discard 1) .unit ⟨owner, contract.erase.erase, true, []⟩
      (signature (Plan.invoke (key := ⟨owner, .dispose⟩))) :=
  .typed (.discard (by simp [SourcePlannedTyping.Contracts.insert]) rfl rfl held
    (by rw [close]; exact List.Subset.refl [])) ClauseRowAdmission.discard_rows ClauseRowAdmission.protected_discard_rows

theorem ordinary : SourcePlannedSources.Offer operations policy contracts [] (fun _ => none) []
    0 1 .unit .unit .unit [] [] (.discard 1) false true (some [])
    (.available (fun owner => Plan.invoke (key := ⟨owner, .dispose⟩))) :=
  .available (fun _ => rfl) (fun _ => rfl) ordinaryBody

theorem declarations : SourcePlannedSources.Declarations operations policy contracts [] (fun _ => none) [] effect .unit
    (HandledRequest.clauses 0) (HandledRequest.table 0) (HandledRequest.declarations 0) :=
  .cons rfl ordinary .unavailable .nil

def requirements : Requirements [] :=
  (Requirements.emitAfter (.request [] []) [] [⟨effect, 0, false⟩]).prepend [.ordinary (.handler effect 0 (HandledRequest.table 0))]

theorem bodySource : SourcePlannedSources.Expression operations policy contracts [] [effect] .none (fun _ => none)
    (.perform (Instantiation.freezeEffect effect) 0 .unit) .unit []
    (.emitAfter (.request [] []) [] [⟨effect, 0, false⟩]) (signature (.sequence .pure (Plan.request (effect := effect) (operation := 0)))) :=
  .perform rfl (by simp) .unit (List.nil_subset _)

theorem clausesTyped : ScopedPorts.ClausesTyped operations.erase.erase.ports []
    (fun _ => none) effect .unit [] (HandledRequest.clauses 0) :=
  .cons rfl (.discard (List.Subset.refl [])) .nil

theorem coverage : ScopedPorts.Covers operations.erase.erase.ports effect (HandledRequest.clauses 0) := by
  intro operation input output known
  simp only [SourcePlannedTyping.Operations.erase, SourceDependencyAnnotations.Operations.erase,
    CoherentSourceTypes.Operations.ports, operations] at known
  split at known
  · simp_all [HandledRequest.clauses, ScopedTyping.clauseKeys]
  · cases known

theorem source : SourcePlannedSources.Expression operations policy contracts [] [] .none (fun _ => none)
    expression .unit [] requirements (signature (HandledRequest.plan effect 0)) :=
  .handler bodySource clausesTyped (.cons (.discard rfl) .nil) coverage (by decide) (List.Subset.refl [])
    (HandledRequest.table 0) (.cons (fun _ => rfl) .nil) declarations

theorem authenticated : Auth operations policy ports owners emptyRows source .unit rows := by
  apply Auth.handler (body := bodySource) (declarations := declarations)
    (clauses := clausesTyped) (capabilities := .cons (.discard rfl) .nil)
    (coverage := coverage) (unique := by decide) (admitted := List.Subset.refl [])
    (modes := .cons (fun _ => rfl) .nil)
  · exact Auth.perform (known := (rfl : operations effect 0 = some (.unit, .unit))) (admitted := List.mem_cons_self) (formed := List.nil_subset _)
      (operand := .unit) .unit
  · apply AuthDeclarations.cons (known := (rfl : operations effect 0 = some (.unit, .unit))) (supportBound := []) (ordinary := ordinary)
      (protectedMode := .unavailable) (rest := .nil)
    · apply AuthOffer.available (source := ordinaryBody)
        (resumeInterface := fun _ => rfl) (closeInterface := fun _ => rfl)
      intro owner contract fresh input answer resume close held demands
      exact AuthBody.typed (rows := ClauseRowAdmission.discard_rows)
        (closingRows := ClauseRowAdmission.protected_discard_rows)
        (Auth.discard (known := by simp [SourcePlannedTyping.Contracts.insert])
          (resolved := rfl) (permission := rfl) (unprotected := held)
          (admitted := by rw [close]; exact List.Subset.refl []))
    · exact .unavailable
    · exact .nil
    · exact List.Subset.refl []

def handler (activation : Nat) :=
  Context.handler (effect := effect) (table := HandledRequest.table 0) activation declarationRows Context.nil

theorem disposeCertificate (activation owner : Nat) (demand : List Nat) :
    SourceAdmission.Code [] (actions.insert owner ⟨false, true⟩) []
      (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available []) owner) [] [activation]
      (Rows.invoke (key := ⟨owner, .dispose⟩))
      (Context.live (owner := owner) (resumeDemand := demand) (handler activation) Context.nil) := by
  apply SourceAdmission.Code.dispose (front := Context.nil) (captured := handler activation)
    (tail := Context.nil) (rights := ⟨false, true⟩)
  · exact .hit
  · simp [Syntax.UsageTickets.insert]
  · rfl
  · simp [OwnerPhaseTransitions.introduce]
  · rfl
  · exact .handler .nil
  · exact .spent .nil

theorem budgetCertificate (activation : Nat) :
    RequestBudget [] (OwnerPhaseTransitions.available []) effect 0 (handler activation) := by
  intro _
  refine ⟨_, rfl, ?_, ?_⟩ <;>
    simp [CleanupHints.Metadata.check, CleanupHints.Metadata.closing,
      RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel,
      Context.pack, Context.context, OwnerSource.exportAt, ProtectionResiduals.residual_empty]

theorem requestCertificate (activation : Nat) :
    SourceAdmission.Code [] actions [] (OwnerPhaseTransitions.available []) [] [activation]
      (Rows.request (effect := effect) (operation := 0)) (handler activation) :=
  .request (bodyRows := fun owner => Rows.invoke (key := ⟨owner, .dispose⟩))
    (declarationRows := declarationRows) (rights := ⟨false, true⟩)
    (whole := handler activation) (captured := handler activation) (tail := Context.nil)
    (contract := ⟨true, some [], none⟩) (modes := (some HandledRequest.family, none))
    rfl (.handler rfl rfl rfl rfl) (fun _ => .handler .nil) (fun _ => .handler .nil)
    (budgetCertificate activation) (.selected .here .ordinary) .here rfl (.handler .nil)
    (fun owner demand _ _ => disposeCertificate activation owner demand)

theorem certificate : SourceAdmission.Code [] actions [] (OwnerPhaseTransitions.available []) [] [] rows Context.nil :=
  .handler (fun activation _ => .sequence .pure (requestCertificate activation))

theorem disposeResourceChecked (activation owner : Nat) (demand : List Nat) :
    CodeChecked [] [] (disposeCertificate activation owner demand) := by
  apply CodeChecked.dispose (front := Context.nil) (captured := handler activation) (tail := Context.nil)
    (rights := ⟨false, true⟩) (located := .hit) (known := by simp [Syntax.UsageTickets.insert])
    (permission := rfl) (available := by simp [OwnerPhaseTransitions.introduce]) (unprotected := rfl)
    (abandoned := .handler .nil) (waiting := .spent .nil)
  · exact .handler .nil
  · exact .spent .nil

theorem requestResourceChecked (activation : Nat) : CodeChecked [] [] (requestCertificate activation) := by
  apply CodeChecked.request (effect := effect) (operation := 0) (whole := handler activation) (captured := handler activation) (tail := Context.nil)
    (contract := ⟨true, some [], none⟩) (modes := (some HandledRequest.family, none))
    (cut := rfl) (guarded := .handler rfl rfl rfl rfl)
    (callbacks := fun _ => .handler .nil) (ownerBound := fun _ => .handler .nil)
    (cleanupBudget := budgetCertificate activation) (selected := .selected .here .ordinary)
    (terminal := .here) (requiredRights := rfl) (retained := .handler .nil)
    (body := fun owner demand _ _ => disposeCertificate activation owner demand)
  · intro _; exact .handler .nil
  · exact .handler .nil
  · intro owner demand _ _; exact disposeResourceChecked activation owner demand

theorem resourceChecked : CodeChecked [] [] certificate := by
  apply CodeChecked.handler
    (body := fun activation _ => .sequence .pure (requestCertificate activation))
  · exact List.Subset.refl []
  · intro activation _
    exact .sequence (first := .pure) (second := requestCertificate activation) .pure
      (requestResourceChecked activation)
def executionRoot : Requirements [] :=
  .sequence (.request [] []) (.sequence (.request [] []) (.request [] []))

theorem interpreted : Accounting.Run [] [] rows Context.nil executionRoot := by
  apply Accounting.Run.installHandler
  intro activation fresh
  apply Accounting.Run.sequence
  apply Accounting.Run.pure
  apply Accounting.Wait.plain
  apply Accounting.Run.request
    (captured := Context.handler (effect := effect) (table := HandledRequest.table 0)
      activation declarationRows Context.nil) (tail := Context.nil)
    (contract := ⟨true, some [], none⟩)
    (modes := (some HandledRequest.family, none))
    (bodyRows := fun owner => Rows.invoke (key := ⟨owner, .dispose⟩))
    (localRoot := fun owner _ => Requirements.sequence (.retire owner)
      (.sequence (.spent owner) (.request [] [])))
  · rfl
  · exact .selected .here .ordinary
  · intro owner demand absent
    apply Accounting.Run.dispose (front := Context.nil)
      (captured := Context.handler (effect := effect) (table := HandledRequest.table 0)
        activation declarationRows Context.nil) (tail := Context.nil)
    · exact .hit
    · exact .handler (.closing (.spent .nil))
  · intro owner demand absent
    exact .sequence .retireSelf (.sequence .spentSelf .empty)

theorem executionRoot_checked : RecursiveRequirements.Checked [] []
    (OwnerPhaseTransitions.available []) (annotateDisposals executionRoot) [] := by
  change RecursiveRequirements.Checked [] [] (OwnerPhaseTransitions.available [])
    (.sequence (.request [] []) (.sequence (.request [] []) (.request [] []))) ([] ++ ([] ++ []))
  exact .sequence (.request rfl) (.sequence (.request rfl) (.request rfl))

/-- The fixture packages source judgments, with no runtime-state premise. -/
def program : Program operations policy ports [] [] expression :=
  { result := .unit, resultRows := .unit,
    dependencies := HandledRequest.dependencies effect 0, plan := HandledRequest.plan effect 0,
    rows := rows, demand := [], requirements := requirements, source := source,
    authenticated := authenticated,
    certified := certified_from_existing SourcePlannedClauseRecipes.handled_request_certified,
    certificate := certificate, resourceChecked := resourceChecked,
    rootDemand := [], root := executionRoot, interpreted := interpreted,
    annotated := executionRoot, annotation := .original, rootRow := [],
    checked := executionRoot_checked, bounded := List.Subset.refl [],
    resources := List.Subset.refl [], builtinSignatures := builtinSignatures }

/-- A handled operation and its consuming clause inhabit closed initial admission. -/
theorem handled_discard_initial :
    InstallationState operations policy contracts tables families required [] annotations [] [] [] [] [] [] []
      ports owners emptyRows (.value .unit) (.value .unit) (initialRun expression) :=
  program.closed_initial_state tables families required

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample.ports
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample.ordinaryBody
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample.ordinary
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample.declarations
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample.bodySource
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample.clausesTyped
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample.coverage
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample.source
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample.authenticated
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample.disposeCertificate
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample.budgetCertificate
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample.requestCertificate
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample.certificate
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample.disposeResourceChecked
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample.requestResourceChecked
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample.resourceChecked
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample.interpreted
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample.executionRoot_checked
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample.program
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.HandledExample.handled_discard_initial
