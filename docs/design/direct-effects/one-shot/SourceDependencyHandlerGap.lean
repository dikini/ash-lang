import SourceDependencySchemes

/-! Test whether uniform declaration schemes can admit clauses which use an
outer interpretation. This compares source and contextual judgments; it is not
a reachable-run counterexample or a change to the admitted calculus. -/
namespace Ash.OneShot.SourceDependencyHandlerGap
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations
open SourceDependencyChecks (Local Pending)
open SourceDependencySchemes (ClauseFamily CaptureSource Checked Retained)
open SourceDependencyCapture

def effect : Instance := .user 92 []
def rights : Syntax.OneShotRights := ⟨true, false⟩
def actions : Syntax.UsageTickets := fun _ => some rights
def phases : OwnerPhaseTransitions.Phases := fun _ => .available
def family (owner : Nat) : Dependencies :=
  .sequence (.sequence .pure (.request effect 0)) (.sequence .pure (.invoke ⟨owner, .resume⟩))
def outside : SourceDependencyCapture.Scope := Examples.handlerF .nil

/-- Even an empty captured continuation and empty receiving stack satisfy
the current abstract resume-only continuation interface. -/
theorem empty_capture_source (outward : List Instance) :
    CaptureSource outward actions phases [] 19 rights .nil .nil :=
  ⟨fun _ => .nil, .nil, by intro impossible; cases impossible⟩

/-- The same interface also admits an outer handler. No future execution is
assumed in either case. -/
theorem outer_capture_source (outward : List Instance) :
    CaptureSource outward actions phases [] 19 rights .nil outside :=
  ⟨fun _ => .nil, .handler .nil, by intro impossible; cases impossible⟩

/-- The dependency tree passes the existing structural local checker when
the required outer handler is present. Resume reuses the established scheme. -/
theorem checked_with_outer : Checked [] actions phases [] (family 19) (.live 19 .nil outside) := by
  apply Local.sequence
  · apply Local.sequence .pure
    apply Local.request_selected (found := rfl)
    · decide
    · intro impossible; cases impossible
    · intro impossible; cases impossible
  · exact (SourceDependencySchemes.resume_family (rights := rights) rfl).silent_prefix .pure |>.instantiate
      (actions := actions) (phases := phases) rfl rfl (outer_capture_source [])

/-- Uniform checking loses the distinction between an available outer
interpretation and its absence. Merely enlarging the outward effect list does
not supply an installed handler to the local request checker. -/
theorem no_uniform_scheme (outward : List Instance) : ¬ ClauseFamily outward rights family := by
  intro scheme
  have checked := scheme.instantiate rfl rfl (empty_capture_source outward)
  have request := (Local.sequence_iff.mp (Local.sequence_iff.mp checked).1).2
  have guarded := Local.request_guard request
  change false = true at guarded
  cases guarded

def operations : Operations := fun actual operation =>
  if actual = effect ∧ operation = 0 then some (.unit, .unit) else none
def policy : Syntax.TicketPolicy := fun _ => rights
def code : Code := .bind 7 (.perform (Instantiation.freezeEffect effect) 0 .unit) (.resume 9 .unit)
def requirements (owner : Nat) (contract : Contract) :
    RecursiveRequirements.Requirements (owner :: contract.resumeDemand) :=
  .sequence (.emitAfter (.request [] []) [] [⟨effect, 0, false⟩])
    (.sequence (.request [] []) (.invoke ⟨owner, .resume⟩ contract.resumeDemand []))

/-- This is the actual rich source expression producing that dependency
tree, for any matching resume interface. It is not just an arbitrary annotation.
The declaration is constructed below; reachable-run admission remains separate. -/
theorem source_expression (known : contracts owner = some contract)
    (input : contract.input = .unit) (answer : contract.answer = .unit)
    (allowed : contract.resumeEffects ⊆ [effect]) :
    Expression operations policy contracts [] [effect] (.ticket 9 owner)
      environment code .unit (owner :: contract.resumeDemand) (requirements owner contract) (family owner) := by
  have performed := Expression.perform (operations := operations) (policy := policy)
    (contracts := contracts) (world := []) (allowed := [effect]) (scope := .ticket 9 owner) (environment := environment)
    (show operations effect 0 = some (.unit, .unit) by simp [operations]) List.mem_cons_self
    Expression.unit (by simp [ScopedPorts.InWorld, Value.erase, CoherentSourceTypes.Value.port, ScopedPorts.Port.resources])
  have resumed := Expression.resume (operations := operations) (policy := policy)
    (world := []) (scope := .ticket 9 owner) (binder := 9) (environment := environment.extend 7 .unit)
    known rfl rfl (input.symm ▸ Expression.unit) allowed
    (by simp [answer, ScopedPorts.InWorld, Value.erase, CoherentSourceTypes.Value.port, ScopedPorts.Port.resources])
  exact Expression.bind performed (answer ▸ resumed)

/-- The established row interface retains the operation advertisement and
its actual outer interpretation. Reuse its resume check and open/close theorem. -/
theorem clause_rows (held : contract.held = false) :
    ClauseRowAdmission.Rows ⟨owner, contract.erase, false, [⟨effect, 0, false⟩]⟩ (requirements owner contract) (ClauseRowAdmission.SourceStore operations.erase owner contract.erase) := by
  intro store tail before requestRow interface exported
  have pureCheck : RecursiveRequirements.Checked store (.live owner contract.held :: tail) before
      (.request [] []) [] := .request (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])
  have operationCheck : OwnerSource.exportAt (.live owner contract.held :: tail) before
      [⟨effect, 0, false⟩] = some requestRow := by
    simp only [OwnerSource.exportAt, OwnerPhaseTransitions.project, held]
    split <;> exact exported
  have first : RecursiveRequirements.Checked store (.live owner contract.held :: tail) before
      (.emitAfter (.request [] []) [] [⟨effect, 0, false⟩]) ([] ++ requestRow) :=
    .emitAfter pureCheck operationCheck
  have last : RecursiveRequirements.Checked store (.live owner contract.held :: tail) before
      (.sequence (.request [] []) (.invoke ⟨owner, .resume⟩ contract.resumeDemand [])) ([] ++ contract.resumeRow) :=
    .sequence pureCheck interface.resume
  have checked := RecursiveRequirements.Checked.sequence first last
  obtain ⟨calls, derived, supplied⟩ := ContextualClauseChecks.open_checked checked
  exact ⟨_, calls, derived, supplied, List.Subset.refl _⟩

/-- The ordinary clause offer itself is admitted by the hereditary rich
source judgment, including its independently checked row bound. -/
theorem ordinary_offer :
    Offer operations policy contracts [] environment [effect] 1 9 .unit .unit .unit [effect] []
      code false false (some [⟨effect, 0, false⟩]) (some family) := by
  apply Offer.available (fun _ => rfl) (by intro impossible; cases impossible)
  intro owner contract fresh input answer resumeEffects closeEffects held balance
  exact .typed (source_expression (by simp [Contracts.insert]) input answer
    (resumeEffects.symm ▸ List.Subset.refl _)) (clause_rows held)

/-- Source offer admission does not imply the additional uniform mode
certificate currently required on an installed handler. -/
theorem no_uniform_mode (outward : List Instance) :
    ¬ SourceDependencySchemes.ModeScheme outward code.requiredActions (some family) := by
  intro mode
  cases mode with | available scheme => exact no_uniform_scheme outward scheme

def clauses : Clauses := .cons 0 1 9 code .nil
def table : List (Nat × ClauseContract) := [(0, ⟨false, some [⟨effect, 0, false⟩], none⟩)]
def dependencies : ClauseDependencies := [(0, some family, none)]

/-- A handler for F may delegate an F operation to an outer interpretation
before resuming. This is an admitted declaration, not just a standalone body. -/
theorem source_declarations :
    Declarations operations policy contracts [] environment [effect] effect .unit clauses table dependencies :=
  .cons (by simp [operations]) ordinary_offer .unavailable .nil

theorem no_uniform_declarations (outward : List Instance) :
    ¬ SourceDependencySchemes.DeclarationSchemes outward clauses dependencies := by
  intro schemes
  exact no_uniform_scheme outward (schemes.selected ClauseAt.hit (held := false) rfl)

end Ash.OneShot.SourceDependencyHandlerGap

#print axioms Ash.OneShot.SourceDependencyHandlerGap.empty_capture_source
#print axioms Ash.OneShot.SourceDependencyHandlerGap.outer_capture_source
#print axioms Ash.OneShot.SourceDependencyHandlerGap.checked_with_outer
#print axioms Ash.OneShot.SourceDependencyHandlerGap.no_uniform_scheme
#print axioms Ash.OneShot.SourceDependencyHandlerGap.source_expression
#print axioms Ash.OneShot.SourceDependencyHandlerGap.clause_rows
#print axioms Ash.OneShot.SourceDependencyHandlerGap.ordinary_offer
#print axioms Ash.OneShot.SourceDependencyHandlerGap.no_uniform_mode
#print axioms Ash.OneShot.SourceDependencyHandlerGap.source_declarations
#print axioms Ash.OneShot.SourceDependencyHandlerGap.no_uniform_declarations
