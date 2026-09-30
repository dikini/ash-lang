import SourceConsumingUseCapture
import SourceConsumingLeafInterfacesExamples

/-! Rich captured code is rechecked at consumption beneath a temporary mask.
Its second operation resumes a distinct outside owner and is not an operation
footprint. Source rechecking retains that owner's actual cut and rights. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.UseAdmissionExamples
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceConsumingClauseAnnotations (Body Generated)
open SourceScheduledCapabilityAnnotations (Code Retained recipeLaws)
open SourceScheduledSourceRechecking (ReceiverChange)
open SourceDependencyCapture.Examples (effectE resumeTable resumeDependencies)
open LeafAdmissionExamples (masked maskedBody admitted)

def actions : Syntax.UsageTickets := fun owner =>
  if owner = 19 then some ⟨true, true⟩ else if owner = 37 then some ⟨true, false⟩ else none
def phases := OwnerPhaseTransitions.available [19, 37]
def waiting := Forest.live (owner := 37) .nil HandlerExamples.waiting

def savedPlan := Plan.sequence (.request (effect := effectE) (operation := 0)) (.invoke (key := ⟨37, .resume⟩))
def saved := Forest.plain savedPlan .nil
def whole := Forest.live (owner := 19) saved waiting

def savedCode : Code [] savedPlan (.spent (owner := 19) waiting) :=
  .sequence (.operations [(effectE, 0)] .request .request)
    (.resume (.spent .hit) (.operations .nil) (.operations (.spent .nil)) (.handler (.operations .nil)))

def context : Context [] 19 [] actions phases whole .nil saved waiting where
  cut := .hit
  before := .nil
  resumption := fun _ => ⟨.plain savedCode (.operations .nil),
    ⟨⟨rfl, ⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩⟩⟩, rfl⟩⟩
  closing := fun _ => ⟨.operations .nil, rfl⟩
  disposal := fun _ => ⟨rfl, rfl⟩
  after := .live (.operations .nil) (.handler (.operations .nil))
  tailReady := ⟨rfl, ⟨rfl, rfl⟩⟩

/-- The saved source cannot take the operation-interface route. -/
theorem rich_source (permission) :
    SourceScheduledSourceRechecking.OperationSource.extract (context.resumption permission).val = none := rfl

/-- Only the final caller is used: inner supplying E, outer empty E, consumed
owner19, then the still-available outside owner37 and its waiting handler. -/
theorem at_use : AtUse [] actions phases context maskedBody .nil := by
  apply AtUse.handler
  apply AtUse.handler
  apply AtUse.resume
  intro _permission
  apply ReceiverChange.plain
  · apply SourceScheduledSourceRechecking.Expression.sequence
    · exact .operations rfl
    · exact SourceScheduledSourceRechecking.Expression.resume_from_bound
        (.spent .hit) (.handler (.handler (.spent .hit)))
        (.spent .nil) (.handler _ (.handler _ (.spent .nil)))
        (.handler (.operations .nil)) .operations
        (by obtain ⟨⟨_, ready⟩, _⟩ := (context.resumption (by rfl)).property; exact ready)
        (List.Subset.refl []) rfl rfl
  · exact .empty

theorem generated : ∃ annotation : Code [] masked whole,
    annotation.Valid [] actions phases ∧ Generated actions context.continuationBounds maskedBody annotation :=
  at_use.initial_source (recipeLaws []) (fun evidence => evidence) admitted rfl rfl rfl

/-- The outside owner cannot already be spent when the saved code is resumed. -/
theorem outside_consumed_rejected : ¬ savedCode.Valid [] actions
    (OwnerPhaseTransitions.spend (OwnerPhaseTransitions.spend phases 19) 37) := by
  intro ready
  have available := ready.2.2.1
  change OwnerPhaseTransitions.spend (OwnerPhaseTransitions.spend phases 19) 37 37 = .available at available
  simp [OwnerPhaseTransitions.spend] at available

/-- The source carries non-absent current-code metadata, so replacing the
saved annotation by a compact operation view would lose this correspondence. -/
theorem rich_bounds_not_absent : context.continuationBounds.resumption rfl ≠
    SourceBoundSnapshots.Retained.absent saved := by
  intro equal
  cases equal

/-- Reuse the previously admitted resource body; only its richer captured
source needs a new structural leaf derivation. -/
theorem resource_at_use : AtUse [] actions phases context LeafAdmissionExamples.RichWaiting.resourceBody .nil := by
  apply AtUse.resource
  intro identity _fresh
  apply AtUse.sequence
  apply AtUse.handler
  apply AtUse.handler
  apply AtUse.resume
  intro _permission
  apply ReceiverChange.plain
  · apply SourceScheduledSourceRechecking.Expression.sequence
    · exact .operations rfl
    · exact SourceScheduledSourceRechecking.Expression.resume_from_bound
        (.spent .hit) (.handler (.handler (.cell (.spent .hit))))
        (.spent .nil) (.handler _ (.handler _ (.cell (.spent .nil))))
        (.handler (.operations .nil)) .operations
        (by
          obtain ⟨⟨_, ready⟩, _⟩ :=
            ((context.world_weaken (List.nil_subset [identity])).resumption (by rfl)).property
          exact ready)
        (List.Subset.refl []) rfl rfl
  · exact .empty

theorem resource_generated : ∃ annotation : Code [] LeafAdmissionExamples.RichWaiting.resourcePlan whole,
    annotation.Valid [] actions phases ∧ Generated actions context.continuationBounds
      LeafAdmissionExamples.RichWaiting.resourceBody annotation :=
  resource_at_use.initial_source (recipeLaws []) (fun evidence => evidence)
    LeafAdmissionExamples.RichWaiting.resource_admitted rfl rfl rfl

/-- The same leaf judgment admits the existing fresh-disposer example,
reusing its structural rechecking proof rather than an operation interface. -/
theorem disposing_at_use : AtUse [] HandlerExamples.actions HandlerExamples.phases
    HandlerExamples.context HandlerExamples.body .nil :=
  .handler (.choice (.resume HandlerExamples.saved_rechecking) (.dispose HandlerExamples.closing_rechecking))

theorem disposing_generated : ∃ annotation : Code [] HandlerExamples.clause HandlerExamples.whole,
    annotation.Valid [] HandlerExamples.actions HandlerExamples.phases ∧
    Generated HandlerExamples.actions HandlerExamples.context.continuationBounds HandlerExamples.body annotation :=
  disposing_at_use.generate_source (recipeLaws []) (fun evidence => evidence) .hit .nil HandlerExamples.checked

namespace Closing

def callback := Plan.invoke (key := ⟨37, .resume⟩)
def saved := Forest.cleanup (needs := []) callback .nil
def whole := Forest.live (owner := 19) saved waiting

def normalCallback : Code [] callback (.running (.spent (owner := 19) waiting)) :=
  .resume (.running (.spent .hit)) (.operations .nil)
    (.operations (.running (.spent .nil))) (.handler (.operations .nil))
def closingCallback : Code [] callback (.running (.running (.spent (owner := 19) waiting))) :=
  .resume (.running (.running (.spent .hit))) (.operations .nil)
    (.operations (.running (.running (.spent .nil)))) (.handler (.operations .nil))

def context : Context [] 19 [] actions phases whole .nil saved waiting where
  cut := .hit
  before := .nil
  resumption := fun _ => ⟨.cleanup normalCallback (.operations .nil),
    ⟨⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩⟩, rfl⟩⟩
  closing := fun _ => ⟨.cleanup closingCallback (.operations .nil),
    ⟨⟨rfl, rfl, rfl, rfl, ⟨rfl, rfl⟩⟩, rfl⟩⟩
  disposal := fun _ => ⟨rfl, rfl⟩
  after := .live (.operations .nil) (.handler (.operations .nil))
  tailReady := ⟨rfl, ⟨rfl, rfl⟩⟩

def clause := Plan.handler (effect := effectE) (table := []) [] .nil
  (Plan.handler (effect := effectE) (table := resumeTable) [] SourceScheduledInvocationInterfaceExamples.declarations
    (.invoke (key := ⟨19, .dispose⟩)))
def body : Body [] 19 clause := .handler .nil .nil
  (.handler HandlerInterfaceExamples.bounds SourceScheduledInvocationInterfaceExamples.declaration_recipes .dispose)

theorem admitted : SourceConsumingClauseAnnotations.Admitted ⟨true, true⟩ [] [] body [] :=
  .handler (.handler (.dispose rfl) rfl rfl) rfl rfl

theorem closing_rich (permission) :
    SourceScheduledSourceRechecking.OperationSource.extract (context.closing permission).val = none := rfl

theorem at_use : AtUse [] actions phases context body .nil := by
  apply AtUse.handler
  apply AtUse.handler
  apply AtUse.dispose
  intro _permission
  apply ReceiverChange.cleanup
  · exact SourceScheduledSourceRechecking.Expression.resume_from_bound
      (.running (.running (.spent .hit))) (.running (.running (.handler (.handler (.spent .hit)))))
      (.running (.running (.spent .nil)))
      (.running (.running (.handler _ (.handler _ (.spent .nil)))))
      (.handler (.operations .nil)) .operations
      (by obtain ⟨ready, _⟩ := (context.closing (by rfl)).property; exact ready)
      (List.Subset.refl []) rfl rfl
  · exact .empty

theorem generated : ∃ annotation : Code [] clause whole,
    annotation.Valid [] actions phases ∧ Generated actions context.continuationBounds body annotation :=
  at_use.initial_source (recipeLaws []) (fun evidence => evidence) admitted rfl rfl rfl

end Closing

end Ash.OneShot.SourceConsumingCleanupAdmission.UseAdmissionExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAdmissionExamples.rich_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAdmissionExamples.at_use
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAdmissionExamples.generated
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAdmissionExamples.outside_consumed_rejected

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAdmissionExamples.disposing_at_use
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAdmissionExamples.disposing_generated
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAdmissionExamples.Closing.admitted
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAdmissionExamples.Closing.closing_rich
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAdmissionExamples.Closing.at_use
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAdmissionExamples.Closing.generated

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAdmissionExamples.rich_bounds_not_absent
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAdmissionExamples.resource_at_use
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseAdmissionExamples.resource_generated

namespace Ash.OneShot.SourceConsumingCleanupAdmission.UseCaptureExamples
open SourceScheduledCapabilityAnnotations (recipeLaws)
open SourceConsumingClauseAnnotations (SelectedSource)
open CaptureExamples

/-- Actual request instantiation needs no operation view and no eager At. -/
theorem at_use : AtUse [] (actions.insert 19 raw.requiredActions) (OwnerPhaseTransitions.introduce phases 19)
    context (body 19) .nil :=
  .handler (.resume (fun permission => recheck_saved (context.resumption permission).val))

theorem allocator_certificate : ∃ certificate : SourceScheduledCaptureAnnotations.Capture [] 19 outer 0 offered
    (some family, some family) plans 1 9 raw saved, certificate.Valid [] actions phases := by
  obtain ⟨annotation, ready, _⟩ := SelectedSource.capture_at_use
    (recipeLaws []) (fun evidence => evidence) snapshot snapshot_admitted bounded cut selected
    selected_source source captureSource permits rfl fresh absent at_use rfl
  exact ⟨.site cut selected annotation, ready⟩

end Ash.OneShot.SourceConsumingCleanupAdmission.UseCaptureExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseCaptureExamples.at_use
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseCaptureExamples.allocator_certificate

namespace Ash.OneShot.SourceConsumingCleanupAdmission.MissingCaptureContract
open SourceConsumingClauseAnnotations (Body Admitted)
open SourceDeclarationPlans (Plan)
open SourceScheduledCapabilityAnnotations (recipeLaws)
open SourceDependencyCapture.Examples (effectE)

/-- The clause's declared interface omits the E request in the actual saved
source. Local clause admission alone cannot authenticate that interface. -/
def plan := Plan.handler (effect := effectE) (table := []) [] .nil
  (.invoke (key := ⟨19, .resume⟩))
def body : Body [] 19 plan := .handler .nil .nil .resume

theorem empty_interface_admitted : Admitted ⟨true, true⟩ [] [] body [] :=
  .handler (.resume rfl) rfl rfl

/-- The original captured source is valid, but the clause masks the provider
it needs. Reuse the existing compiler to refute every structural AtUse proof. -/
theorem no_at_use : ¬ AtUse [] HandlerExamples.actions HandlerExamples.phases
    HandlerExamples.context body .nil := by
  intro checked
  cases checked with
  | handler inner =>
    cases inner with
    | resume restored =>
      obtain ⟨source, ready, _⟩ := (restored (by rfl)).compile_retaining
        (recipeLaws []) (fun evidence => evidence) (HandlerExamples.context.resumption (by rfl)).property
      have scheduled := source.compile_with (recipeLaws []) ready
      cases scheduled with
      | plain code tail =>
        cases code with
        | request guarded closing =>
          have impossible := SourceDependencySchemes.checked_request guarded
          change false = true at impossible
          cases impossible

/-- Authenticating the actual saved requirement repairs this example using
the existing clause checker; it must reject the masking clause. -/
theorem honest_interface_rejected : ¬ Admitted ⟨true, true⟩ [(effectE, 0)] [] body [] := by
  intro admitted
  have checked := admitted.at_capture (actions := HandlerExamples.actions)
    (phases := HandlerExamples.phases) (captured := SourceDependencyCapture.Scope.nil)
    (waiting := SourceDependencyCapture.Scope.nil) rfl rfl rfl
  have impossible := checked.2.2.2.1
  change false = true at impossible
  cases impossible

/-- This local counterexample is not a source-typed handler when E has the
operation used by the saved code. Full source typing independently requires
coverage, so the local example cannot refute a theorem using that premise. -/
theorem empty_handler_not_source_typed
    {operations : SourcePlannedTyping.Operations}
    (known : operations effectE 0 = some (input, output)) :
    ¬ SourcePlannedSources.Expression operations policy contracts world allowed scope environment
      (.handle (Instantiation.freezeEffect effectE) code .nil) answer demand requirements checking := by
  intro source
  generalize frozen : Instantiation.freezeEffect effectE = actual at source
  cases source with
  | handler inner clauses capabilities coverage unique admitted table modes declarations =>
      cases ScopedExecution.freeze_effect_injective frozen
      have covered := coverage 0 _ _ (CoherentSourceTypes.port_lookup
        (SourceDependencyAnnotations.operation_erase (SourcePlannedSources.operation_erase known)))
      exact List.not_mem_nil covered

end Ash.OneShot.SourceConsumingCleanupAdmission.MissingCaptureContract

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.MissingCaptureContract.empty_interface_admitted
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.MissingCaptureContract.no_at_use
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.MissingCaptureContract.honest_interface_rejected

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.MissingCaptureContract.empty_handler_not_source_typed

namespace Ash.OneShot.ClauseRowAdmission.UncheckedTemplate
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements

def effect : Instance := .user 990 []
def contract : CoherentSourceTypes.Owners.Contract :=
  ⟨.unit, .unit, false, [], [], [], none, [effect], []⟩
def outer : OwnerPhases.Context := [.ordinary (.handler effect 0 [(1, ⟨false, some [], some []⟩)])]
def inner (table : List (Nat × ClauseContract)) : OwnerPhases.Context := [.ordinary (.handler effect 0 table)]
def store : Store := [(⟨19, .resume⟩, ⟨[], .request [] [⟨effect, 1, false⟩]⟩)]
def phases := OwnerPhaseTransitions.available [19]
def required (table : List (Nat × ClauseContract)) : Requirements [19] :=
  (Requirements.sequence (.request [] []) (.invoke ⟨19, .resume⟩ [] [])).prepend (inner table)

/-- The row interface accepts a stored request without consulting any source
operation signature. The caller below supplies that request. -/
theorem original_interface : Interface 19 contract false store outer phases [] := by
  apply Interface.of_resume (denied := rfl) (fresh := by decide)
  exact .invoke rfl (by decide) .hit (.request (by decide))

/-- An arbitrary stored template can require an operation omitted by the
inserted table. This refutes the universal row premise, even when that omitted
operation is outside the real source signature. -/
theorem nested_rows_rejected (missing : ProtectionContracts.lookup 1 table = none) :
    ¬ Rows ⟨19, contract, false, []⟩ (required table) := by
  intro rows
  obtain ⟨row, checked, bound⟩ := rows.instantiate original_interface (by rfl)
  have impossible := checked_complete checked
  have failed : evaluate store (.live 19 contract.held :: outer) phases (required table) = none := by
    simp only [required, Requirements.prepend, evaluate_sequence]
    rw [evaluate_invoke (show lookup ⟨19, .resume⟩ store = some ⟨[], Requirements.request [] [⟨effect, 1, false⟩]⟩ from rfl)]
    simp only [evaluate, evaluateFuel]
    simp [inner, contract, outer, phases, PhaseRechecking.checkOwners,
      OwnerPhaseTransitions.spendAll, OwnerPhaseTransitions.available, OwnerPhases.consume,
      OwnerSource.exportAt, OwnerPhaseTransitions.project, OwnerPhaseTransitions.spend,
      ProtectionResiduals.residualize, ProtectionResiduals.throughLayer,
      ProtectionResiduals.demandThrough, ProtectionResiduals.merge, missing]
  rw [failed] at impossible
  cases impossible

def plannedContract : SourcePlannedTyping.Contract :=
  ⟨.unit, .unit, false, [], [], [], none, [effect], []⟩

def nestedPlan := SourceDeclarationPlans.Plan.handler
  (effect := effect) (table := SourceDependencyCapture.Examples.resumeTable) []
  SourceScheduledClauseHandlers.Examples.innerPlans
  (SourceDeclarationPlans.Plan.sequence .pure (.invoke (key := ⟨19, .resume⟩)))

/-- Full expression typing still cannot supply the former unrestricted row
contract. This is not a rejection by the new source-relative Body rule. -/
theorem nested_unrestricted_body_rejected
    (known : contracts 19 = some plannedContract) :
    ¬ ∃ demand, ∃ requirements : RecursiveRequirements.Requirements demand,
      SourcePlannedSources.Expression operations policy contracts world allowed (.ticket 7 19) environment
        (.handle (Instantiation.freezeEffect effect) (.resume 7 .unit)
          SourceScheduledClauseHandlers.Examples.innerClauses) .unit demand requirements checking ∧
      Rows ⟨19, contract, false, []⟩ requirements := by
  rintro ⟨demand, requirements, source, rows⟩
  generalize answerEq : SourcePlannedTyping.Value.unit = answer at source
  generalize frozen : Instantiation.freezeEffect effect = requested at source
  cases source with
  | handler body clauses capabilities coverage unique admitted table modes declarations =>
    cases ScopedExecution.freeze_effect_injective frozen
    cases body with
    | resume found resolved permission operand admitted formed =>
      have ownerSame : _ = 19 := Option.some.inj resolved.symm
      subst_vars
      have contractSame := Option.some.inj (found.symm.trans known)
      cases contractSame
      cases operand
      have missing : ProtectionContracts.lookup 1 table = none := by
        cases modes with
        | cons dispose rest => cases rest; rfl
      exact nested_rows_rejected missing rows

def operations : SourcePlannedTyping.Operations := fun actual operation =>
  if actual = effect ∧ operation = 0 then some (.unit, .unit) else none

def policy : Syntax.TicketPolicy := fun _ => ⟨true, false⟩
def contracts : SourcePlannedTyping.Contracts := fun owner =>
  if owner = 19 then some plannedContract else none

private theorem resume_offer (held : Bool) :
    SourcePlannedSources.Offer operations policy contracts [] (fun _ => none) [effect]
      2 3 .unit .unit .unit [effect] [] (.resume 3 .unit) held false (some [])
      (.available SourceScheduledClauseHandlers.Examples.resumeBodies) := by
  apply SourcePlannedSources.Offer.available (fun _ => rfl) (by intro impossible; cases impossible)
  intro owner offered fresh inputSame answerSame resumeSame closeSame heldSame balance
  have known : (contracts.insert owner offered) owner = some offered := by
    simp [SourcePlannedTyping.Contracts.insert]
  have operand : SourcePlannedSources.Expression operations policy (contracts.insert owner offered)
      [] [effect] (.ticket 3 owner) (SourcePlannedTyping.Environment.extend (fun _ => none) 2 .unit)
      .unit offered.input [] (.request [] []) .pure := inputSame.symm ▸ .unit
  have resumed := SourcePlannedSources.Expression.resume (binder := 3) known rfl rfl operand
    (resumeSame.symm ▸ List.Subset.refl [effect])
    (answerSame.symm ▸ (by simp [ScopedPorts.InWorld, SourcePlannedTyping.Value.erase,
      SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port, ScopedPorts.Port.resources]))
  exact .typed (answerSame ▸ resumed) ClauseRowAdmission.resume_rows ClauseRowAdmission.protected_resume_rows

/-- Every expression-typing premise holds: operation coverage, ports, one-shot
use and both hereditary offers. The unrestricted outer row premise is additional. -/
theorem expression_typed :
    SourcePlannedSources.Expression operations policy contracts [] [effect] (.ticket 7 19) (fun _ => none)
      (.handle (Instantiation.freezeEffect effect) (.resume 7 .unit)
        SourceScheduledClauseHandlers.Examples.innerClauses) .unit [19]
      (required SourceDependencyCapture.Examples.resumeTable) (SourcePlanSignatures.signature nestedPlan) := by
  have known : operations effect 0 = some (.unit, .unit) := by simp [operations]
  have ports := CoherentSourceTypes.port_lookup
    (SourceDependencyAnnotations.operation_erase (SourcePlannedSources.operation_erase known))
  have covered : ScopedPorts.Covers operations.erase.erase.ports effect
      SourceScheduledClauseHandlers.Examples.innerClauses := by
    intro operation input output found
    by_cases same : operation = 0
    · simp [same, SourceScheduledClauseHandlers.Examples.innerClauses, ScopedTyping.clauseKeys]
    · simp [CoherentSourceTypes.Operations.ports, SourceDependencyAnnotations.Operations.erase,
        SourcePlannedTyping.Operations.erase, operations, same] at found
  exact .handler
    (.resume (show contracts 19 = some plannedContract from rfl) rfl rfl .unit
      (by simp [plannedContract]) (by simp [plannedContract, ScopedPorts.InWorld,
        SourcePlannedTyping.Value.erase, SourceDependencyAnnotations.Value.erase,
        CoherentSourceTypes.Value.port, ScopedPorts.Port.resources]))
    (.cons ports (.resume .unit (List.Subset.refl _) (by simp [plannedContract, ScopedPorts.InWorld,
      SourcePlannedTyping.Value.erase, SourceDependencyAnnotations.Value.erase,
      CoherentSourceTypes.Value.port, ScopedPorts.Port.resources])) .nil)
    (.cons (.resume rfl .unit) .nil) covered (by decide) (List.Subset.refl _)
    SourceDependencyCapture.Examples.resumeTable (.cons (by intro impossible; cases impossible) .nil)
    (.cons known (resume_offer false) (resume_offer true) .nil)

/-- The template that refutes the row premise is outside this exact source
signature. It is not a reachable well-typed continuation counterexample. -/
theorem template_operation_not_declared : operations effect 1 = none := by decide

end Ash.OneShot.ClauseRowAdmission.UncheckedTemplate

#print axioms Ash.OneShot.ClauseRowAdmission.UncheckedTemplate.original_interface
#print axioms Ash.OneShot.ClauseRowAdmission.UncheckedTemplate.nested_rows_rejected
#print axioms Ash.OneShot.ClauseRowAdmission.UncheckedTemplate.nested_unrestricted_body_rejected
#print axioms Ash.OneShot.ClauseRowAdmission.UncheckedTemplate.expression_typed
#print axioms Ash.OneShot.ClauseRowAdmission.UncheckedTemplate.template_operation_not_declared

namespace Ash.OneShot.ClauseRowAdmission.AuthenticatedTemplate
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open RecursiveRequirements

/-- This contract names the exact stored template and a structural summary
before caller interpretation. It contains no successful target-body premise. -/
def source (owner : Nat) (effect : Instance) (store : Store) : Prop :=
  ∃ (body : Requirements []) (raw : Footprint),
    lookup ⟨owner, .resume⟩ store = some ⟨[], body⟩ ∧
    RecursiveOutward.Outward body (some raw) ∧
    raw ⊆ [⟨effect, 0, false⟩, ⟨effect, 0, true⟩]

def table : List (Nat × ClauseContract) := [(0, ⟨false, some [], some []⟩)]
def caller (effect : Instance) : OwnerPhases.Context := [.ordinary (.handler effect 0 table)]
def code (owner : Nat) (effect : Instance) : Requirements [owner] :=
  (Requirements.sequence (.request [] []) (.invoke ⟨owner, .resume⟩ [] [])).prepend (caller effect)

/-- Reuse the finite interpreter check and outward-summary theorem at every
actual store satisfying the source contract. Further owner calls are excluded
by Outward, not silently accepted by this example. -/
theorem rows (empty : contract.resumeDemand = []) :
    Rows ⟨owner, contract, false, advertised⟩ (code owner effect) (source owner effect) := by
  intro authenticated tail before requestRow interface exported
  obtain ⟨body, raw, known, summary, bounded⟩ := authenticated.property
  obtain ⟨oldBody, waiting, original, available, selected, checked⟩ := checked_invocation interface.resume
  rw [empty] at available
  have interpreted : throughLayer (.handler effect 0 table) raw = some [] := by
    obtain ⟨row, found, covered⟩ := UniformClauseBounds.layer_coverage bounded
      (show throughLayer (.handler effect 0 table) [⟨effect, 0, false⟩, ⟨effect, 0, true⟩] = some [] from by
        simp [throughLayer, demandThrough, table, ProtectionContracts.lookup, ClauseContract.row, modeCheck, merge])
    have noRequests : row = [] := List.eq_nil_iff_forall_not_mem.mpr (by intro request member; exact List.not_mem_nil (covered member))
    exact noRequests ▸ found
  have next : Checked authenticated ((caller effect) ++ .live owner contract.held :: tail)
      (OwnerPhaseTransitions.spend before owner) body [] := by
    apply evaluate_sound
    rw [RecursiveOutward.evaluation summary]
    simp [caller, OwnerPhaseTransitions.project, interpreted, residualize, residual_empty]
  have invoked : Checked authenticated (.live owner contract.held :: tail) before
      (.invoke ⟨owner, .resume⟩ [] (caller effect)) [] :=
    .invoke known available (.ordinary .hit) next
  have whole : Checked authenticated (.live owner contract.held :: tail) before (code owner effect) [] := by
    change Checked authenticated (.live owner contract.held :: tail) before
      (.sequence (.request (caller effect) []) (.invoke ⟨owner, .resume⟩ [] (caller effect))) []
    exact Checked.sequence (firstRow := []) (.request (by simp [OwnerSource.exportAt, residual_empty])) invoked
  obtain ⟨calls, derived, supplied⟩ := ContextualClauseChecks.open_checked whole
  exact ⟨[], calls, derived, supplied, List.nil_subset _⟩

open UncheckedTemplate (contract effect phases)

def goodStore : Store := [(⟨19, .resume⟩, ⟨[], .request [] [⟨effect, 0, false⟩]⟩)]
def tail : OwnerPhases.Context := [.ordinary (.handler effect 0 table)]

theorem good_source : source 19 effect goodStore :=
  ⟨.request [] [⟨effect, 0, false⟩], _, rfl, .request (layers := []), by simp⟩

theorem good_interface : Interface 19 contract false goodStore tail phases [] := by
  apply Interface.of_resume (denied := rfl) (fresh := by decide)
  exact .invoke rfl (by decide) .hit (.request (by decide))

theorem admitted_instance : ∃ row,
    Checked goodStore (.live 19 contract.held :: tail) phases (code 19 effect) row ∧ row ⊆ [] :=
  (rows (contract := contract) (advertised := []) rfl).instantiate good_interface rfl good_source

theorem unknown_template_rejected : ¬ source 19 effect UncheckedTemplate.store := by
  rintro ⟨body, raw, known, summary, bounded⟩
  have same : body = Requirements.request [] [⟨effect, 1, false⟩] := by
    have pair := Option.some.inj known
    cases pair
    rfl
  cases same
  have equal := RecursiveOutward.unique summary (RecursiveOutward.Outward.request (layers := []))
  cases Option.some.inj equal
  have impossible := bounded (by simp : (⟨effect, 1, false⟩ : Demand) ∈ [⟨effect, 1, false⟩])
  simp at impossible

end Ash.OneShot.ClauseRowAdmission.AuthenticatedTemplate

#print axioms Ash.OneShot.ClauseRowAdmission.AuthenticatedTemplate.rows
#print axioms Ash.OneShot.ClauseRowAdmission.AuthenticatedTemplate.good_source
#print axioms Ash.OneShot.ClauseRowAdmission.AuthenticatedTemplate.good_interface
#print axioms Ash.OneShot.ClauseRowAdmission.AuthenticatedTemplate.admitted_instance
#print axioms Ash.OneShot.ClauseRowAdmission.AuthenticatedTemplate.unknown_template_rejected

/- The clause-row interface must exclude an active alias of its newly allocated
owner. Otherwise an impossible tail changes interpretation when that owner is
consumed and rejects an effectful cleanup that is valid at a fresh boundary. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.CleanupTailFreshness
open ClauseRowAdmission
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals CoherentSourceTypes
open RecursiveRequirements

def f : Instance := .user 910 []
def g : Instance := .user 911 []
def contract : Owners.Contract := ⟨.unit, .unit, false, [], [], [], none, [f], []⟩
def contracts : Owners.Contracts := fun owner => if owner = 19 then some contract else none
def whole : Stack := .live 19 .unit .unit .nil .none .nil
def resumes : Store := [(⟨19, .resume⟩, ⟨[], .request [] []⟩)]
def disposals : Store := [(⟨19, .dispose⟩, ⟨[], .request [] []⟩)]
def store : Store := resumes ++ disposals

theorem authenticated : SourceStore operations 19 contract store := by
  apply SourceStore.of_source (contracts := contracts) (stack := whole)
    (policy := fun _ => ⟨true, false⟩) (tables := fun _ => []) (world := [])
    (input := .unit) (output := .unit) (demand := [])
    (requirements := .sequence (.spent 19) (.request [] []))
  · unfold whole resumes
    exact .live (contract := contract) rfl rfl rfl ⟨.none, .none⟩ rfl .nil .nil
  · unfold whole disposals
    exact .close (capture := .nil) (plan := []) rfl (OpenOwnerUses.internal_of_subset (List.nil_subset [])) .nil .nil .nil
  · rfl

def tail : OwnerPhases.Context := [
  .ordinary (.handler f 0 [(0, ⟨false, some [⟨g, 0, false⟩], some [⟨g, 0, false⟩]⟩)]),
  .live 19 true,
  .ordinary (.handler g 1 [(0, ⟨false, none, some []⟩)])]
def phases := OwnerPhaseTransitions.available [19]
def advertised : Footprint := [⟨f, 0, true⟩]
def requirements : Requirements [19] :=
  .emitAfter (.sequence (.request [] [])
    (.sequence (.request [] []) (.invoke ⟨19, .resume⟩ [] []))) [] advertised

/-- The former resume check accepts this store and phase environment even
though the tail repeats the newly allocated owner. -/
theorem phantom_resume : RecursiveRequirements.Checked store (.live 19 contract.held :: tail) phases
    (.invoke ⟨19, .resume⟩ [] []) [] :=
  .invoke rfl (by decide) .hit (.request (by decide))

/-- Ownership freshness excludes this context independently of its row. -/
theorem phantom_interface_rejected : ¬ Interface 19 contract false store tail phases [] := by
  intro supplied
  exact supplied.fresh (by decide)

theorem exported : OwnerSource.exportAt tail phases advertised = some [] := by decide
theorem failed : evaluate store (.live 19 contract.held :: tail) phases requirements = none := by
  simp [evaluate, evaluateFuel, store, resumes, disposals, requirements, RecursiveRequirements.lookup, contract, tail, phases, advertised, f, g, PhaseRechecking.checkOwners, OwnerPhaseTransitions.available, OwnerPhaseTransitions.spendAll, OwnerPhaseTransitions.spend, OwnerPhases.consume, OwnerSource.exportAt, OwnerPhaseTransitions.project, residualize, throughLayer, demandThrough, merge, ClauseContract.row, modeCheck, ProtectionContracts.lookup]

def operations : Operations := fun effect operation =>
  if effect = f ∧ operation = 0 then some (.unit, .unit) else none
def policy : Syntax.TicketPolicy := fun _ => ⟨true, false⟩
def callback : Code := .lambda 0 (.perform (Instantiation.freezeEffect f) 0 .unit)
def clause : Code := .cleanup callback (.resume 8 .unit)
def goodTail : OwnerPhases.Context := [.ordinary (.handler f 2 [(0, ⟨false, some [], some []⟩)])]

theorem clause_source : DeclaredSources.Expression operations policy contracts [] [f] (.ticket 8 19)
    Environment.empty clause .unit [19] requirements := by
  have known : contracts 19 = some contract := rfl
  have action : DeclaredSources.Expression operations policy contracts [] [f] (.ticket 8 19)
      Environment.empty callback (.function .unit .unit [f] [⟨f, 0, false⟩]) [] (.request [] []) :=
    .lambda (.perform (by decide) List.mem_cons_self (.stable .unit)
      (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]))
      (.emitAfter (layers := []) (.request (layers := [])))
      (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources, f, Instance.resources])
  exact .cleanup action (.resume (binder := 8) known rfl rfl (.stable .unit)
    (List.Subset.refl [f]) (by simp [contract, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]))
    (by simp)

theorem good_export : OwnerSource.exportAt goodTail phases advertised = some [] := by decide
theorem good_evaluation : evaluate store (.live 19 contract.held :: goodTail) phases requirements = some [] := by
  simp [evaluate, evaluateFuel, store, resumes, disposals, requirements, RecursiveRequirements.lookup, contract, goodTail, phases, advertised, f, PhaseRechecking.checkOwners, OwnerPhaseTransitions.available, OwnerPhaseTransitions.spendAll, OwnerPhaseTransitions.spend, OwnerPhases.consume, OwnerSource.exportAt, OwnerPhaseTransitions.project, residualize, throughLayer, demandThrough, merge, ClauseContract.row, modeCheck, ProtectionContracts.lookup]

/-- The same literal clause now has a source-relative certificate for all
fresh abstract interfaces, not just the concrete successful example. -/
theorem admitted_clause : ClauseRowAdmission.Body operations policy contracts [] [f]
    Environment.empty 8 19 contract false advertised clause .unit :=
  .typed clause_source (ClauseRowAdmission.cleanup_resume_rows rfl)

theorem good_interface : Interface 19 contract false store goodTail phases [] := by
  apply Interface.of_resume (denied := rfl) (fresh := by decide)
  exact .invoke rfl (by decide) .hit (.request (by decide))

end Ash.OneShot.SourceConsumingCleanupAdmission.CleanupTailFreshness

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CleanupTailFreshness.authenticated

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CleanupTailFreshness.phantom_resume

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CleanupTailFreshness.phantom_interface_rejected

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CleanupTailFreshness.exported

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CleanupTailFreshness.failed

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CleanupTailFreshness.clause_source

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CleanupTailFreshness.good_export

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CleanupTailFreshness.good_evaluation

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CleanupTailFreshness.admitted_clause

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.CleanupTailFreshness.good_interface
