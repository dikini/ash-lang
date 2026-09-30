import ScopedPolicies

/-!
Provenance of clause action profiles through actual scoped execution. Profiles
include current code, retained frames and recursively saved captures. Execution
may copy or drop entries but cannot invent a new key/requirement pair. This is
action-contract provenance, not capture safety or Core identity authentication.
-/

namespace Ash.OneShot.ScopedProfiles
open Syntax (OneShotRights TicketPolicy)
open ScopedExpressions ScopedExecution ActionRequirements ActionPolicies

def clausesProfile (clauses : Clauses) : Profile := clauseEntries clauses.usageShape
def contextProfile (context : Context) : Profile := (context.plug .unit).actionProfile

def frameProfile : ExecFrame → Profile
  | .plain data => contextProfile data.context
  | .handler data => clausesProfile data.clauses
  | .cell _ _ _ _ | .closing _ _ | .retiring _ => []
  | .armed action | .unwinding action => action.action.actionProfile
  | .running action saved _ => action.action.actionProfile ++ saved.actionProfile

def stackProfile : Stack → Profile
  | .nil => []
  | .push frame rest => frameProfile frame ++ stackProfile rest
  | .live _ _ _ saved _ rest => stackProfile saved ++ stackProfile rest
  | .spent _ _ _ rest => stackProfile rest

def profile (configuration : Configuration) : Profile :=
  configuration.expression.actionProfile ++ stackProfile configuration.stack

theorem context_profile_membership (context : Context) (code : Code) (entry : Nat × OneShotRights) :
    entry ∈ (context.plug code).actionProfile ↔ entry ∈ code.actionProfile ∨ entry ∈ contextProfile context := by
  cases context <;>
    simp only [Context.plug, Code.actionProfile, Code.usageShape, entries, contextProfile, List.mem_append, List.not_mem_nil] <;>
    grind only

theorem stack_append_profile (left right : Stack) :
    stackProfile (left.append right) = stackProfile left ++ stackProfile right := by
  induction left <;> simp_all [Stack.append, stackProfile, List.append_assoc]

theorem selected_clause_profile (selected : ClauseAt operation clauses parameter binder body) :
    (binder, body.requiredActions) ∈ clausesProfile clauses ∧ body.actionProfile ⊆ clausesProfile clauses := by
  induction selected with
  | hit =>
    constructor
    · exact List.mem_cons_self
    · intro entry member
      exact List.mem_cons_of_mem _ (List.mem_append_left _ member)
  | pass different next ih =>
    constructor
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ ih.1)
    · intro entry member
      exact List.mem_cons_of_mem _ (List.mem_append_right _ (ih.2 member))

theorem handler_cut_profile (cut : HandlerCut requested whole cap tail handler) :
    clausesProfile handler.clauses ⊆ stackProfile whole := by
  induction cut with
  | hit => exact List.subset_append_left _ _
  | push _ _ _ _ _ _ _ ih => exact ih.trans (List.subset_append_right _ _)
  | live _ _ _ _ _ _ _ _ _ _ ih => exact ih.trans (List.subset_append_right _ _)
  | spent _ _ _ _ _ _ _ _ ih => exact ih

theorem cell_update_profile (selected : CellUpdate identity old new before after) :
    stackProfile after = stackProfile before := by
  induction selected <;> simp_all [stackProfile, frameProfile]

def planProfile : List CloseEntry → Profile
  | [] => []
  | .invoke action :: rest => action.action.actionProfile ++ planProfile rest
  | _ :: rest => planProfile rest

theorem plan_append_profile (left right : List CloseEntry) :
    planProfile (left ++ right) = planProfile left ++ planProfile right := by
  induction left with
  | nil => rfl
  | cons entry rest ih => cases entry <;> simp_all [planProfile, List.append_assoc]

theorem close_control_profile (plan : List CloseEntry) (scope : Scope) :
    stackProfile (closeControl scope plan) = planProfile plan := by
  induction plan with
  | nil => rfl
  | cons entry rest ih => cases entry <;> simp_all [closeControl, CloseEntry.frame, stackProfile, frameProfile, planProfile]

theorem make_plan_profile (stack : Stack) (built : makePlan stack = some plan) :
    planProfile plan ⊆ stackProfile stack := by
  induction stack generalizing plan with
  | nil => cases built; exact List.Subset.refl _
  | push frame rest ih =>
    cases frame <;> cases known : makePlan rest <;> simp only [makePlan, known] at built
    all_goals first | cases built | skip
    all_goals simp only [stackProfile, frameProfile, planProfile]
    all_goals first
      | exact (ih known).trans (List.subset_append_right _ _)
      | exact ih known
      | exact append_subset (List.Subset.refl _) (ih known)
  | live ticket q a saved scope rest ihSaved ihRest =>
    cases inside : makePlan saved <;> cases outside : makePlan rest <;>
      simp only [makePlan, inside, outside] at built
    all_goals first | cases built | skip
    simp only [plan_append_profile, planProfile, stackProfile]
    exact append_subset (ihSaved inside) (ihRest outside)
  | spent _ _ _ _ ih => exact ih built

/-- No current, retained or saved code gains a new clause contract pair. Raw
    execution suffices; typing, usage, access and freshness are not premises. -/
theorem raw_step_profile (step : RawStep before after created discharged) : profile after ⊆ profile before := by
  cases step with
  | focus plain selected tail =>
    rw [← focus_reconstructs selected]
    simp only [profile, stackProfile, frameProfile, List.subset_def, List.mem_append, context_profile_membership]
    grind only
  | plug plain value closed scope tail =>
    simp only [profile, stackProfile, frameProfile, List.subset_def, List.mem_append, context_profile_membership]
    grind only
  | bind parameter value suffix scope tail closed ready =>
    have bound := Code.substitution_action_profile_bound suffix parameter closed.1
    simp only [profile, Code.actionProfile, Code.usageShape, entries, List.subset_def, List.mem_append] at bound ⊢
    grind only
  | beta parameter body value scope tail closed ready =>
    have bound := Code.substitution_action_profile_bound body parameter closed.1
    simp only [profile, Code.actionProfile, Code.usageShape, entries, List.subset_def, List.mem_append] at bound ⊢
    grind only
  | ifTrue | ifFalse | enterHandler | leaveHandler | leaveCell | enterCleanup | startCleanup | finishCleanup
  | leaveClause | finishClose | retire =>
    simp only [profile, stackProfile, frameProfile, clausesProfile, Code.actionProfile, Code.usageShape, entries,
      List.subset_def, List.mem_append, List.not_mem_nil]
    grind only
  | enterCell binder identity payload body scope answer tail ready =>
    simp only [profile, stackProfile, frameProfile, Code.actionProfile,
      Code.instantiation_usage_shape, Code.usageShape, entries, List.nil_append]
    exact List.Subset.refl _
  | capture requested operation parameter binder ticket operand body scope whole cap tail handler output cut clause closed ready =>
    have bodyBound := (selected_clause_profile clause).2.trans (handler_cut_profile cut)
    have substituted := Code.substitution_action_profile_bound body parameter closed.1
    have decomposition : stackProfile whole = stackProfile cap ++ stackProfile tail := by
      rw [handler_cut_reconstructs cut, stack_append_profile]
    simp only [profile, stackProfile, Code.actionProfile, Code.usageShape, entries,
      List.subset_def, List.mem_append, decomposition] at bodyBound substituted ⊢
    grind only
  | resume =>
    simp only [profile, stack_append_profile, stackProfile, Code.actionProfile, Code.usageShape, entries,
      List.subset_def, List.mem_append]
    grind only
  | discard binder ticket closeId scope callerScope q a front cap tail plan resolve built =>
    have bound := make_plan_profile cap built
    simp only [profile, stack_append_profile, stackProfile, frameProfile, close_control_profile,
      Code.actionProfile, Code.usageShape, entries, List.subset_def, List.mem_append, List.not_mem_nil] at bound ⊢
    grind only
  | readCell _ _ _ _ _ selected | writeCell _ _ _ _ _ _ selected =>
    simp only [profile, Code.actionProfile, Code.usageShape, entries, List.nil_append, cell_update_profile selected]
    exact List.Subset.refl _

theorem raw_trace_profile (steps : RawTrace before after created discharged) : profile after ⊆ profile before := by
  induction steps with
  | refl => exact List.Subset.refl _
  | next first rest ih => exact ih.trans (raw_step_profile first)

theorem run_step_profile (step : RunStep before after) : profile after.configuration ⊆ profile before.configuration := by
  cases step with
  | event _ _ _ raw _ => exact raw_step_profile raw

theorem run_steps_profile (steps : RunSteps before after) : profile after.configuration ⊆ profile before.configuration := by
  induction steps with
  | refl => exact List.Subset.refl _
  | next first rest ih => exact ih.trans (run_step_profile first)

theorem named_step_profile (step : NamedStep before after) :
    profile after.execution.configuration ⊆ profile before.execution.configuration :=
  run_step_profile (named_step_executes step)

theorem named_steps_profile (steps : NamedSteps before after) :
    profile after.execution.configuration ⊆ profile before.execution.configuration :=
  run_steps_profile (named_steps_execute steps)

theorem named_access_steps_profile (steps : NamedAccessSteps ambient before after) :
    profile after.execution.configuration ⊆ profile before.execution.configuration :=
  named_steps_profile (named_access_steps_have_names steps)

/-- The source policy is fixed; historical or temporarily absent clauses do not
    lose their entries when execution moves to a smaller current expression. -/
theorem source_profile_provenance
    (steps : NamedAccessSteps ambient
      ⟨⟨⟨source, .none, .nil⟩, [], []⟩, []⟩ after) :
    profile after.execution.configuration ⊆ source.actionProfile := by
  simpa only [profile, stackProfile, List.append_nil] using named_access_steps_profile steps

theorem source_profile_coverage
    (steps : NamedAccessSteps ambient
      ⟨⟨⟨source, .none, .nil⟩, [], []⟩, []⟩ after) :
    Covers source.inferredPolicy (profile after.execution.configuration) :=
  fun entry member => inferred_covers source.actionProfile entry (source_profile_provenance steps member)

theorem source_profile_coherence
    (coherent : Coherent source.actionProfile)
    (steps : NamedAccessSteps ambient
      ⟨⟨⟨source, .none, .nil⟩, [], []⟩, []⟩ after) :
    Coherent (profile after.execution.configuration) :=
  coherent_subset coherent (source_profile_provenance steps)

theorem source_contract_exact
    (coherent : Coherent source.actionProfile)
    (steps : NamedAccessSteps ambient
      ⟨⟨⟨source, .none, .nil⟩, [], []⟩, []⟩ after)
    (member : (binder, rights) ∈ profile after.execution.configuration) :
    source.inferredPolicy binder = rights :=
  inferred_exact coherent (source_profile_provenance steps member)

theorem selected_contract_exact
    (coherent : Coherent source.actionProfile)
    (steps : NamedAccessSteps ambient
      ⟨⟨⟨source, .none, .nil⟩, [], []⟩, []⟩ before)
    (cut : HandlerCut requested before.execution.configuration.stack cap tail handler)
    (selected : ClauseAt operation handler.clauses parameter binder body) :
    source.inferredPolicy binder = body.requiredActions :=
  source_contract_exact coherent steps
    (List.mem_append_right _ (handler_cut_profile cut (selected_clause_profile selected).1))

theorem raw_ticket_contract_exact
    {source : Code}
    (coherent : Coherent source.actionProfile)
    (origin : profile before ⊆ source.actionProfile)
    (raw : RawStep before after [.ticket owner] discharged) :
    ∃ binder, after.scope = .ticket binder owner ∧ source.inferredPolicy binder = after.expression.requiredActions := by
  cases raw with
  | capture requested operation parameter binder ticket operand body scope whole cap tail handler output cut clause closed ready =>
    refine ⟨binder, rfl, ?_⟩
    rw [Code.substitution_required_actions body parameter closed.1]
    exact inferred_exact coherent
      (origin (List.mem_append_right _ (handler_cut_profile cut (selected_clause_profile clause).1)))

theorem named_ticket_contract_exact
    (coherent : Coherent source.actionProfile)
    (steps : NamedAccessSteps ambient
      ⟨⟨⟨source, .none, .nil⟩, [], []⟩, []⟩ before)
    (step : NamedStep before after)
    (allocated : after.execution.issued = before.execution.issued ++ [.ticket owner]) :
    ∃ binder, after.execution.configuration.scope = .ticket binder owner ∧
      source.inferredPolicy binder = after.execution.configuration.expression.requiredActions := by
  cases step with
  | event after created discharged raw fresh names =>
    have same : created = [.ticket owner] := List.append_cancel_left allocated
    subst created
    exact raw_ticket_contract_exact coherent (source_profile_provenance steps) raw

/-- Type-directed capture now connects its actual registry permission to the
    source-derived local requirement. Only capture-specific closing safety is
    left in the conditional certificate, not arbitrary excess action grants. -/
theorem source_capture_constructs_ready_obligation
    (coherent : Coherent source.actionProfile)
    (steps : NamedAccessSteps ambient
      ⟨⟨⟨source, .none, .nil⟩, [], []⟩, []⟩
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩, activations⟩)
    (cut : HandlerCut requested whole cap tail handler)
    (ready : ScopedPrepared.Ready signature source.inferredPolicy registry ambient
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩, activations⟩ result outgoing)
    (isValue : operand.IsValue) (fresh : (issued ++ [Owner.ticket owner]).Nodup)
    (checks : AccessChecks ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩ ambient) :
    ∃ (parameter binder : Nat) (body : Code) (output : Ty) (residual : List Instance),
      let record : Joint.TicketRecord := ⟨⟨output, handler.answer, residual, residual⟩, source.inferredPolicy binder⟩
      let initial : NamedState :=
        ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body.subst parameter operand, .ticket binder owner,
        .live owner output handler.answer cap handler.scope tail⟩
      NamedAccessStep ambient initial (ScopedJoint.advanceState initial after [.ticket owner] []) ∧
      ScopedJoint.Valid signature source.inferredPolicy (registry.insert owner record) ambient
        (ScopedJoint.advanceState initial after [.ticket owner] []) result outgoing ∧
      record.permissions = body.requiredActions ∧
      ((body.requiredActions.dispose = true → ScopedTyping.CloseReady signature
          (ScopedTyping.resourceWorld issued) residual cap) →
        ScopedPrepared.Ready signature source.inferredPolicy (registry.insert owner record) ambient
          (ScopedJoint.advanceState initial after [.ticket owner] []) result outgoing) := by
  obtain ⟨parameter, binder, body, output, residual, step, valid, obligation⟩ :=
    ScopedPrepared.capture_constructs_ready_obligation cut ready isValue fresh checks
  obtain ⟨actualBinder, sameScope, exactContract⟩ :=
    named_ticket_contract_exact coherent steps step.execution rfl
  have sameBinder : binder = actualBinder := (Execution.Scope.ticket.inj sameScope).1
  subst actualBinder
  have exactRights : source.inferredPolicy binder = body.requiredActions := by
    simpa only [ScopedJoint.advanceState, Code.substitution_required_actions body parameter isValue] using exactContract
  refine ⟨parameter, binder, body, output, residual, step, valid, exactRights, ?_⟩
  intro safe
  apply obligation
  rw [exactRights]
  exact safe

namespace Examples
open ScopedExpressions.PolicyExamples

def duplicateBefore : Configuration :=
  ⟨.app (.lambda 5 (.pair (.variable 5) (.variable 5))) repeatedFunction, .none, .nil⟩
def duplicateAfter : Configuration := ⟨copiedFunctions, .none, .nil⟩

theorem repeated_function_closed : ClosedValue repeatedFunction := by
  refine ⟨trivial, rfl, ?_⟩
  intro dependency member
  cases member

theorem duplicate_beta : RawStep duplicateBefore duplicateAfter [] [] :=
  .beta 5 (.pair (.variable 5) (.variable 5)) repeatedFunction .none .nil repeated_function_closed
    ⟨trivial, rfl, by intro dependency member; cases member⟩

theorem duplicate_profiles :
    profile duplicateBefore = [(9, resumeOnly), (11, disposeOnly)] ∧
    profile duplicateAfter = [(9, resumeOnly), (11, disposeOnly), (9, resumeOnly), (11, disposeOnly)] := ⟨rfl, rfl⟩

theorem duplication_preserves_provenance : profile duplicateAfter ⊆ profile duplicateBefore :=
  raw_step_profile duplicate_beta

def callbackAction : ActionData := ⟨7, repeatedFunction, repeated_function_closed, .none, .unit, []⟩
def cleanupCapture : Stack := .push (.armed callbackAction) .nil

theorem cleanup_plan_retains_clause_profiles :
    makePlan cleanupCapture = some [.invoke callbackAction] ∧
      stackProfile (closeControl .none [.invoke callbackAction]) = [(9, resumeOnly), (11, disposeOnly)] := ⟨rfl, rfl⟩

def branchingSource : Code := .branch (.boolean true) .unit distinctSource

theorem branch_drops_current_profile :
    RawStep ⟨branchingSource, .none, .nil⟩ ⟨.unit, .none, .nil⟩ [] [] ∧
      branchingSource.inferredPolicy 9 = resumeOnly ∧
      (Code.unit).inferredPolicy 9 = ActionRequirements.none := ⟨.ifTrue .unit distinctSource .none .nil, rfl, rfl⟩

theorem running_contract_record :
    ∃ next after record,
      next 3 = some record ∧ record.permissions.dispose = false ∧
      NamedAccessStep [] ScopedPrepared.Examples.before after ∧
      ScopedPrepared.Ready ScopedPrepared.Examples.signature runningSource.inferredPolicy next [] after .unit [] := by
  have coherent : Coherent runningSource.actionProfile := distinct_keys_coherent (by decide)
  obtain ⟨parameter, binder, body, output, residual, step, _, exactRights, obligation⟩ :=
    source_capture_constructs_ready_obligation coherent ScopedPrepared.Examples.source_reaches_running_request
      ScopedPrepared.Examples.actual_cut running_before_ready trivial (owner := 3) (by decide)
      ScopedPrepared.Examples.before_access_checks
  refine ⟨_, _, (⟨⟨output, ScopedPrepared.Examples.handler.answer, residual, residual⟩,
    runningSource.inferredPolicy binder⟩ : Joint.TicketRecord), ?_,
    running_policy_forbids_dispose binder, step, obligation ?_⟩
  · simp [Joint.Registry.insert]
  · intro forbidden
    change runningSource.inferredPolicy binder = body.requiredActions at exactRights
    rw [← exactRights, running_policy_forbids_dispose] at forbidden
    cases forbidden

end Examples

end Ash.OneShot.ScopedProfiles

#print axioms Ash.OneShot.ScopedProfiles.context_profile_membership
#print axioms Ash.OneShot.ScopedProfiles.stack_append_profile
#print axioms Ash.OneShot.ScopedProfiles.selected_clause_profile
#print axioms Ash.OneShot.ScopedProfiles.handler_cut_profile
#print axioms Ash.OneShot.ScopedProfiles.cell_update_profile
#print axioms Ash.OneShot.ScopedProfiles.plan_append_profile
#print axioms Ash.OneShot.ScopedProfiles.close_control_profile
#print axioms Ash.OneShot.ScopedProfiles.make_plan_profile
#print axioms Ash.OneShot.ScopedProfiles.raw_step_profile
#print axioms Ash.OneShot.ScopedProfiles.raw_trace_profile
#print axioms Ash.OneShot.ScopedProfiles.run_step_profile
#print axioms Ash.OneShot.ScopedProfiles.run_steps_profile
#print axioms Ash.OneShot.ScopedProfiles.named_step_profile
#print axioms Ash.OneShot.ScopedProfiles.named_steps_profile
#print axioms Ash.OneShot.ScopedProfiles.named_access_steps_profile
#print axioms Ash.OneShot.ScopedProfiles.source_profile_provenance
#print axioms Ash.OneShot.ScopedProfiles.source_profile_coverage
#print axioms Ash.OneShot.ScopedProfiles.source_profile_coherence
#print axioms Ash.OneShot.ScopedProfiles.source_contract_exact
#print axioms Ash.OneShot.ScopedProfiles.selected_contract_exact
#print axioms Ash.OneShot.ScopedProfiles.raw_ticket_contract_exact
#print axioms Ash.OneShot.ScopedProfiles.named_ticket_contract_exact
#print axioms Ash.OneShot.ScopedProfiles.source_capture_constructs_ready_obligation
#print axioms Ash.OneShot.ScopedProfiles.Examples.repeated_function_closed
#print axioms Ash.OneShot.ScopedProfiles.Examples.duplicate_beta
#print axioms Ash.OneShot.ScopedProfiles.Examples.duplicate_profiles
#print axioms Ash.OneShot.ScopedProfiles.Examples.duplication_preserves_provenance
#print axioms Ash.OneShot.ScopedProfiles.Examples.cleanup_plan_retains_clause_profiles
#print axioms Ash.OneShot.ScopedProfiles.Examples.branch_drops_current_profile
#print axioms Ash.OneShot.ScopedProfiles.Examples.running_contract_record
