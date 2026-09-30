import SourcePlannedCheckedAllocation

/-! Closing annotations retain the actual callback plans as data. Source typing
and scheduling refer to that same annotation; a check for another plan with the
same erased dependencies cannot substitute for it. These annotations refine the
existing close plan and do not add runtime instructions. -/
namespace Ash.OneShot.SourcePlannedClosingPlans
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceContextualHints (Hints)
open SourceContextualInvocationHints (forClosing)
open SourcePlannedTyping (Operations Contracts)
open SourcePlannedSources (ValueSummary)
open SourcePlannedChecks (Local Pending)
open RecursiveRequirements (Requirements)
open OwnerClosingSource (retirements)
abbrev Receiving := SourceDependencyCapture.Scope

inductive Plans : List CloseEntry → {scope : Receiving} → Hints scope → Type where
  | nil : Plans [] .nil
  | release : Plans tail hints → Plans (.release identity payload :: tail) (.cell (identity := identity) hints)
  | retire : Plans tail hints → Plans (.retire owner :: tail) (.running hints)
  | invoke (callback : Plan dependencies) : Plans tail hints →
      Plans (.invoke action :: tail) (.cleanup (needs := action.requests) (callback := dependencies) hints)

def Plans.append (first : Plans before firstHints) (second : Plans after secondHints) :
    Plans (before ++ after) (firstHints.append secondHints) :=
  match first with
  | .nil => second
  | .release rest => .release (rest.append second)
  | .retire rest => .retire (rest.append second)
  | .invoke callback rest => .invoke callback (rest.append second)

inductive Contents (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (world : List Nat) : {plan : List CloseEntry} → {scope : Receiving} → {hints : Hints scope} → Plans plan hints → Prop where
  | nil : Contents operations policy contracts world .nil
  | release : Contents operations policy contracts world rest → Contents operations policy contracts world (.release rest)
  | retire (known : contracts owner = some contract) (rest : Contents operations policy contracts world plans) :
      Contents operations policy contracts world (.retire (owner := owner) plans)
  | invoke {callbackPlan : Plan dependencies} {plans : Plans tail hints}
      (callback : ValueSummary operations policy contracts world (fun _ => none) [] action.action
        (.function .unit .unit action.requests latent (signature callbackPlan)))
      (rest : Contents operations policy contracts world plans) :
      Contents operations policy contracts world (.invoke (action := action) callbackPlan plans)

theorem Contents.append
    (first : Contents operations policy contracts world before)
    (second : Contents operations policy contracts world after) :
    Contents operations policy contracts world (before.append after) := by
  induction first with
  | nil => exact second
  | release rest ih => exact .release ih
  | retire known rest ih => exact .retire known ih
  | invoke callback rest ih => exact .invoke callback ih

/-- Extract annotations from the actual retained source, including callbacks
inside dormant captures. This extraction does not assert their closing checks. -/
theorem plan_contents {hints : Hints receiving} {outside : Hints outsideScope}
    (source : SourcePlannedCheckedFrames.Segment operations policy contracts tables families required actions outward phases world
      capture input output demand requirements records hints outside incoming outgoing)
    (built : makePlan capture = some plan) :
    ∃ plans : Plans plan (forClosing hints), Contents operations policy contracts world plans := by
  induction capture generalizing input output demand requirements records receiving hints outsideScope incoming outgoing plan with
  | nil => cases source; cases built; exact ⟨.nil, .nil⟩
  | push frame rest ih => cases source with
      | push head tail bound => cases head with
          | plain => obtain ⟨plans, contents⟩ := ih tail built; exact ⟨plans, contents⟩
          | handler => obtain ⟨plans, contents⟩ := ih tail built; exact ⟨plans, contents⟩
          | cell =>
              cases next : makePlan rest <;> simp [makePlan, next] at built
              case some suffix =>
                subst plan
                obtain ⟨plans, contents⟩ := ih tail next
                exact ⟨.release plans, .release contents⟩
          | armed scope callback annotation interface checked =>
              cases next : makePlan rest <;> simp [makePlan, next] at built
              case some suffix =>
                subst plan
                obtain ⟨plans, contents⟩ := ih tail next
                exact ⟨.invoke _ plans, .invoke callback contents⟩
          | running | closing | retiring => simp [makePlan] at built
  | live owner inputType answerType saved caller rest ihSaved ihRest => cases source with
      | live known actionKnown inputAnnotation answerAnnotation scopeKnown held captured savedBound tail resume close bound =>
          cases inside : makePlan saved <;> cases outsidePlan : makePlan rest <;> simp [makePlan, inside, outsidePlan] at built
          case some.some first second =>
            subst plan
            obtain ⟨savedPlans, savedContents⟩ := ihSaved captured inside
            obtain ⟨tailPlans, tailContents⟩ := ihRest tail outsidePlan
            exact ⟨savedPlans.append (.retire tailPlans), savedContents.append (.retire known tailContents)⟩
  | spent owner answer caller rest ih => cases source with
      | spent known annotation scopeKnown tail bound => obtain ⟨plans, contents⟩ := ih tail built; exact ⟨plans, contents⟩

/-- Scheduling checks exactly the plans retained by the annotation. The Local
checks are evaluated at the actual closing suffix and outside interpretations. -/
inductive Checked (outward : List Instance) (actions : Syntax.UsageTickets) (phases : OwnerPhaseTransitions.Phases)
    (world : List Nat) {outsideScope : Receiving} (outside : Hints outsideScope) :
    {plan : List CloseEntry} → {scope : Receiving} → {hints : Hints scope} → Plans plan hints → Prop where
  | nil : Checked outward actions phases world outside .nil
  | release : Checked outward actions phases world outside rest → Checked outward actions phases world outside (.release rest)
  | retire : Checked outward actions phases world outside rest → Checked outward actions phases world outside (.retire rest)
  | invoke {callback : Plan dependencies} {hints : Hints scope} {plans : Plans tail hints}
      (localCheck : Local outward actions phases world callback (.running (hints.append outside)))
      (rest : Checked outward actions phases world outside plans) :
      Checked outward actions phases world outside (.invoke (hints := hints) callback plans)

theorem Checked.erase {plans : Plans plan hints}
    (checked : Checked outward actions phases world outside plans) :
    Pending outward actions phases world hints outside := by
  induction checked with
  | nil => exact .nil
  | release rest ih => exact .cell ih
  | retire rest ih => exact .running ih
  | invoke callback rest ih => exact .cleanup callback ih

theorem Checked.transport
    (checked : Checked outward actions phases world outside plans)
    (extension : SourceDependencySchemes.PhaseExtension phases nextPhases)
    (permissions : Syntax.UsageExtension actions nextActions) :
    Checked outward nextActions nextPhases world outside plans := by
  induction checked with
  | nil => exact .nil
  | release rest ih => exact .release ih
  | retire rest ih => exact .retire ih
  | invoke callback rest ih => exact .invoke (SourcePlannedPhases.local_transport callback extension permissions) ih

inductive Template (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (world : List Nat) (caller : Execution.Scope) :
    {plan : List CloseEntry} → {scope : Receiving} → {hints : Hints scope} → Plans plan hints →
      Footprint → Requirements (retirements plan) → Prop where
  | nil : Template operations policy contracts tables world caller .nil [] (.request [] [])
  | release {plans : Plans tail hints} (rest : Template operations policy contracts tables world caller plans raw requirements) :
      Template operations policy contracts tables world caller (.release (identity := identity) (payload := payload) plans) raw
        (.sequence ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables (closeControl caller tail))) requirements)
  | retire (known : contracts owner = some contract)
      (rest : Template operations policy contracts tables world caller plans raw requirements) :
      Template operations policy contracts tables world caller (.retire (owner := owner) plans) raw (.sequence (.retire owner) requirements)
  | invoke {callbackPlan : Plan dependencies} {plans : Plans tail hints}
      (callback : ValueSummary operations policy contracts world (fun _ => none) [] action.action
        (.function .unit .unit action.requests latent (signature callbackPlan)))
      (rest : Template operations policy contracts tables world caller plans raw requirements) :
      Template operations policy contracts tables world caller (.invoke (action := action) callbackPlan plans)
        (DisposalProtection.callbackResidual tail latent ++ raw)
        (.sequence ((Requirements.request [] (qualify true latent)).prepend (OwnerPhases.ofStack tables (closeControl caller tail))) requirements)

theorem Contents.template {plans : Plans plan hints} (contents : Contents operations policy contracts world plans) :
    ∃ raw, ∃ requirements : Requirements (retirements plan), Template operations policy contracts tables world caller plans raw requirements := by
  induction contents with
  | nil => exact ⟨[], _, .nil⟩
  | release rest ih => obtain ⟨raw, requirements, template⟩ := ih; exact ⟨raw, _, .release template⟩
  | retire known rest ih => obtain ⟨raw, requirements, template⟩ := ih; exact ⟨raw, _, .retire known template⟩
  | invoke callback rest ih => obtain ⟨raw, requirements, template⟩ := ih; exact ⟨_, _, .invoke callback template⟩

theorem Template.erase {hints : Hints receiving} {plans : Plans plan hints}
    (template : Template operations policy contracts tables world caller plans raw requirements) :
    SourceDependencySchemes.Closing.Template operations.erase policy contracts.erase tables world caller plan raw requirements receiving := by
  induction template with
  | nil => exact .nil
  | release rest ih => exact .release ih
  | retire known rest ih => exact .retire (SourcePlannedSources.contract_erase_known known) ih
  | invoke callback rest ih => exact .invoke (SourcePlannedSources.expression_erase callback) ih

/-- Materialize the same stored requirement body and callback plans. The check
and source premises share Plans, so every armed frame uses the source's plan. -/
theorem Template.source {plans : Plans plan hints}
    (template : Template operations policy contracts tables world caller plans raw requirements)
    (checked : Checked outward actions phases world outside plans)
    (typed : ScopedPorts.PlanTyped operations.erase.erase.ports world closing plan)
    (scope : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports caller) :
    SourcePlannedCheckedFrames.Segment operations policy contracts tables families required actions outward phases world
      (closeControl caller plan) .unit .unit (retirements plan) requirements [] hints outside
      (ScopedPorts.planProvides plan ++ closing) closing := by
  have scopeTypes := ScopedPorts.effect_scope_known_has_types scope
  induction template with
  | nil => exact .nil (List.Subset.refl _)
  | release rest ih => cases typed with | release typed => cases checked with | release next =>
      exact .push (.cell scopeTypes (by simp [ScopedPorts.eraseType, ScopedPorts.Port.resources]) rfl
        (.cell scope (by simp [ScopedPorts.eraseType, ScopedPorts.Port.resources]))) (ih next typed) (List.Subset.refl _)
  | retire known rest ih => cases typed with | retire typed => cases checked with | retire next =>
      exact .push (.retiring known (.retiring (CoherentSourceTypes.Owners.ports_lookup
        (SourceDependencyAnnotations.contract_erase_known (SourcePlannedSources.contract_erase_known known))))) (ih next typed) (List.Subset.refl _)
  | @invoke dependencies tail receiving hints latent raw requirements action callbackPlan plans callback rest ih =>
    cases typed with | invoke callable effects typed => cases checked with | invoke localCheck next =>
      exact .push (.armed (action := { action with scope := caller, answer := .unit }) scopeTypes callback rfl (.armed scope callable effects) localCheck) (ih next typed) (List.Subset.refl _)

end Ash.OneShot.SourcePlannedClosingPlans

#print axioms Ash.OneShot.SourcePlannedClosingPlans.Contents.append
#print axioms Ash.OneShot.SourcePlannedClosingPlans.plan_contents
#print axioms Ash.OneShot.SourcePlannedClosingPlans.Checked.erase
#print axioms Ash.OneShot.SourcePlannedClosingPlans.Checked.transport
#print axioms Ash.OneShot.SourcePlannedClosingPlans.Contents.template
#print axioms Ash.OneShot.SourcePlannedClosingPlans.Template.erase
#print axioms Ash.OneShot.SourcePlannedClosingPlans.Template.source
