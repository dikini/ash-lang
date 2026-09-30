import SourceAnnotatedClosingRuntime
import SourceAnnotatedRuntimeTyping

/-! Closing source is extracted from the original annotated saved segment.
The same callback type, latent footprint and declaration plan are retained in
the template. Erasure supplies existing closing proofs at those exact indices. -/
namespace Ash.OneShot.SourceAnnotatedClosingPlans
open ScopedExpressions ProtectionContracts
open SourceAnnotatedRuntime (CloseEntry makePlan closeControl)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceContextualHints (Hints)
open SourceContextualInvocationHints (forClosing)
open SourcePlannedTyping (Operations Contracts)
open SourceAnnotatedSources (ValueSummary)
open SourceAnnotatedRuntimeTyping (Segment)
open SourceRetainedPlans (Forest closingForest)
open RecursiveRequirements (Requirements)
open OwnerClosingSource (retirements)
abbrev Receiving := SourceDependencyCapture.Scope

inductive Plans : List CloseEntry → {scope : Receiving} → Hints scope → Type where
  | nil : Plans [] .nil
  | release : Plans tail hints → Plans (.release identity payload :: tail) (.cell (identity := identity) hints)
  | retire : Plans tail hints → Plans (.retire owner :: tail) (.running hints)
  | invoke (callback : Plan dependencies) : Plans tail hints →
      Plans (.invoke action :: tail) (.cleanup (needs := action.requests) (callback := dependencies) hints)

def Plans.erase (plans : Plans plan hints) : SourcePlannedClosingPlans.Plans (plan.map CloseEntry.erase) hints :=
  match plans with
  | .nil => .nil
  | .release rest => .release rest.erase
  | .retire rest => .retire rest.erase
  | .invoke callback rest => .invoke callback rest.erase

def Plans.append (first : Plans before firstHints) (second : Plans after secondHints) :
    Plans (before ++ after) (firstHints.append secondHints) :=
  match first with
  | .nil => second
  | .release rest => .release (rest.append second)
  | .retire rest => .retire (rest.append second)
  | .invoke callback rest => .invoke callback (rest.append second)

theorem Plans.closingForest_append (first : Plans before firstHints) (second : Plans after secondHints) :
    closingForest (first.append second).erase = (closingForest first.erase).append (closingForest second.erase) := by
  induction first <;> simp_all [Plans.append, Plans.erase, closingForest, Forest.append] <;> rfl

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

theorem Contents.erase (contents : Contents operations policy contracts world plans) :
    SourcePlannedClosingPlans.Contents operations policy contracts world plans.erase := by
  induction contents with
  | nil => exact .nil
  | release rest ih => exact .release ih
  | retire known rest ih => exact .retire known ih
  | invoke callback rest ih => exact .invoke callback.erase ih

theorem Contents.append
    (first : Contents operations policy contracts world before)
    (second : Contents operations policy contracts world after) :
    Contents operations policy contracts world (before.append after) := by
  induction first with
  | nil => exact second
  | release rest ih => exact .release ih
  | retire known rest ih => exact .retire known ih
  | invoke callback rest ih => exact .invoke callback ih

/-- Extract callback sources and exact retained plans from every saved frame,
including callbacks inside dormant captures. Scheduling remains separate. -/
theorem plan_contents [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy] {hints : Hints receiving} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (source : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      capture input output demand requirements records forest outside incoming outgoing)
    (built : makePlan capture = some plan) :
    ∃ plans : Plans plan (forClosing hints),
      Contents operations policy contracts world plans ∧ closingForest plans.erase = forest.forClosing := by
  induction capture generalizing input output demand requirements records receiving hints outsideScope outsideHints incoming outgoing plan with
  | nil => cases source; cases built; exact ⟨.nil, .nil, rfl⟩
  | push frame rest ih => cases source with
    | push head tail bound => cases head with
      | plain => obtain ⟨plans, contents, same⟩ := ih tail built; exact ⟨plans, contents, same⟩
      | handler => obtain ⟨plans, contents, same⟩ := ih tail built; exact ⟨plans, contents, same⟩
      | cell =>
          cases next : makePlan rest <;> simp [makePlan, next] at built
          case some suffix =>
            subst plan
            obtain ⟨plans, contents, same⟩ := ih tail next
            exact ⟨.release plans, .release contents, congrArg Forest.cell same⟩
      | armed scope callback annotation interface checked =>
          cases next : makePlan rest <;> simp [makePlan, next] at built
          case some suffix =>
            subst plan
            obtain ⟨plans, contents, same⟩ := ih tail next
            exact ⟨.invoke _ plans, .invoke callback contents, congrArg (Forest.cleanup _) same⟩
      | running | closing | retiring => simp [makePlan] at built
  | live owner inputType answerType saved caller rest ihSaved ihTail => cases source with
    | live known actionKnown inputAnnotation answerAnnotation scopeKnown held captured savedBound tail resume close bound =>
        cases inside : makePlan saved <;> cases outsidePlan : makePlan rest <;> simp [makePlan, inside, outsidePlan] at built
        case some.some first second =>
          subst plan
          obtain ⟨savedPlans, savedContents, savedSame⟩ := ihSaved captured inside
          obtain ⟨tailPlans, tailContents, tailSame⟩ := ihTail tail outsidePlan
          refine ⟨savedPlans.append (.retire tailPlans), savedContents.append (.retire known tailContents), ?_⟩
          exact (Plans.closingForest_append savedPlans (.retire (owner := owner) tailPlans)).trans
            (congr (congrArg Forest.append savedSame) (congrArg Forest.running tailSame))
  | spent owner answer caller rest ih => cases source with
    | spent known annotation scopeKnown tail bound => obtain ⟨plans, contents, same⟩ := ih tail built; exact ⟨plans, contents, same⟩

inductive Template (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (world : List Nat) (caller : Execution.Scope) :
    {plan : List CloseEntry} → {scope : Receiving} → {hints : Hints scope} → Plans plan hints →
      Footprint → Requirements (retirements (plan.map CloseEntry.erase)) → Prop where
  | nil : Template operations policy contracts tables world caller .nil [] (.request [] [])
  | release {plans : Plans tail hints} (rest : Template operations policy contracts tables world caller plans raw requirements) :
      Template operations policy contracts tables world caller (.release (identity := identity) (payload := payload) plans) raw
        (.sequence ((Requirements.request [] []).prepend
          (OwnerPhases.ofStack tables (closeControl caller tail).erase)) requirements)
  | retire (known : contracts owner = some contract)
      (rest : Template operations policy contracts tables world caller plans raw requirements) :
      Template operations policy contracts tables world caller (.retire (owner := owner) plans) raw (.sequence (.retire owner) requirements)
  | invoke {callbackPlan : Plan dependencies} {plans : Plans tail hints}
      (callback : ValueSummary operations policy contracts world (fun _ => none) [] action.action
        (.function .unit .unit action.requests latent (signature callbackPlan)))
      (rest : Template operations policy contracts tables world caller plans raw requirements) :
      Template operations policy contracts tables world caller (.invoke (action := action) callbackPlan plans)
        (DisposalProtection.callbackResidual (tail.map CloseEntry.erase) latent ++ raw)
        (.sequence ((Requirements.request [] (qualify true latent)).prepend
          (OwnerPhases.ofStack tables (closeControl caller tail).erase)) requirements)

theorem Contents.template {plans : Plans plan hints} (contents : Contents operations policy contracts world plans) :
    ∃ raw, ∃ requirements : Requirements (retirements (plan.map CloseEntry.erase)),
      Template operations policy contracts tables world caller plans raw requirements := by
  induction contents with
  | nil => exact ⟨[], _, .nil⟩
  | release rest ih => obtain ⟨raw, requirements, template⟩ := ih; exact ⟨raw, _, .release template⟩
  | retire known rest ih => obtain ⟨raw, requirements, template⟩ := ih; exact ⟨raw, _, .retire known template⟩
  | invoke callback rest ih => obtain ⟨raw, requirements, template⟩ := ih; exact ⟨_, _, .invoke callback template⟩

theorem Template.erase {plans : Plans plan hints}
    (template : Template operations policy contracts tables world caller plans raw requirements) :
    SourcePlannedClosingPlans.Template operations policy contracts tables world caller plans.erase raw requirements := by
  induction template with
  | nil => exact .nil
  | release rest ih =>
      rw [SourceAnnotatedRuntime.closeControl_erase]
      exact .release ih
  | retire known rest ih => exact .retire known ih
  | invoke callback rest ih =>
      rw [SourceAnnotatedRuntime.closeControl_erase]
      exact .invoke callback.erase ih

theorem Template.transport
    (template : Template operations policy contracts tables world caller plans raw requirements)
    (extension : contracts.Extends nextContracts) :
    Template operations policy nextContracts tables world caller plans raw requirements := by
  induction template with
  | nil => exact .nil
  | release rest ih => exact .release ih
  | retire known rest ih => exact .retire (extension _ _ known) ih
  | invoke callback rest ih => exact .invoke (SourceAnnotatedSources.Values.extension callback extension) ih

theorem Template.world_weaken
    (template : Template operations policy contracts tables world caller plans raw requirements)
    (larger : world ⊆ nextWorld) :
    Template operations policy contracts tables nextWorld caller plans raw requirements := by
  induction template with
  | nil => exact .nil
  | release rest ih => exact .release ih
  | retire known rest ih => exact .retire known ih
  | invoke callback rest ih => exact .invoke (SourceAnnotatedSources.Values.world_weaken callback larger) ih

theorem Template.tables_congr
    (template : Template operations policy contracts tables world caller plans raw requirements) :
    Template operations policy contracts nextTables world caller plans raw requirements := by
  have same : ∀ plan, OwnerPhases.ofStack tables (closeControl caller plan).erase =
      OwnerPhases.ofStack nextTables (closeControl caller plan).erase := by
    intro plan
    rw [SourceAnnotatedRuntime.closeControl_erase]
    exact RecursiveHandlerTables.closing_context_congr tables nextTables caller _
  induction template with
  | nil => exact .nil
  | release rest ih => rw [same]; exact .release ih
  | retire known rest ih => exact .retire known ih
  | invoke callback rest ih => rw [same]; exact .invoke callback ih

end Ash.OneShot.SourceAnnotatedClosingPlans

#print axioms Ash.OneShot.SourceAnnotatedClosingPlans.Plans.closingForest_append
#print axioms Ash.OneShot.SourceAnnotatedClosingPlans.Contents.erase
#print axioms Ash.OneShot.SourceAnnotatedClosingPlans.Contents.append
#print axioms Ash.OneShot.SourceAnnotatedClosingPlans.plan_contents
#print axioms Ash.OneShot.SourceAnnotatedClosingPlans.Contents.template
#print axioms Ash.OneShot.SourceAnnotatedClosingPlans.Template.erase

#print axioms Ash.OneShot.SourceAnnotatedClosingPlans.Template.transport
#print axioms Ash.OneShot.SourceAnnotatedClosingPlans.Template.world_weaken
#print axioms Ash.OneShot.SourceAnnotatedClosingPlans.Template.tables_congr
