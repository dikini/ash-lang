import SourceConsumingCleanupAdmission

/-! Structural receiver plans expose the primitive checks needed after cleanup
insertion. The existing full source generator supplies expression rechecking;
this traversal retains every original code position and derives ReceiverChange.
A plan is source checking data, not a promise that its checks succeed. -/
namespace Ash.OneShot.SourceScheduledCleanupGeneration
open SourceScheduledCapabilityAnnotations (Code Retained DeclarationPolicy)
open SourceScheduledSourceRechecking (ReceiverChange)
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceScheduledCleanupInsertion (Insertion)
open SourceScheduledAdaptationCompilation (RequestFootprint)
open SourceScheduledSourceInterfaces (Declared)
open SourcePlanSignatures (signature)

/-- Original operation and handler checks are transported by equality. Current
and callback code supply the independently generated expression check trees. -/
inductive ReceiverPlan [DeclarationPolicy] :
    {world : List Nat} → {scope outsideScope nextScope : SourceDependencyCapture.Scope} →
    {hints : Hints scope} → {outsideHints : Hints outsideScope} → {nextHints : Hints nextScope} →
    {forest : Forest hints} → {outside : Forest outsideHints} →
    Retained world forest outside → Forest nextHints → Type where
  | operations {interfaces : SourceScheduledRetainedInterfaces.Interfaces world forest}
      {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
      {nextHints : Hints nextScope} {next : Forest nextHints}
      (preserved : interfaces.check outsideScope = interfaces.check nextScope) :
      ReceiverPlan (.operations (outside := outside) interfaces) next
  | plain {rest : Forest restHints} {outside : Forest outsideHints} {next : Forest nextHints}
      {code : Code world plan (rest.append outside)} {tail : Retained world rest outside} :
      CodeResult code (rest.append next) → ReceiverPlan tail next → ReceiverPlan (.plain code tail) next
  | handler {restHints : Hints restScope} {outsideHints : Hints outsideScope}
      {nextHints : Hints nextScope} {rest : Forest restHints} {outside : Forest outsideHints}
      {next : Forest nextHints} {tail : Retained world rest outside}
      (preserved : checkRequirements (restScope.append outsideScope) required =
        checkRequirements (restScope.append nextScope) required) :
      ReceiverPlan tail next →
      ReceiverPlan (.handler (effect := effect) (table := table) (families := families) (required := required) tail) next
  | cell : ReceiverPlan tail next → ReceiverPlan (.cell (identity := identity) tail) next
  | cleanup {rest : Forest restHints} {outside : Forest outsideHints} {next : Forest nextHints}
      {code : Code world plan (.running (rest.append outside))} {tail : Retained world rest outside} :
      CodeResult code (.running (rest.append next)) →
      ReceiverPlan tail next → ReceiverPlan (.cleanup (needs := needs) code tail) next
  | running : ReceiverPlan tail next → ReceiverPlan (.running tail) next
  | live {rest : Forest restHints} {outside : Forest outsideHints} {next : Forest nextHints}
      {saved : Retained world captured (rest.append outside)} {tail : Retained world rest outside} :
      ReceiverPlan saved (rest.append next) → ReceiverPlan tail next → ReceiverPlan (.live (owner := owner) saved tail) next
  | spent : ReceiverPlan tail next → ReceiverPlan (.spent (owner := owner) tail) next

variable [DeclarationPolicy]

def ReceiverPlan.checks {source : Retained world forest outside} (plan : ReceiverPlan source next) : Checks :=
  match plan with
  | .operations _ => .done
  | .plain code tail | .cleanup code tail => .both code.checks tail.checks
  | .handler _ tail | .cell tail | .running tail | .spent tail => tail.checks
  | .live saved tail => .both saved.checks tail.checks

/-- Derive the existing structural receiver judgment. No target validity or
receiver-change derivation is supplied by the caller. -/
theorem ReceiverPlan.rechecking {source : Retained world forest outside}
    (plan : ReceiverPlan source next) (ready : source.Valid outward actions phases)
    (checked : plan.checks.Holds outward) : ReceiverChange outward actions phases source next := by
  induction plan with
  | operations preserved => exact .operations _ (preserved.symm.trans ready)
  | plain code tail ih => exact .plain (code.rechecking _ _ _ ready.1 checked.1) (ih ready.2 checked.2)
  | handler preserved tail ih => exact .handler (preserved.symm.trans ready.1) (ih ready.2 checked)
  | cell tail ih => exact .cell (ih ready checked)
  | cleanup code tail ih => exact .cleanup (code.rechecking _ _ _ ready.1 checked.1) (ih ready.2 checked.2)
  | running tail ih => exact .running (ih ready checked)
  | live saved tail ihSaved ihTail => exact .live (ihSaved ready.1 checked.1) (ihTail ready.2 checked.2)
  | spent tail ih => exact .spent (ih ready checked)

/-- Generate every retained-frame case from the original source. The existing
mutual generator handles arbitrary code, including free owner calls and all
resource families. Success of the generated primitive checks remains explicit. -/
theorem receiver_plan {callback : Plan dependencies}
    (footprint : RequestFootprint callback required) (declared : Declared world (signature callback))
    {hints : Hints scope} {forest : Forest hints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    {nextHints : Hints nextScope} {next : Forest nextHints}
    (source : Retained world forest outside) (changed : Insertion needs callback outside next) :
    Nonempty (ReceiverPlan source next) := by
  induction forest generalizing outsideScope nextScope with
  | nil => cases source with
    | operations interfaces => exact ⟨.operations (interfaces_receiver interfaces changed)⟩
  | plain plan rest ih => cases source with
    | operations interfaces => exact ⟨.operations (interfaces_receiver interfaces changed)⟩
    | plain code tail =>
        obtain ⟨codePlan⟩ := code_generate footprint code declared (changed.prefix rest)
        obtain ⟨tailPlan⟩ := ih tail changed
        exact ⟨.plain codePlan tailPlan⟩
  | handler rest ih => cases source with
    | operations interfaces => exact ⟨.operations (interfaces_receiver interfaces changed)⟩
    | handler tail =>
        obtain ⟨tailPlan⟩ := ih tail changed
        exact ⟨.handler (changed.prefix rest).requirements tailPlan⟩
  | cell rest ih => cases source with
    | operations interfaces => exact ⟨.operations (interfaces_receiver interfaces changed)⟩
    | cell tail => obtain ⟨tailPlan⟩ := ih tail changed; exact ⟨.cell tailPlan⟩
  | cleanup plan rest ih => cases source with
    | operations interfaces => exact ⟨.operations (interfaces_receiver interfaces changed)⟩
    | cleanup code tail =>
        obtain ⟨codePlan⟩ := code_generate footprint code declared (.running (changed.prefix rest))
        obtain ⟨tailPlan⟩ := ih tail changed
        exact ⟨.cleanup codePlan tailPlan⟩
  | running rest ih => cases source with
    | operations interfaces => exact ⟨.operations (interfaces_receiver interfaces changed)⟩
    | running tail => obtain ⟨tailPlan⟩ := ih tail changed; exact ⟨.running tailPlan⟩
  | live saved rest ihSaved ihRest => cases source with
    | operations interfaces => exact ⟨.operations (interfaces_receiver interfaces changed)⟩
    | live inside tail =>
        obtain ⟨insidePlan⟩ := ihSaved inside (changed.prefix rest)
        obtain ⟨tailPlan⟩ := ihRest tail changed
        exact ⟨.live insidePlan tailPlan⟩
  | spent rest ih => cases source with
    | operations interfaces => exact ⟨.operations (interfaces_receiver interfaces changed)⟩
    | spent tail => obtain ⟨tailPlan⟩ := ih tail changed; exact ⟨.spent tailPlan⟩

end Ash.OneShot.SourceScheduledCleanupGeneration

#print axioms Ash.OneShot.SourceScheduledCleanupGeneration.ReceiverPlan.rechecking
#print axioms Ash.OneShot.SourceScheduledCleanupGeneration.receiver_plan

namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceScheduledCapabilityAnnotations (DeclarationLaws)
open SourceScheduledCleanupGeneration (ReceiverPlan)
open SourceScheduledAdaptationCompilation (RequestFootprint)
open SourceScheduledSourceInterfaces (Declared)
open SourcePlanSignatures (signature)
open SourceDeclarationPlans (Plan ClausePlans)
open SourceConsumingClauseAnnotations (Body)
open SourceRetainedPlans (Forest)
open SourceContextualHints (Hints)
open OwnerPhaseTransitions (spend)

variable [declarations : SourceScheduledCapabilityAnnotations.DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]
  [SourceScheduledChecks.DeclarationProjection admission certification]

/-- Cleanup admission derives both receiver changes from original source plans
and their primitive check trees. The existing recursive contextual rule remains
the rule being proved; no target annotation validity is an input. -/
theorem At.cleanup_planned
    {laws : DeclarationLaws declarations admission certification outward}
    {project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans}
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    {context : Context world owner outward actions phases whole front saved waiting}
    {body : Body world owner plan}
    {footprint : RequestFootprint callback required} {declared : Declared world (signature callback)}
    (covered : ∀ request ∈ required, request.1 ∈ needs)
    (resumption : ∀ permission, ReceiverPlan (context.resumption permission).val
      (.cleanup (needs := needs) callback (front.append (.spent (owner := owner) waiting))))
    (resumeChecked : ∀ permission, (resumption permission).checks.Holds outward)
    (closing : ∀ permission, ReceiverPlan (context.closing permission).val
      (.running (.cleanup (needs := needs) callback (front.append (.spent (owner := owner) waiting)))))
    (closeChecked : ∀ permission, (closing permission).checks.Holds outward)
    (inner : At laws (@project) body
      (context.cleanupSource laws (@project) footprint declared needs
        (fun permission => (resumption permission).rechecking (context.resumption permission).property (resumeChecked permission))
        (fun permission => (closing permission).rechecking (context.closing permission).property (closeChecked permission)))) :
    At laws (@project) (.cleanup (needs := needs) required footprint declared body) context :=
  .cleanupSource covered
    (fun permission => (resumption permission).rechecking (context.resumption permission).property (resumeChecked permission))
    (fun permission => (closing permission).rechecking (context.closing permission).property (closeChecked permission)) inner

end Ash.OneShot.SourceConsumingCleanupAdmission

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.At.cleanup_planned
