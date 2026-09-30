import SourceScheduledSourceRechecking

/-! Source rechecking when only the outside receiver changes. Unlike general
RetainedChange, these rules cannot discard or replace retained code positions.
Their bound projection therefore remains exactly the original snapshot. -/
namespace Ash.OneShot.SourceScheduledSourceRechecking
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceScheduledCapabilityAnnotations (Code Retained DeclarationPolicy DeclarationLaws)
open SourceBoundSnapshots.Retained (ofCapability)

inductive ReceiverChange [DeclarationPolicy] (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) :
    {world : List Nat} → {scope outsideScope nextScope : SourceDependencyCapture.Scope} →
    {hints : Hints scope} → {outsideHints : Hints outsideScope} → {nextHints : Hints nextScope} →
    {forest : Forest hints} → {outside : Forest outsideHints} →
    Retained world forest outside → Forest nextHints → Prop where
  | same {source : Retained world forest outside} : ReceiverChange outward actions phases source outside
  | provide {source : Retained world forest outside}
      (ready : source.Valid outward actions phases)
      (previous : ReceiverChange outward actions phases source receiver)
      (inserted : SourceScheduledProviders.Insertion identity receiver next) :
      ReceiverChange outward actions phases source next
  | operations {forest : Forest hints} {nextHints : Hints nextScope} {next : Forest nextHints}
      {original : SourceScheduledRetainedInterfaces.Interfaces world forest}
      (interfaces : SourceScheduledRetainedInterfaces.Interfaces world forest)
      (supplied : interfaces.check nextScope = true) :
      ReceiverChange outward actions phases (.operations original) next
  | plain {rest : Forest restHints} {outside : Forest outsideHints} {next : Forest nextHints}
      {code : Code world plan (rest.append outside)} {tail : Retained world rest outside}
      (codeChanged : Expression outward actions phases code (rest.append next)) :
      ReceiverChange outward actions phases tail next → ReceiverChange outward actions phases (.plain code tail) next
  | handler {restHints : Hints restScope} {rest : Forest restHints}
      {nextHints : Hints nextScope} {next : Forest nextHints}
      {tail : Retained world rest outside}
      (supplied : checkRequirements (restScope.append nextScope) required = true) :
      ReceiverChange outward actions phases tail next →
      ReceiverChange outward actions phases (.handler (effect := effect) (table := table) (families := families) (required := required) tail) next
  | cell : ReceiverChange outward actions phases tail next →
      ReceiverChange outward actions phases (.cell (identity := identity) tail) next
  | cleanup {rest : Forest restHints} {outside : Forest outsideHints} {next : Forest nextHints}
      {code : Code world plan (.running (rest.append outside))} {tail : Retained world rest outside}
      (callback : Expression outward actions phases code (.running (rest.append next))) :
      ReceiverChange outward actions phases tail next → ReceiverChange outward actions phases (.cleanup (needs := needs) code tail) next
  | running : ReceiverChange outward actions phases tail next → ReceiverChange outward actions phases (.running tail) next
  | live {rest : Forest restHints} {outside : Forest outsideHints} {next : Forest nextHints}
      {saved : Retained world captured (rest.append outside)} {tail : Retained world rest outside} :
      ReceiverChange outward actions phases saved (rest.append next) → ReceiverChange outward actions phases tail next →
      ReceiverChange outward actions phases (.live (owner := owner) saved tail) next
  | spent : ReceiverChange outward actions phases tail next → ReceiverChange outward actions phases (.spent (owner := owner) tail) next

variable [declarations : DeclarationPolicy]

theorem ReceiverChange.rechecking {source : Retained world forest outside}
    (changed : ReceiverChange outward actions phases source next) :
    RetainedChange outward actions phases source forest next := by
  induction changed with
  | same => exact .same
  | provide ready previous inserted ih => exact .provide ready ih inserted
  | operations interfaces supplied => exact .operations interfaces supplied
  | plain code tail ih => exact .plain code ih
  | handler supplied tail ih => exact .handler supplied ih
  | cell tail ih => exact .cell ih
  | cleanup code tail ih => exact .cleanup code ih
  | running tail ih => exact .running ih
  | live saved tail ihSaved ihTail => exact .live ihSaved ihTail
  | spent tail ih => exact .spent ih

theorem ReceiverChange.empty {source : Retained world .nil outside} : ReceiverChange outward actions phases source next := by
  rw [retained_nil_eq source]
  exact .operations .nil rfl

/-- A retained atomic request can acquire a builtin or resumptive receiver
regardless of whether its original annotation was operation-only or selected.
Case analysis uses the original annotation; no target validity is assumed. -/
theorem ReceiverChange.request
    {source : Retained world (.plain (.request (effect := effect) (operation := operation)) .nil) outside}
    {nextHints : Hints nextScope} {next : Forest nextHints}
    (supplied : SourceContextualClauses.RequestCapability effect operation nextScope) :
    ReceiverChange outward actions phases source next := by
  cases source with
  | operations interfaces =>
      apply ReceiverChange.operations (.plain .nil [(effect, operation)] .request .request .nil)
      change (SourceContextualHints.checkRequirements nextScope [(effect, operation)] && true) = true
      rw [Bool.and_true]
      apply SourceContextualRequirements.check_requirements_iff.mpr
      intro request member
      cases List.mem_singleton.mp member
      exact supplied
  | plain code tail => exact .plain (.capability supplied) .empty

variable [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- No target-validity premise is needed. Current code reuses the existing
expression compiler; the retained traversal preserves every original position. -/
theorem ReceiverChange.compile_retaining
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {source : Retained world forest outside}
    (changed : ReceiverChange outward actions phases source next) (ready : source.Valid outward actions phases) :
    ∃ annotation : Retained world forest next,
      annotation.Valid outward actions phases ∧ ofCapability annotation = ofCapability source := by
  induction changed with
  | same => exact ⟨_, ready, rfl⟩
  | provide original previous inserted ih =>
      obtain ⟨middle, middleReady, middleKept⟩ := ih ready
      obtain ⟨next, nextReady, nextKept⟩ := middle.provide_receiver_retaining laws project middleReady inserted
      exact ⟨next, nextReady, nextKept.trans middleKept⟩
  | operations interfaces supplied => exact ⟨.operations interfaces, supplied, rfl⟩
  | plain code tail ih =>
      obtain ⟨code, codeReady, codeKept⟩ := code.compile_retaining laws project ready.1
      obtain ⟨rest, restReady, restKept⟩ := ih ready.2
      exact ⟨.plain code rest, ⟨codeReady, restReady⟩, by simp only [ofCapability, codeKept, restKept]⟩
  | handler supplied tail ih =>
      obtain ⟨rest, valid, kept⟩ := ih ready.2
      exact ⟨.handler rest, ⟨supplied, valid⟩, congrArg SourceBoundSnapshots.Retained.handler kept⟩
  | cell tail ih =>
      obtain ⟨rest, valid, kept⟩ := ih ready
      exact ⟨.cell rest, valid, congrArg SourceBoundSnapshots.Retained.cell kept⟩
  | cleanup code tail ih =>
      obtain ⟨code, codeReady, codeKept⟩ := code.compile_retaining laws project ready.1
      obtain ⟨rest, restReady, restKept⟩ := ih ready.2
      exact ⟨.cleanup code rest, ⟨codeReady, restReady⟩, by simp only [ofCapability, codeKept, restKept]⟩
  | running tail ih =>
      obtain ⟨rest, valid, kept⟩ := ih ready
      exact ⟨.running rest, valid, congrArg SourceBoundSnapshots.Retained.running kept⟩
  | live saved tail ihSaved ihTail =>
      obtain ⟨inside, insideReady, insideKept⟩ := ihSaved ready.1
      obtain ⟨rest, restReady, restKept⟩ := ihTail ready.2
      exact ⟨.live inside rest, ⟨insideReady, restReady⟩, by simp only [ofCapability, insideKept, restKept]⟩
  | spent tail ih =>
      obtain ⟨rest, valid, kept⟩ := ih ready
      exact ⟨.spent rest, valid, congrArg SourceBoundSnapshots.Retained.spent kept⟩

end Ash.OneShot.SourceScheduledSourceRechecking

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ReceiverChange.rechecking
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ReceiverChange.empty
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ReceiverChange.compile_retaining

#print axioms Ash.OneShot.SourceScheduledSourceRechecking.ReceiverChange.request
