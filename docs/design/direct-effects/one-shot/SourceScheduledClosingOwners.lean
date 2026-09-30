import SourceScheduledCaptureSource

/-! A disposing capture separates pending-ticket ownership from callback
ownership. Closing removes captured live owners; callbacks may reference only
owners in the surviving receiver. These necessary structural bounds reuse the
existing invocation, scheduling and closing proofs. -/
namespace Ash.OneShot.SourceScheduledPhaseRestriction
open SourceDependencyCapture (Scope)
open SourceDependencyOwners (owners)

/-- Closing recursively retires all live owners in the segment being closed. -/
theorem owners_closing_empty (scope : Scope) : owners scope.forClosing = [] := by
  induction scope <;> simp_all only [Scope.forClosing, owners, owners_append, List.nil_append]

end Ash.OneShot.SourceScheduledPhaseRestriction

namespace Ash.OneShot.SourceScheduledNeutral
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDependencyOwners (owners)

/-- Extending the caller with an owner-free prefix preserves the actual
selected saved body and tail. Membership alone is not an owner selection. -/
theorem OwnerCut.prefix_without_owner
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : OwnerCut owner whole front saved tail)
    {prefixHints : Hints prefixScope} (leading : Forest prefixHints)
    (absent : owner ∉ owners prefixScope) :
    OwnerCut owner (leading.append whole) (leading.append front) saved tail := by
  induction leading with
  | nil => exact cut
  | plain plan rest ih => exact .plain (ih absent)
  | handler rest ih => exact .handler (ih absent)
  | cell rest ih => exact .cell (ih absent)
  | cleanup plan rest ih => exact .cleanup (ih absent)
  | running rest ih => exact .running (ih absent)
  | live saved rest ihSaved ihRest =>
      apply OwnerCut.live
      · intro same; subst owner; exact absent List.mem_cons_self
      · exact ihRest (fun member => absent (List.mem_cons_of_mem _ (List.mem_append_right _ member)))
  | spent rest ih => exact .spent (ih absent)

/-- Closing cannot shadow an active owner in the surviving receiver, even
when it recursively closes dormant branches. Exact owner-cut evidence is
retained; action permissions and one-shot phases are checked separately. -/
theorem OwnerCut.closing_prefix
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : OwnerCut owner whole front saved tail)
    {prefixHints : Hints prefixScope} (leading : Forest prefixHints) :
    OwnerCut owner (leading.forClosing.append whole) (leading.forClosing.append front) saved tail := by
  apply cut.prefix_without_owner leading.forClosing
  simp only [SourceScheduledPhaseRestriction.owners_closing_empty, List.not_mem_nil, not_false_eq_true]

/-- An original active selection cannot end in a prefix that does not own
its target. Recover the same saved body and tail in the actual outside forest. -/
theorem OwnerCut.drop_prefix
    {prefixHints : Hints prefixScope} (leading : Forest prefixHints)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (absent : owner ∉ owners prefixScope)
    (cut : OwnerCut owner (leading.append whole) front saved tail) :
    ∃ outsideFrontScope, ∃ outsideFrontHints : Hints outsideFrontScope,
      ∃ outsideFront : Forest outsideFrontHints, OwnerCut owner whole outsideFront saved tail := by
  induction leading generalizing frontScope with
  | nil => exact ⟨_, _, front, cut⟩
  | plain plan rest ih => cases cut with | plain next => exact ih absent next
  | handler rest ih => cases cut with | handler next => exact ih absent next
  | cell rest ih => cases cut with | cell next => exact ih absent next
  | cleanup plan rest ih => cases cut with | cleanup next => exact ih absent next
  | running rest ih => cases cut with | running next => exact ih absent next
  | spent rest ih => cases cut with | spent next => exact ih absent next
  | live dormant rest ihDormant ihRest =>
      cases cut with
      | hit => exact False.elim (absent List.mem_cons_self)
      | live different next =>
          exact ihRest (fun member => absent (List.mem_cons_of_mem _ (List.mem_append_right _ member))) next

/-- Original active selection, surviving-owner membership and the existing
unique-owner invariant derive a selection after closing. No target cut is an
input. Dormant membership alone would not suffice without the original cut. -/
theorem OwnerCut.survives_closing
    {prefixHints : Hints prefixScope} (leading : Forest prefixHints)
    {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : OwnerCut owner (leading.append whole) front saved tail)
    (unique : (owners (prefixScope.append wholeScope)).Nodup)
    (survives : owner ∈ owners wholeScope) :
    ∃ nextFrontScope, ∃ nextFrontHints : Hints nextFrontScope,
      ∃ nextFront : Forest nextFrontHints,
        OwnerCut owner (leading.forClosing.append whole) nextFront saved tail := by
  have separate := (List.nodup_append.mp
    (by simpa only [SourceScheduledPhaseRestriction.owners_append] using unique)).2.2
  have absent : owner ∉ owners prefixScope := fun included => separate owner included owner survives rfl
  obtain ⟨_, _, outsideFront, selected⟩ := OwnerCut.drop_prefix leading absent cut
  exact ⟨_, _, leading.forClosing.append outsideFront, selected.closing_prefix leading⟩

end Ash.OneShot.SourceScheduledNeutral

namespace Ash.OneShot.SourceDependencyChecks
open SourceDependencyOwners (Within owners)
open SourceScheduledPhaseRestriction (selected_owner)

/-- An immediate invocation must name a live owner in its actual receiver.
The bound follows the existing dependency syntax; handler clause binders keep
their separate declaration checks. -/
theorem Local.owner_bound (checked : Local outward actions phases world dependencies scope) :
    Within world (owners scope) dependencies := by
  apply Local.rec
    (motive_1 := fun _ world dependencies scope _ => Within world (owners scope) dependencies)
    (motive_2 := fun _ _ _ _ _ => True)
    (t := checked)
  all_goals intros
  all_goals first
    | trivial
    | exact Within.pure
    | exact Within.request
    | (rename_i access restored ih
       cases access with
       | checked located known permission available => exact .invoke (selected_owner located))
    | (rename_i access scheduled ih
       cases access with
       | checked located known permission available unprotected closing => exact .invoke (selected_owner located))
    | (rename_i first second ihFirst ihSecond; exact .sequence ihFirst ihSecond)
    | (rename_i first second ihFirst ihSecond; exact .choice ihFirst ihSecond)
    | (rename_i body ih; exact .handler ih)
    | (rename_i body completion ihBody ihCompletion; exact .cleanup ihCompletion ihBody)
    | (rename_i body ih; exact .resource ih)

end Ash.OneShot.SourceDependencyChecks

namespace Ash.OneShot.SourceDependencyOwners
open SourceDependencyCapture (Scope)

/-- Owner references in every cleanup body, including dormant saved branches.
Plain pending code is omitted because disposal discards it. This bound is
independent of operation requirements, permission modes and one-shot phases. -/
inductive CallbacksWithin (world allowed : List Nat) : Scope → Prop where
  | nil : CallbacksWithin world allowed .nil
  | plain : CallbacksWithin world allowed rest → CallbacksWithin world allowed (.plain dependencies rest)
  | handler : CallbacksWithin world allowed rest → CallbacksWithin world allowed (.handler effect table families rest)
  | cell : CallbacksWithin world allowed rest → CallbacksWithin world allowed (.cell identity rest)
  | cleanup : Within world allowed callback → CallbacksWithin world allowed rest →
      CallbacksWithin world allowed (.cleanup needs callback rest)
  | running : CallbacksWithin world allowed rest → CallbacksWithin world allowed (.running rest)
  | live : CallbacksWithin world allowed saved → CallbacksWithin world allowed rest →
      CallbacksWithin world allowed (.live owner saved rest)
  | spent : CallbacksWithin world allowed rest → CallbacksWithin world allowed (.spent owner rest)

theorem CallbacksWithin.world_weaken (bound : CallbacksWithin world allowed scope) (larger : world ⊆ nextWorld) :
    CallbacksWithin nextWorld allowed scope := by
  induction bound with
  | nil => exact .nil
  | plain tail ih => exact .plain ih
  | handler tail ih => exact .handler ih
  | cell tail ih => exact .cell ih
  | cleanup callback tail ih => exact .cleanup (callback.world_weaken larger) ih
  | running tail ih => exact .running ih
  | live saved tail ihSaved ihTail => exact .live ihSaved ihTail
  | spent tail ih => exact .spent ih

/-- Splitting at the actual interpretation boundary preserves both callback
bounds; recomposition checks the same bodies without changing their owner set. -/
theorem CallbacksWithin.append_iff : CallbacksWithin world allowed (first.append second) ↔
    CallbacksWithin world allowed first ∧ CallbacksWithin world allowed second := by
  induction first with
  | nil => exact ⟨fun bound => ⟨.nil, bound⟩, fun pair => pair.2⟩
  | plain dependencies rest ih =>
      constructor
      · intro bound; cases bound with
        | plain tail => obtain ⟨inside, outside⟩ := ih.mp tail; exact ⟨.plain inside, outside⟩
      · rintro ⟨inside, outside⟩; cases inside with
        | plain tail => exact .plain (ih.mpr ⟨tail, outside⟩)
  | handler effect table families rest ih =>
      constructor
      · intro bound; cases bound with
        | handler tail => obtain ⟨inside, outside⟩ := ih.mp tail; exact ⟨.handler inside, outside⟩
      · rintro ⟨inside, outside⟩; cases inside with
        | handler tail => exact .handler (ih.mpr ⟨tail, outside⟩)
  | cell identity rest ih =>
      constructor
      · intro bound; cases bound with
        | cell tail => obtain ⟨inside, outside⟩ := ih.mp tail; exact ⟨.cell inside, outside⟩
      · rintro ⟨inside, outside⟩; cases inside with
        | cell tail => exact .cell (ih.mpr ⟨tail, outside⟩)
  | cleanup needs callback rest ih =>
      constructor
      · intro bound; cases bound with
        | cleanup code tail => obtain ⟨inside, outside⟩ := ih.mp tail; exact ⟨.cleanup code inside, outside⟩
      · rintro ⟨inside, outside⟩; cases inside with
        | cleanup code tail => exact .cleanup code (ih.mpr ⟨tail, outside⟩)
  | running rest ih =>
      constructor
      · intro bound; cases bound with
        | running tail => obtain ⟨inside, outside⟩ := ih.mp tail; exact ⟨.running inside, outside⟩
      · rintro ⟨inside, outside⟩; cases inside with
        | running tail => exact .running (ih.mpr ⟨tail, outside⟩)
  | live owner saved rest ihSaved ihRest =>
      constructor
      · intro bound; cases bound with
        | live dormant tail => obtain ⟨inside, outside⟩ := ihRest.mp tail; exact ⟨.live dormant inside, outside⟩
      · rintro ⟨inside, outside⟩; cases inside with
        | live dormant tail => exact .live dormant (ihRest.mpr ⟨tail, outside⟩)
  | spent owner rest ih =>
      constructor
      · intro bound; cases bound with
        | spent tail => obtain ⟨inside, outside⟩ := ih.mp tail; exact ⟨.spent inside, outside⟩
      · rintro ⟨inside, outside⟩; cases inside with
        | spent tail => exact .spent (ih.mpr ⟨tail, outside⟩)

/-- The closing traversal preserves precisely these callback references,
including callbacks in a dormant capture. -/
theorem CallbacksWithin.forClosing_iff : CallbacksWithin world allowed scope.forClosing ↔
    CallbacksWithin world allowed scope := by
  induction scope with
  | nil => exact Iff.rfl
  | plain dependencies rest ih =>
      exact ⟨fun bound => .plain (ih.mp bound), fun bound => by cases bound with | plain tail => exact ih.mpr tail⟩
  | handler effect table families rest ih =>
      exact ⟨fun bound => .handler (ih.mp bound), fun bound => by cases bound with | handler tail => exact ih.mpr tail⟩
  | spent owner rest ih =>
      exact ⟨fun bound => .spent (ih.mp bound), fun bound => by cases bound with | spent tail => exact ih.mpr tail⟩
  | cell identity rest ih =>
      constructor
      · intro bound; cases bound with | cell tail => exact .cell (ih.mp tail)
      · intro bound; cases bound with | cell tail => exact .cell (ih.mpr tail)
  | cleanup needs callback rest ih =>
      constructor
      · intro bound; cases bound with | cleanup code tail => exact .cleanup code (ih.mp tail)
      · intro bound; cases bound with | cleanup code tail => exact .cleanup code (ih.mpr tail)
  | running rest ih =>
      constructor
      · intro bound; cases bound with | running tail => exact .running (ih.mp tail)
      · intro bound; cases bound with | running tail => exact .running (ih.mpr tail)
  | live owner saved rest ihSaved ihRest =>
      constructor
      · intro bound
        obtain ⟨inside, tail⟩ := CallbacksWithin.append_iff.mp bound
        cases tail with | running tail => exact .live (ihSaved.mp inside) (ihRest.mp tail)
      · intro bound
        cases bound with | live inside tail =>
          exact CallbacksWithin.append_iff.mpr ⟨ihSaved.mpr inside, .running (ihRest.mpr tail)⟩

end Ash.OneShot.SourceDependencyOwners

namespace Ash.OneShot.SourceScheduledChecks
open SourceDependencyOwners (Within PendingWithin CallbacksWithin owners)
open SourceScheduledPhaseRestriction (owners_append owners_closing_empty)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)
open SourceContextualHints (Hints)
open SourceDeclarationPlans (ClausePlans)

variable [admission : DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy]

/-- Reuse scheduling's existing erasure, including its spent-marker projection. -/
theorem Local.owner_bound
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → certification.accepts outward required plans)
    {hints : Hints scope} {forest : Forest hints}
    {plan : SourceDeclarationPlans.Plan dependencies}
    (checked : Local outward actions phases world plan forest) :
    Within world (owners scope) dependencies := by
  simpa only [SourceDependencySchemes.owners_project] using
    ((checked.erase_with project).erase).owner_bound

/-- Every callback checked by the actual closing schedule references only
owners of the surviving receiver. Recursive live branches use the existing
ordered append decomposition, not a new disposal traversal. -/
theorem Pending.closing_owner_bound
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → certification.accepts outward required plans)
    {hints : Hints scope} {forest : Forest hints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (checked : Pending outward actions phases world forest.forClosing outside) :
    CallbacksWithin world (owners outsideScope) scope := by
  induction forest generalizing outsideScope with
  | nil => exact .nil
  | plain plan rest ih => exact .plain (ih checked)
  | handler rest ih => exact .handler (ih checked)
  | cell rest ih => cases checked with
    | cell tail => exact .cell (ih tail)
  | cleanup plan rest ih => cases checked with
    | cleanup callback tail =>
        apply CallbacksWithin.cleanup
        · simpa only [SourceDependencyOwners.owners, SourceScheduledPhaseRestriction.owners_append, owners_closing_empty, List.nil_append] using
            callback.owner_bound project
        · exact ih tail
  | running rest ih => cases checked with
    | running tail => exact .running (ih tail)
  | live saved rest ihSaved ihRest =>
      obtain ⟨inside, tail⟩ := (SourceScheduledRecomposition.pending_append_iff _ _ _).mp checked
      cases tail with
      | running tail =>
          apply CallbacksWithin.live
          · simpa only [SourceScheduledPhaseRestriction.owners_append, SourceDependencyOwners.owners, owners_closing_empty, List.nil_append] using ihSaved inside
          · exact ihRest tail
  | spent rest ih => exact .spent (ih checked)

/-- At one actual disposing cut, ordinary pending code uses captured owners,
while callbacks use surviving owners. Both bounds follow from the existing
request judgment, without a new admission premise or a replacement schedule. -/
theorem Local.disposal_owner_bounds
    (project : ∀ {clauses families required} {plans : ClausePlans clauses families},
      admission.accepts outward required plans → certification.accepts outward required plans)
    {wholeHints : Hints wholeScope} {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    (checked : Local outward actions phases world (.request (effect := effect) (operation := operation)) whole)
    (cut : SourceScheduledNeutral.Cut effect operation contract modes whole saved waiting)
    (disposes : contract.dispose = true) :
    PendingWithin world (owners savedScope) savedScope ∧
      CallbacksWithin world (owners waitingScope) savedScope := by
  cases checked with
  | request guarded scheduled =>
      refine ⟨SourceDependencySchemes.checked_request_owners guarded cut.erase.lookup disposes, ?_⟩
      have closes := scheduled _ _ _ _ _ _ cut.erase saved waiting cut.forest disposes
      have bounded := closes.closing_owner_bound project
      exact bounded

end Ash.OneShot.SourceScheduledChecks

namespace Ash.OneShot.SourceScheduledSourceRechecking
open SourceScheduledCapabilityAnnotations (DeclarationPolicy DeclarationLaws Retained)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDependencyOwners (CallbacksWithin owners)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

/-- The bound is a necessary consequence of structural closing, not another
successful-target premise added to the closing judgment. -/
theorem Closing.callback_owners
    (laws : DeclarationLaws declarations admission certification outward)
    (project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {hints : Hints scope} {forest : Forest hints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    {nextHints : Hints nextScope} {next : Forest nextHints}
    {source : Retained world forest outside}
    (closing : Closing outward actions phases source next) (ready : source.Valid outward actions phases) :
    CallbacksWithin world (owners nextScope) scope := by
  obtain ⟨annotation, valid, _⟩ := closing.compile_retaining laws project ready
  exact (annotation.compile_with laws valid).closing_owner_bound laws.projected

end Ash.OneShot.SourceScheduledSourceRechecking

namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceDependencyOwners (CallbacksWithin owners)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

variable [declarations : DeclarationPolicy]
  [admission : SourceScheduledChecks.DeclarationPolicy]
  [certification : SourcePlannedChecks.DeclarationPolicy]

theorem CaptureSource.callback_owners
    (laws : DeclarationLaws declarations admission certification outward)
    (_project : ∀ {clauses families required} {plans : SourceDeclarationPlans.ClausePlans clauses families},
      admission.accepts outward required plans → declarations.accepts required plans)
    {wholeHints : Hints wholeScope} {savedHints : Hints savedScope} {waitingHints : Hints waitingScope}
    {whole : Forest wholeHints} {saved : Forest savedHints} {waiting : Forest waitingHints}
    {cut : SourceScheduledNeutral.Cut effect operation contract modes whole saved waiting}
    {source : Retained world whole .nil}
    (captured : CaptureSource outward actions phases cut source rights) (disposes : rights.dispose = true) :
    CallbacksWithin world (owners waitingScope) savedScope := by
  obtain ⟨annotation, ready, _⟩ := captured.closing disposes
  have bounded := SourceScheduledChecks.Pending.closing_owner_bound
    (actions := actions) (phases := phases) (world := world)
    (forest := saved) (outsideScope := .running waitingScope)
    (outsideHints := SourceContextualHints.Hints.running waitingHints) (outside := .running waiting)
    laws.projected (annotation.compile_with laws ready)
  exact bounded

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledPhaseRestriction.owners_closing_empty
#print axioms Ash.OneShot.SourceScheduledNeutral.OwnerCut.prefix_without_owner
#print axioms Ash.OneShot.SourceScheduledNeutral.OwnerCut.closing_prefix
#print axioms Ash.OneShot.SourceScheduledNeutral.OwnerCut.drop_prefix
#print axioms Ash.OneShot.SourceScheduledNeutral.OwnerCut.survives_closing
#print axioms Ash.OneShot.SourceDependencyChecks.Local.owner_bound
#print axioms Ash.OneShot.SourceScheduledChecks.Local.owner_bound
#print axioms Ash.OneShot.SourceScheduledChecks.Pending.closing_owner_bound
#print axioms Ash.OneShot.SourceScheduledChecks.Local.disposal_owner_bounds
#print axioms Ash.OneShot.SourceScheduledSourceRechecking.Closing.callback_owners
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.CaptureSource.callback_owners

#print axioms Ash.OneShot.SourceDependencyOwners.CallbacksWithin.world_weaken
#print axioms Ash.OneShot.SourceDependencyOwners.CallbacksWithin.append_iff
#print axioms Ash.OneShot.SourceDependencyOwners.CallbacksWithin.forClosing_iff
