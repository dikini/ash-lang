import SourceConsumingHandlerInterference

/-! Composition and extraction of the existing callback-boundary summary.
These proofs authenticate finite bounds against actual recursive scopes; they
do not assume a valid successor or change source declaration admission. -/
namespace Ash.OneShot.SourceHandlerBoundaryComposition
open SourceDependencyCapture (Scope)
open SourceRecursiveRoutes (Shape scopeProviders)
open SourceHandlerInterference (exposed Shielded)
open SourceHandlerClosingInsertion (normal_append)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

/-- Appending a receiver hides exactly those prefix callback requirements
supplied by its builtins. Dormant captures use that same receiver. -/
theorem exposed_append_mem (front tail : Scope) :
    effect ∈ exposed (front.append tail).shape ↔
      (effect ∈ exposed front.shape ∧ effect ∉ scopeProviders tail.shape.normal) ∨
        effect ∈ exposed tail.shape := by
  induction front with
  | nil => simp [Scope.append, Scope.shape, exposed]
  | plain code rest ih | running rest ih | handler other table families rest ih => exact ih
  | cell identity rest ih | spent owner rest ih => exact ih
  | cleanup needs code rest ih =>
      simp only [Scope.append, Scope.shape, exposed, List.mem_append, List.mem_filter,
        decide_eq_true_eq, normal_append, SourceRecursiveRoutes.scope_providers_append] at *
      grind
  | live owner saved rest ihSaved ihRest =>
      simp only [Scope.append, Scope.shape, exposed, List.mem_append, List.mem_filter,
        decide_eq_true_eq, normal_append, SourceRecursiveRoutes.scope_providers_append] at *
      grind

/-- A single finite bound splits at the actual boundary. Prefix requirements
discharged by the tail must be restored when that prefix is considered alone. -/
theorem boundary_append_iff (front tail : Scope) :
    exposed (front.append tail).shape ⊆ bound ↔
      exposed front.shape ⊆ scopeProviders tail.shape.normal ++ bound ∧
        exposed tail.shape ⊆ bound := by
  constructor
  · intro covered
    constructor
    · intro effect member
      by_cases supplied : effect ∈ scopeProviders tail.shape.normal
      · exact List.mem_append_left _ supplied
      · exact List.mem_append_right _ (covered ((exposed_append_mem front tail).mpr (Or.inl ⟨member, supplied⟩)))
    · intro effect member
      exact covered ((exposed_append_mem front tail).mpr (Or.inr member))
  · rintro ⟨inside, outside⟩ effect member
    rcases (exposed_append_mem front tail).mp member with ⟨first, absent⟩ | second
    · exact (List.mem_append.mp (inside first)).resolve_left absent
    · exact outside second

/-- Recomposition for the existing structural shielding judgment. No new
admissibility predicate or second callback analysis is introduced. -/
theorem shielded_append_iff (front tail : Scope) :
    Shielded effect (front.append tail).shape context ↔
      Shielded effect front.shape (tail.shape.normal ++ context) ∧
        Shielded effect tail.shape context := by
  simp only [SourceHandlerInterference.shielded_summary, exposed_append_mem,
    SourceRecursiveRoutes.scope_providers_append, List.mem_append]
  constructor
  · intro checked
    constructor
    · intro member
      by_cases supplied : effect ∈ scopeProviders tail.shape.normal
      · exact Or.inl supplied
      · exact Or.inr (checked (Or.inl ⟨member, supplied⟩))
    · exact fun member => checked (Or.inr member)
  · rintro ⟨inside, outside⟩ (⟨member, absent⟩ | member)
    · exact (inside member).resolve_left absent
    · exact outside member

/-- The selected source cut determines both pieces; their bounds are derived
from the bound on the original whole scope. This also applies to dormant
captures nested in the selected prefix. -/
theorem boundary_at_cut {wholeHints : Hints wholeScope} {savedHints : Hints savedScope}
    {waitingHints : Hints waitingScope} {whole : Forest wholeHints}
    {saved : Forest savedHints} {waiting : Forest waitingHints}
    (cut : SourceScheduledNeutral.Cut effect operation contract modes whole saved waiting)
    (covered : exposed wholeScope.shape ⊆ bound) :
    exposed savedScope.shape ⊆ scopeProviders waitingScope.shape.normal ++ bound ∧
      exposed waitingScope.shape ⊆ bound := by
  rw [cut.erase.reconstruct_scope] at covered
  exact (boundary_append_iff savedScope waitingScope).mp covered

/-- A replacement receiver can discharge the same prefix requirements even
when its concrete scope differs. The target summary is derived, not assumed. -/
theorem boundary_recompose (front oldTail nextTail : Scope)
    (covered : exposed (front.append oldTail).shape ⊆ bound)
    (providers : scopeProviders oldTail.shape.normal ⊆ scopeProviders nextTail.shape.normal ++ nextBound)
    (retained : bound ⊆ nextBound)
    (outside : exposed nextTail.shape ⊆ nextBound) :
    exposed (front.append nextTail).shape ⊆ nextBound := by
  apply (boundary_append_iff front nextTail).mpr
  refine ⟨?_, outside⟩
  intro effect member
  rcases List.mem_append.mp (((boundary_append_iff front oldTail).mp covered).1 member) with supplied | exported
  · exact providers supplied
  · exact List.mem_append_right _ (retained exported)

/-- Closing retains every normally visible builtin and may reveal additional
builtins from dormant captures. This concerns provider membership only. -/
theorem closing_providers (scope : Scope) :
    scopeProviders scope.shape.normal ⊆ scopeProviders scope.forClosing.shape.normal := by
  induction scope with
  | nil => exact List.Subset.refl _
  | plain code rest ih | running rest ih | handler effect table families rest ih => exact ih
  | cleanup needs code rest ih | spent owner rest ih => exact ih
  | cell identity rest ih =>
      exact List.cons_subset_cons _ ih
  | live owner saved rest ihSaved ihRest =>
      intro effect member
      simp only [Scope.forClosing, normal_append, SourceRecursiveRoutes.scope_providers_append,
        Scope.shape, Shape.normal]
      exact List.mem_append_right _ (ihRest member)

/-- Materializing all saved cleanup cannot introduce an exposed callback
effect. The original summary already includes dormant callbacks. -/
theorem exposed_closing_subset (scope : Scope) :
    exposed scope.forClosing.shape ⊆ exposed scope.shape := by
  induction scope with
  | nil => exact List.Subset.refl _
  | plain code rest ih | running rest ih | handler effect table families rest ih => exact ih
  | cell identity rest ih | spent owner rest ih => exact ih
  | cleanup needs code rest ih =>
      intro effect member
      simp only [Scope.forClosing, Scope.shape, exposed, List.mem_append, List.mem_filter,
        decide_eq_true_eq] at member ⊢
      rcases member with ⟨needed, absent⟩ | remaining
      · exact Or.inl ⟨needed, fun supplied => absent (closing_providers rest supplied)⟩
      · exact Or.inr (ih remaining)
  | live owner saved rest ihSaved ihRest =>
      intro effect member
      rcases (exposed_append_mem saved.forClosing (.running rest.forClosing)).mp member with
        ⟨inside, absent⟩ | outside
      · simp only [Scope.shape, exposed, List.mem_append, List.mem_filter, decide_eq_true_eq]
        exact Or.inl ⟨ihSaved inside, fun supplied => absent (closing_providers rest supplied)⟩
      · exact List.mem_append_right _ (ihRest outside)

/-- Resume can supply additional builtins to dormant callbacks, but cannot
expose a new callback dependency. The caller prefix is retained in full. -/
theorem exposed_resume_subset (front saved tail : Scope) :
    exposed (saved.append (front.append (.spent owner tail))).shape ⊆
      exposed (front.append (.live owner saved tail)).shape := by
  intro effect member
  simp only [exposed_append_mem, Scope.shape, Shape.normal, exposed, List.mem_append,
    List.mem_filter, decide_eq_true_eq, normal_append, SourceRecursiveRoutes.scope_providers_append] at member ⊢
  grind

/-- Disposal preserves the same finite callback bound. This reuses the
closing-materialization lemma and the same full-prefix composition argument. -/
theorem exposed_dispose_subset (front saved tail : Scope) :
    exposed (saved.forClosing.append (.running (front.append (.spent owner tail)))).shape ⊆
      exposed (front.append (.live owner saved tail)).shape := by
  intro effect member
  rcases (exposed_append_mem saved.forClosing (.running (front.append (.spent owner tail)))).mp member with
    ⟨inside, absent⟩ | outside
  · apply exposed_resume_subset front saved tail
    exact (exposed_append_mem saved (front.append (.spent owner tail))).mpr
      (Or.inl ⟨exposed_closing_subset saved inside, absent⟩)
  · apply exposed_resume_subset front saved tail
    exact (exposed_append_mem saved (front.append (.spent owner tail))).mpr (Or.inr outside)

/-- The existing structural shielding derivation survives resumption. -/
theorem shielded_resume (front saved tail : Scope)
    (shielded : Shielded effect (front.append (.live owner saved tail)).shape context) :
    Shielded effect (saved.append (front.append (.spent owner tail))).shape context :=
  SourceHandlerInterference.shielded_summary.mpr (fun member =>
    SourceHandlerInterference.shielded_summary.mp shielded (exposed_resume_subset front saved tail member))

/-- The existing structural shielding derivation also survives disposal. -/
theorem shielded_dispose (front saved tail : Scope)
    (shielded : Shielded effect (front.append (.live owner saved tail)).shape context) :
    Shielded effect (saved.forClosing.append (.running (front.append (.spent owner tail)))).shape context :=
  SourceHandlerInterference.shielded_summary.mpr (fun member =>
    SourceHandlerInterference.shielded_summary.mp shielded (exposed_dispose_subset front saved tail member))

/-- Extract and preserve the bound at the actual owner selection. Independent
permissions and phase proofs still decide whether this resume is allowed. -/
theorem boundary_resume_at_owner {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : SourceScheduledNeutral.OwnerCut owner whole front saved tail)
    (covered : exposed wholeScope.shape ⊆ bound) :
    exposed (savedScope.append (frontScope.append (.spent owner tailScope))).shape ⊆ bound := by
  rw [(SourceContextualInvocationHints.selected_cut cut.found).reconstruct] at covered
  exact (exposed_resume_subset frontScope savedScope tailScope).trans covered

/-- The analogous statement for disposal uses the same selected owner and
actual saved scope; no future callback execution is assumed. -/
theorem boundary_dispose_at_owner {wholeHints : Hints wholeScope} {frontHints : Hints frontScope}
    {savedHints : Hints savedScope} {tailHints : Hints tailScope}
    {whole : Forest wholeHints} {front : Forest frontHints}
    {saved : Forest savedHints} {tail : Forest tailHints}
    (cut : SourceScheduledNeutral.OwnerCut owner whole front saved tail)
    (covered : exposed wholeScope.shape ⊆ bound) :
    exposed (savedScope.forClosing.append (.running (frontScope.append (.spent owner tailScope)))).shape ⊆ bound := by
  rw [(SourceContextualInvocationHints.selected_cut cut.found).reconstruct] at covered
  exact (exposed_dispose_subset frontScope savedScope tailScope).trans covered

/-- Feed a whole-scope bound into the existing request-guard transport. The
receiver's providers must be included before testing separation: a callback
hidden in the whole scope may be exposed at the insertion boundary. -/
theorem bypassed_guard_from_composed_boundary {front outside captured tail : Scope}
    (passed : SourceHandlerRequirements.reaches requested front = true)
    (different : requested ≠ installed)
    (found : SourceDependencyCapture.select requested operation outside =
      some (.handler captured tail contract modes))
    (checked : SourceDependencyCapture.CaptureGuard outward (front.append outside) requested operation)
    (covered : contract.dispose = true → exposed (front.append outside).shape ⊆ bound)
    (separate : installed ∉ scopeProviders outside.shape.normal ++ bound) :
    SourceDependencyCapture.CaptureGuard outward
      (front.append (.handler installed table families outside)) requested operation :=
  SourceConsumingHandlerInterference.bypassed_guard_from_boundary_bound passed different found checked
    (fun disposes => ((boundary_append_iff front outside).mp (covered disposes)).1) separate

namespace Examples

/-- The only callback is dormant; its receiver currently provides its effect. -/
def dormant : Scope := .live 37 (.cleanup [.cell 4] .pure .nil) .nil
def receiver : Scope := .cell 4 .nil

theorem hidden_in_whole_exposed_in_prefix :
    exposed (dormant.append receiver).shape = [] ∧ exposed dormant.shape = [.cell 4] := ⟨rfl, rfl⟩

/-- It would be unsound to give the detached prefix the whole scope's empty
boundary bound. Its receiver dependency is necessary, not an extra permission. -/
theorem empty_bound_does_not_split :
    exposed (dormant.append receiver).shape ⊆ ([] : List Instance) ∧
      ¬ exposed dormant.shape ⊆ ([] : List Instance) := by
  refine ⟨List.Subset.refl [], ?_⟩
  intro impossible
  exact List.not_mem_nil (impossible (by decide : Instance.cell 4 ∈ exposed dormant.shape))

/-- Both ways of consuming this dormant continuation retain the supplying
cell and keep its callback hidden at the outer boundary. -/
theorem callback_stays_supplied :
    exposed ((Scope.cleanup [.cell 4] .pure .nil).append (.spent 37 receiver)).shape = [] ∧
      exposed ((Scope.cleanup [.cell 4] .pure .nil).forClosing.append (.running (.spent 37 receiver))).shape = [] :=
  ⟨rfl, rfl⟩

end Examples

end Ash.OneShot.SourceHandlerBoundaryComposition

#print axioms Ash.OneShot.SourceHandlerBoundaryComposition.exposed_append_mem
#print axioms Ash.OneShot.SourceHandlerBoundaryComposition.boundary_append_iff
#print axioms Ash.OneShot.SourceHandlerBoundaryComposition.shielded_append_iff
#print axioms Ash.OneShot.SourceHandlerBoundaryComposition.boundary_at_cut
#print axioms Ash.OneShot.SourceHandlerBoundaryComposition.boundary_recompose
#print axioms Ash.OneShot.SourceHandlerBoundaryComposition.closing_providers
#print axioms Ash.OneShot.SourceHandlerBoundaryComposition.exposed_closing_subset
#print axioms Ash.OneShot.SourceHandlerBoundaryComposition.exposed_resume_subset
#print axioms Ash.OneShot.SourceHandlerBoundaryComposition.exposed_dispose_subset
#print axioms Ash.OneShot.SourceHandlerBoundaryComposition.shielded_resume
#print axioms Ash.OneShot.SourceHandlerBoundaryComposition.shielded_dispose
#print axioms Ash.OneShot.SourceHandlerBoundaryComposition.boundary_resume_at_owner
#print axioms Ash.OneShot.SourceHandlerBoundaryComposition.boundary_dispose_at_owner
#print axioms Ash.OneShot.SourceHandlerBoundaryComposition.bypassed_guard_from_composed_boundary
#print axioms Ash.OneShot.SourceHandlerBoundaryComposition.Examples.hidden_in_whole_exposed_in_prefix
#print axioms Ash.OneShot.SourceHandlerBoundaryComposition.Examples.empty_bound_does_not_split
#print axioms Ash.OneShot.SourceHandlerBoundaryComposition.Examples.callback_stays_supplied
