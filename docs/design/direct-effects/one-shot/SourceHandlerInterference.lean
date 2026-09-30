import SourceRecursiveRoutes

/-! Exact finite interference checks for inserting a source handler into the
original interpretation context of a closing computation. This addresses
callback routing, not the separate operation-table and continuation checks. -/
namespace Ash.OneShot.SourceHandlerInterference
open ScopedExpressions
open SourceResourceRoutes (Context Route)
open SourceRecursiveRoutes (Shape Closing scopeProviders)

/-- A route survives an inserted handler exactly when it requests another
effect or already resolves to a builtin before reaching the insertion. -/
theorem route_insert_iff (front : Context) :
    Route outward (front ++ .handler effect :: original) requested target ↔
      Route outward (front ++ original) requested target ∧
        (requested ≠ effect ∨ requested ∈ scopeProviders front) := by
  induction front with
  | nil =>
      constructor
      · intro route
        cases route with
        | handler different rest => exact ⟨rest, Or.inl different⟩
      · rintro ⟨route, safe⟩
        exact .handler (safe.resolve_right (by simp [scopeProviders])) route
  | cons entry rest ih =>
      cases entry with
      | cell identity =>
          by_cases same : requested = .cell identity
          · subst requested
            constructor
            · intro route
              cases route with
              | cell same => exact ⟨.cell rfl, Or.inr (by simp [scopeProviders])⟩
              | cellMiss different rest => exact False.elim (different rfl)
            · rintro ⟨route, safe⟩
              cases route with
              | cell same => exact .cell rfl
              | cellMiss different rest => exact False.elim (different rfl)
          · constructor
            · intro route
              cases route with
              | cell equal => exact False.elim (same equal)
              | cellMiss different next =>
                  obtain ⟨old, safe⟩ := ih.mp next
                  exact ⟨.cellMiss different old, safe.imp_right (List.mem_cons_of_mem _)⟩
            · rintro ⟨route, safe⟩
              cases route with
              | cell equal => exact False.elim (same equal)
              | cellMiss different next =>
                  apply Route.cellMiss different
                  apply ih.mpr ⟨next, ?_⟩
                  simpa only [scopeProviders, List.mem_cons, same, false_or] using safe
      | handler other =>
          constructor
          · intro route
            cases route with
            | handler different next =>
                obtain ⟨old, safe⟩ := ih.mp next
                exact ⟨.handler different old, safe⟩
          · rintro ⟨route, safe⟩
            cases route with
            | handler different next => exact .handler different (ih.mpr ⟨next, safe⟩)
      | cleanup needs =>
          constructor
          · intro route
            cases route with
            | cleanup next =>
                obtain ⟨old, safe⟩ := ih.mp next
                exact ⟨.cleanup old, safe⟩
          · rintro ⟨route, safe⟩
            cases route with
            | cleanup next => exact .cleanup (ih.mpr ⟨next, safe⟩)

/-- Each callback requesting the inserted effect must be shielded by a
builtin in its own original suffix. Dormant captures use the receiving
suffix as well. There is no premise about successful future execution. -/
inductive Shielded (effect : Instance) : Shape → Context → Prop where
  | nil : Shielded effect .nil front
  | plain (tail : Shielded effect rest front) : Shielded effect (.plain rest) front
  | handler (tail : Shielded effect rest front) : Shielded effect (.handler other rest) front
  | cell (tail : Shielded effect rest front) : Shielded effect (.cell identity rest) front
  | cleanup (shield : effect ∈ needs → effect ∈ scopeProviders (rest.normal ++ front))
      (tail : Shielded effect rest front) : Shielded effect (.cleanup needs rest) front
  | live (inside : Shielded effect saved (rest.normal ++ front))
      (outside : Shielded effect rest front) : Shielded effect (.live saved rest) front
  | spent (tail : Shielded effect rest front) : Shielded effect (.spent rest) front

/-- Exact preservation of closing checks. Handler removal during closing
leaves the surviving context unchanged; only original callback routes can
be intercepted. The same route targets witness both judgments. -/
theorem closing_insert_iff (shape : Shape) (front : Context) :
    Closing outward shape (front ++ .handler effect :: original) surviving ↔
      Closing outward shape (front ++ original) surviving ∧ Shielded effect shape front := by
  induction shape generalizing front surviving with
  | nil => exact ⟨fun _ => ⟨.nil, .nil⟩, fun _ => .nil⟩
  | plain rest ih =>
      constructor
      · intro checked
        cases checked with
        | plain tail => obtain ⟨old, safe⟩ := ih front (surviving := surviving) |>.mp tail; exact ⟨.plain old, .plain safe⟩
      · rintro ⟨checked, safe⟩
        cases checked with
        | plain tail => cases safe with | plain next => exact .plain ((ih front (surviving := surviving)).mpr ⟨tail, next⟩)
  | handler other rest ih =>
      constructor
      · intro checked
        cases checked with
        | handler tail => obtain ⟨old, safe⟩ := ih front (surviving := surviving) |>.mp tail; exact ⟨.handler old, .handler safe⟩
      · rintro ⟨checked, safe⟩
        cases checked with
        | handler tail => cases safe with | handler next => exact .handler ((ih front (surviving := surviving)).mpr ⟨tail, next⟩)
  | cell identity rest ih =>
      constructor
      · intro checked
        cases checked with
        | cell tail => obtain ⟨old, safe⟩ := ih front (surviving := surviving) |>.mp tail; exact ⟨.cell old, .cell safe⟩
      · rintro ⟨checked, safe⟩
        cases checked with
        | cell tail => cases safe with | cell next => exact .cell ((ih front (surviving := surviving)).mpr ⟨tail, next⟩)
  | spent rest ih =>
      constructor
      · intro checked
        cases checked with
        | spent tail => obtain ⟨old, safe⟩ := ih front (surviving := surviving) |>.mp tail; exact ⟨.spent old, .spent safe⟩
      · rintro ⟨checked, safe⟩
        cases checked with
        | spent tail => cases safe with | spent next => exact .spent ((ih front (surviving := surviving)).mpr ⟨tail, next⟩)
  | cleanup needs rest ih =>
      constructor
      · intro checked
        cases checked with
        | cleanup routes tail =>
            have unpack requested (member : requested ∈ needs) := routes requested member
            obtain ⟨old, safe⟩ := (ih front (surviving := surviving)).mp tail
            refine ⟨.cleanup (fun requested member => ?_) old, .cleanup (fun member => ?_) safe⟩
            · obtain ⟨target, first, second⟩ := unpack requested member
              have prior := (route_insert_iff (rest.normal ++ front)).mp (by simpa only [List.append_assoc] using first)
              exact ⟨target, by simpa only [List.append_assoc] using prior.1, second⟩
            · obtain ⟨target, first, second⟩ := unpack effect member
              have prior := (route_insert_iff (rest.normal ++ front)).mp (by simpa only [List.append_assoc] using first)
              exact prior.2.resolve_left (by simp)
      · rintro ⟨checked, safe⟩
        cases checked with
        | cleanup routes tail => cases safe with
          | cleanup shield next =>
              refine .cleanup (fun requested member => ?_) ((ih front (surviving := surviving)).mpr ⟨tail, next⟩)
              obtain ⟨target, first, second⟩ := routes requested member
              refine ⟨target, ?_, second⟩
              have safeRoute : requested ≠ effect ∨ requested ∈ scopeProviders (rest.normal ++ front) := by
                by_cases same : requested = effect
                · exact Or.inr (same ▸ shield (same ▸ member))
                · exact Or.inl same
              have inserted := (route_insert_iff (rest.normal ++ front)).mpr
                ⟨by simpa only [List.append_assoc] using first, safeRoute⟩
              simpa only [List.append_assoc] using inserted
  | live saved rest ihSaved ihRest =>
      constructor
      · intro checked
        cases checked with
        | live inside outside =>
            obtain ⟨oldInside, safeInside⟩ := (ihSaved (rest.normal ++ front) (surviving := rest.closing ++ surviving)).mp
              (by simpa only [List.append_assoc] using inside)
            obtain ⟨oldOutside, safeOutside⟩ := (ihRest front (surviving := surviving)).mp outside
            exact ⟨.live (by simpa only [List.append_assoc] using oldInside) oldOutside, .live safeInside safeOutside⟩
      · rintro ⟨checked, safe⟩
        cases checked with
        | live inside outside => cases safe with
          | live safeInside safeOutside =>
              refine .live ?_ ((ihRest front (surviving := surviving)).mpr ⟨outside, safeOutside⟩)
              have inserted := (ihSaved (rest.normal ++ front) (surviving := rest.closing ++ surviving)).mpr
                ⟨by simpa only [List.append_assoc] using inside, safeInside⟩
              simpa only [List.append_assoc] using inserted

/-- A finite check of the structural shielding obligations. -/
def check (effect : Instance) : Shape → Context → Bool
  | .nil, _ => true
  | .plain rest, front | .handler _ rest, front | .cell _ rest, front | .spent rest, front => check effect rest front
  | .cleanup needs rest, front =>
      decide (effect ∈ needs → effect ∈ scopeProviders (rest.normal ++ front)) && check effect rest front
  | .live saved rest, front => check effect saved (rest.normal ++ front) && check effect rest front

theorem check_sound (shape : Shape) (accepted : check effect shape front = true) : Shielded effect shape front := by
  induction shape generalizing front with
  | nil => exact .nil
  | plain rest ih => exact .plain (ih accepted)
  | handler other rest ih => exact .handler (ih accepted)
  | cell identity rest ih => exact .cell (ih accepted)
  | spent rest ih => exact .spent (ih accepted)
  | cleanup needs rest ih =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at accepted
      exact .cleanup accepted.1 (ih accepted.2)
  | live saved rest ihSaved ihRest =>
      simp only [check, Bool.and_eq_true] at accepted
      exact .live (ihSaved accepted.1) (ihRest accepted.2)

theorem check_complete (safe : Shielded effect shape front) : check effect shape front = true := by
  induction safe with
  | nil => rfl
  | plain tail ih | handler tail ih | cell tail ih | spent tail ih => exact ih
  | cleanup shield tail ih =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨shield, ih⟩
  | live inside outside ihInside ihOutside =>
      simp only [check, Bool.and_eq_true]
      exact ⟨ihInside, ihOutside⟩

theorem check_iff : check effect shape front = true ↔ Shielded effect shape front :=
  ⟨check_sound shape, check_complete⟩

/-- Requirements exposed at the insertion boundary. The list records only
callback effects not supplied by a builtin in their own original suffix.
It is a finite dependency summary, not a count of continuation uses. -/
def exposed : Shape → List Instance
  | .nil => []
  | .plain rest | .handler _ rest | .cell _ rest | .spent rest => exposed rest
  | .cleanup needs rest =>
      needs.filter (fun effect => decide (effect ∉ scopeProviders rest.normal)) ++ exposed rest
  | .live saved rest =>
      (exposed saved).filter (fun effect => decide (effect ∉ scopeProviders rest.normal)) ++ exposed rest

/-- The full recursive shielding check factors through a finite effect list.
Multiplicity does not affect this obligation. The original ordered shape
still determines which builtin can shield each callback. -/
theorem check_summary (shape : Shape) : check effect shape front = true ↔
    (effect ∈ exposed shape → effect ∈ scopeProviders front) := by
  induction shape generalizing front with
  | nil => simp [check, exposed]
  | plain rest ih | handler other rest ih | cell identity rest ih | spent rest ih => exact ih
  | cleanup needs rest ih =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq, ih, exposed, List.mem_append,
        List.mem_filter, SourceRecursiveRoutes.scope_providers_append]
      by_cases suppliedHere : effect ∈ scopeProviders rest.normal <;>
        by_cases outside : effect ∈ scopeProviders front <;> simp_all
  | live saved rest ihSaved ihRest =>
      simp only [check, Bool.and_eq_true, ihSaved, ihRest, exposed, List.mem_append,
        List.mem_filter, decide_eq_true_eq, SourceRecursiveRoutes.scope_providers_append]
      by_cases suppliedHere : effect ∈ scopeProviders rest.normal <;>
        by_cases outside : effect ∈ scopeProviders front <;> simp_all

theorem shielded_summary : Shielded effect shape front ↔
    (effect ∈ exposed shape → effect ∈ scopeProviders front) :=
  check_iff.symm.trans (check_summary shape)

theorem route_requirements (route : Route outward context effect target) :
    effect ∈ scopeProviders context ++ outward := by
  induction route with
  | outside included => exact included
  | cell same => simp [same, scopeProviders]
  | cellMiss different tail ih => exact List.mem_cons_of_mem _ ih
  | handler different tail ih | cleanup tail ih => exact ih

/-- Existing closing evidence bounds the new finite summary. It does not
require a stronger effect annotation on the captured computation. -/
theorem exposed_bound (checked : Closing outward shape original surviving) :
    exposed shape ⊆ scopeProviders original ++ outward := by
  induction checked with
  | nil => exact List.nil_subset _
  | plain tail ih | handler tail ih | cell tail ih | spent tail ih => exact ih
  | @cleanup needs rest original surviving routes tail ih =>
      intro effect member
      rcases List.mem_append.mp member with callback | remaining
      · have included := List.mem_filter.mp callback
        have absent := of_decide_eq_true included.2
        obtain ⟨target, first, second⟩ := routes effect included.1
        have bound := route_requirements first
        rw [SourceRecursiveRoutes.scope_providers_append, List.append_assoc] at bound
        exact (List.mem_append.mp bound).resolve_left absent
      · exact ih remaining
  | @live saved rest original surviving inside outside ihInside ihOutside =>
      intro effect member
      rcases List.mem_append.mp member with captured | remaining
      · have included := List.mem_filter.mp captured
        have absent := of_decide_eq_true included.2
        have bound := ihInside included.1
        rw [SourceRecursiveRoutes.scope_providers_append, List.append_assoc] at bound
        exact (List.mem_append.mp bound).resolve_left absent
      · exact ihOutside remaining

/-- For an already checked closing computation, the finite checker exactly
decides whether inserting this handler preserves its closing judgment. -/
theorem check_closing_iff (checked : Closing outward shape (front ++ original) surviving) :
    check effect shape front = true ↔ Closing outward shape (front ++ .handler effect :: original) surviving := by
  rw [check_iff, closing_insert_iff]
  exact ⟨fun safe => ⟨checked, safe⟩, And.right⟩

/-- A captured computation's existing closing-effect row supplies a sufficient
declaration-level check. Exact shielding remains available when effects
overlap; row exclusion is not imposed as the definition of admission. -/
theorem captured_row_separation (checked : Closing outward shape [] [])
    (separate : effect ∉ outward) : Closing outward shape [.handler effect] [] := by
  apply (check_closing_iff (front := []) checked).mp
  apply (check_summary shape).mpr
  intro member
  exact False.elim (separate (exposed_bound checked member))

/-- Reuse the established closing realization and ownership proof. The
new source check preserves exact callback routes; typing and resource
support remain independent obligations on the same realized stack. -/
theorem realized_interfaces (realized : SourceRecursiveRoutes.Realizes shape stack plan)
    (closing : Closing outward shape (front ++ originalContext) survivingContext)
    (safe : check effect shape front = true)
    (originalScope : SourceRecursiveRoutes.Scope (front ++ .handler effect :: originalContext) original)
    (survivingScope : SourceRecursiveRoutes.Scope survivingContext surviving)
    (supported : Supported stack.erase (original.visible ++ resources))
    (available : original.visible ⊆ surviving.visible ++ resources)
    (typed : ScopedPorts.StackTyped signature tickets world stack input output) :
    ScopedPorts.PlanTyped signature world (scopeProviders survivingContext ++ outward) plan ∧
      Admission.OpenCloses stack.erase original surviving resources outward (plan.map ScopedExecution.CloseEntry.erase) ∧
      (planOwners (plan.map ScopedExecution.CloseEntry.erase)).Perm stack.erase.owners := by
  obtain ⟨planTyped, closes⟩ := realized.interfaces ((check_closing_iff closing).mp safe)
    originalScope survivingScope supported available typed
  exact ⟨planTyped, closes, realized.owner_accounting⟩

namespace Examples

/-- Overlapping effects are allowed when an intervening builtin retains the
callback's exact interpretation through disposal. -/
theorem overlapping_builtin :
    Closing [] (.cleanup [.cell 4] (.cell 4 .nil)) [.handler (.cell 4)] [] := by
  apply (check_closing_iff (front := []) (original := []) ?_).mp rfl
  exact .cleanup (fun _ member => by
    have same := List.mem_singleton.mp member
    exact ⟨some 4, .cell same, .cell same⟩) (.cell .nil)

/-- A previously exported callback cannot acquire a handler that is removed
during closing. -/
theorem exposed_rejected :
    ¬ Closing [.cell 4] (.cleanup [.cell 4] .nil) [.handler (.cell 4)] [] := by
  intro checked
  have safe := (closing_insert_iff (.cleanup [.cell 4] .nil) []).mp checked |>.2
  have rejected := check_complete safe
  contradiction

/-- A dormant callback is still checked against the suffix at which it will
be materialized; ignoring the saved branch would admit this case. -/
theorem dormant_rejected :
    ¬ Closing [.cell 4] (.live (.cleanup [.cell 4] .nil) .nil) [.handler (.cell 4)] [] := by
  intro checked
  have safe := (closing_insert_iff (.live (.cleanup [.cell 4] .nil) .nil) []).mp checked |>.2
  have rejected := check_complete safe
  contradiction

/-- A receiving builtin can also shield a callback in a dormant capture. -/
theorem dormant_builtin :
    Closing [] (.live (.cleanup [.cell 4] .nil) (.cell 4 .nil)) [.handler (.cell 4)] [] := by
  apply (check_closing_iff (front := []) (original := []) ?_).mp rfl
  exact .live (.cleanup (fun _ member => by
    have same := List.mem_singleton.mp member
    exact ⟨some 4, .cell same, .cell same⟩) .nil) (.cell .nil)

end Examples
end Ash.OneShot.SourceHandlerInterference

#print axioms Ash.OneShot.SourceHandlerInterference.route_insert_iff
#print axioms Ash.OneShot.SourceHandlerInterference.closing_insert_iff
#print axioms Ash.OneShot.SourceHandlerInterference.check_sound
#print axioms Ash.OneShot.SourceHandlerInterference.check_complete
#print axioms Ash.OneShot.SourceHandlerInterference.check_iff
#print axioms Ash.OneShot.SourceHandlerInterference.check_summary
#print axioms Ash.OneShot.SourceHandlerInterference.shielded_summary
#print axioms Ash.OneShot.SourceHandlerInterference.route_requirements
#print axioms Ash.OneShot.SourceHandlerInterference.exposed_bound
#print axioms Ash.OneShot.SourceHandlerInterference.check_closing_iff
#print axioms Ash.OneShot.SourceHandlerInterference.captured_row_separation
#print axioms Ash.OneShot.SourceHandlerInterference.realized_interfaces
#print axioms Ash.OneShot.SourceHandlerInterference.Examples.overlapping_builtin
#print axioms Ash.OneShot.SourceHandlerInterference.Examples.exposed_rejected
#print axioms Ash.OneShot.SourceHandlerInterference.Examples.dormant_rejected
#print axioms Ash.OneShot.SourceHandlerInterference.Examples.dormant_builtin
