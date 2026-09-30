import ScopedPortCompletion

/-!
Compute the least outward effect row of an ordered disposal plan. Structural
induction covers arbitrary nested captures through makePlan. This checks the
effect component of closing readiness; it does not grant disposal permission,
prove exact interpretation agreement, or admit future source captures.
-/

namespace Ash.OneShot.ClosingRequirements
open Syntax Instantiation ScopedExpressions ScopedExecution ScopedPorts

/-- Requests not supplied by the remaining disposal suffix. Membership, rather
    than list order or multiplicity, determines the outward effect bound. -/
def unmet (requests provided : List Instance) : List Instance :=
  requests.filter (fun request => !(provided.contains request))

@[simp] theorem mem_unmet : request ∈ unmet requests provided ↔
    request ∈ requests ∧ request ∉ provided := by
  simp [unmet]

theorem unmet_subset_iff : unmet requests provided ⊆ closing ↔
    requests ⊆ provided ++ closing := by
  constructor
  · intro bound request member
    by_cases available : request ∈ provided
    · exact List.mem_append_left _ available
    · exact List.mem_append_right _ (bound (mem_unmet.mpr ⟨member, available⟩))
  · intro bound request member
    obtain ⟨requested, unavailable⟩ := mem_unmet.mp member
    exact (List.mem_append.mp (bound requested)).resolve_left unavailable

/-- Only providers still present when a callback runs can satisfy its row. -/
def requiredEffects : List CloseEntry → List Instance
  | [] => []
  | .release _ _ :: tail | .retire _ :: tail => requiredEffects tail
  | .invoke action :: tail => unmet action.requests (planProvides tail) ++ requiredEffects tail

theorem plan_typed_requires (typed : PlanTyped signature world closing plan) :
    requiredEffects plan ⊆ closing := by
  induction typed with
  | nil => exact List.nil_subset _
  | release rest ih | retire rest ih => exact ih
  | invoke callable effects rest ih =>
      exact List.append_subset.mpr ⟨unmet_subset_iff.mpr effects, ih⟩

/-- Callback typing comes from retained contents; all outward row obligations
    are discharged by one finite subset test. -/
theorem requirements_supply_plan
    (contents : PlanContentsTyped signature tickets world plan)
    (bound : requiredEffects plan ⊆ closing) : PlanTyped signature world closing plan := by
  induction contents with
  | nil => exact .nil
  | release rest ih => exact .release (ih bound)
  | retire known rest ih => exact .retire (ih bound)
  | invoke callable rest ih =>
      obtain ⟨requests, remaining⟩ := List.append_subset.mp bound
      exact .invoke callable (unmet_subset_iff.mp requests) (ih remaining)

theorem plan_typed_iff_requirements
    (contents : PlanContentsTyped signature tickets world plan) :
    PlanTyped signature world closing plan ↔ requiredEffects plan ⊆ closing :=
  ⟨plan_typed_requires, requirements_supply_plan contents⟩

theorem least_plan_row (contents : PlanContentsTyped signature tickets world plan) :
    PlanTyped signature world (requiredEffects plan) plan ∧
      ∀ closing, PlanTyped signature world closing plan → requiredEffects plan ⊆ closing :=
  ⟨requirements_supply_plan contents (List.Subset.refl _), fun _ => plan_typed_requires⟩

/-- Ordered composition of minimal rows. Providers in the suffix discharge
    front requirements; earlier providers cannot discharge suffix requirements. -/
theorem mem_required_append (front tail : List CloseEntry) :
    request ∈ requiredEffects (front ++ tail) ↔
      (request ∈ requiredEffects front ∧ request ∉ planProvides tail) ∨
        request ∈ requiredEffects tail := by
  induction front with
  | nil => simp [requiredEffects]
  | cons entry rest ih => cases entry with
      | release | retire => simpa only [List.cons_append, requiredEffects] using ih
      | invoke action =>
          simp only [List.cons_append, requiredEffects, List.mem_append, mem_unmet,
            plan_provides_append, ih]
          grind only

/-- Splitting preserves order: the front may use providers retained by the
    suffix, while the suffix must close using the outward row alone. -/
theorem plan_typed_decompose (front : List CloseEntry)
    (typed : PlanTyped signature world closing (front ++ tail)) :
    PlanTyped signature world (planProvides tail ++ closing) front ∧
      PlanTyped signature world closing tail := by
  induction front with
  | nil => exact ⟨.nil, typed⟩
  | cons entry rest ih =>
      cases entry with
      | release identity payload => cases typed with
          | release remaining =>
              obtain ⟨inside, outside⟩ := ih remaining
              exact ⟨.release inside, outside⟩
      | retire owner => cases typed with
          | retire remaining =>
              obtain ⟨inside, outside⟩ := ih remaining
              exact ⟨.retire inside, outside⟩
      | invoke action => cases typed with
          | invoke callable effects remaining =>
              obtain ⟨inside, outside⟩ := ih remaining
              exact ⟨.invoke callable (by
                change action.requests ⊆ planProvides (rest ++ tail) ++ closing at effects
                simpa only [plan_provides_append, List.append_assoc] using effects) inside, outside⟩

/-- Converse to close_ready_constructs_plan, proved by induction on the actual
    retained stack. In the live case both saved capture and outside suffix use
    their induction hypotheses; there is no bound on their nesting depth. -/
theorem generated_plan_supplies_readiness (stack : Stack)
    (built : makePlan stack = some plan) (typed : PlanTyped signature world closing plan) :
    CloseReady signature world closing stack := by
  induction stack generalizing plan closing with
  | nil => exact .nil
  | push frame tail ih => cases frame with
      | plain => exact .plain (ih built typed)
      | handler => exact .handler (ih built typed)
      | cell =>
          cases tailPlan : makePlan tail with
          | none => simp [makePlan, tailPlan] at built
          | some rest =>
              simp only [makePlan, tailPlan, Option.some.injEq] at built
              subst plan
              cases typed with | release remaining => exact .cell (ih tailPlan remaining)
      | armed =>
          cases tailPlan : makePlan tail with
          | none => simp [makePlan, tailPlan] at built
          | some rest =>
              simp only [makePlan, tailPlan, Option.some.injEq] at built
              subst plan
              cases typed with
              | invoke callable effects remaining =>
                  exact .armed callable (by rw [← make_plan_provides _ tailPlan]; exact effects)
                    (ih tailPlan remaining)
      | running | unwinding | closing | retiring => simp [makePlan] at built
  | live owner input answer capture scope tail ihCapture ihTail =>
      cases capturePlan : makePlan capture <;> cases tailPlan : makePlan tail <;>
        simp [makePlan, capturePlan, tailPlan] at built
      case some.some inside outside =>
        subst plan
        obtain ⟨innerTyped, outerTyped⟩ := plan_typed_decompose inside typed
        cases outerTyped with
        | retire remaining =>
            exact .live (ihCapture capturePlan (by
              simpa only [planProvides, make_plan_provides _ tailPlan] using innerTyped))
              (ihTail tailPlan remaining)
  | spent owner answer scope tail ih => exact .spent (ih built typed)

/-- An executable effect check for a concrete stack. Failed planning includes
    protected running, closing, or retiring frames at any captured depth. -/
def checkClosingEffects (stack : Stack) (closing : List Instance) : Bool :=
  match makePlan stack with
  | none => false
  | some plan => (requiredEffects plan).all (fun request => closing.contains request)

/-- Exact for the effect-readiness judgment when retained contents are typed.
    It checks neither resource access nor exact handler selection. -/
theorem check_closing_effects_iff
    (contents : StackTyped signature tickets world stack input result) :
    checkClosingEffects stack closing = true ↔ CloseReady signature world closing stack := by
  constructor
  · intro accepted
    cases built : makePlan stack with
    | none => simp [checkClosingEffects, built] at accepted
    | some plan =>
        have bound : requiredEffects plan ⊆ closing := by
          simp only [checkClosingEffects, built, List.all_eq_true, List.contains_eq_mem,
            decide_eq_true_eq] at accepted
          exact fun _ member => accepted _ member
        exact generated_plan_supplies_readiness stack built
          (requirements_supply_plan (make_plan_retains_types contents built) bound)
  · intro ready
    obtain ⟨plan, built, typed⟩ := close_ready_constructs_plan ready
    simp only [checkClosingEffects, built, List.all_eq_true, List.contains_eq_mem,
      decide_eq_true_eq]
    exact fun _ member => plan_typed_requires typed member

namespace Examples
open ScopedPorts.CompletionExamples

theorem callback_before_release : checkClosingEffects captured [] = true := by decide

/-- The same frames in the opposite order no longer supply the callback's
    request: its resource has already been released when it runs. -/
theorem release_before_callback :
    checkClosingEffects (.push (.cell 4 17 .none .unit) (.push (.armed action) .nil)) [] = false := by
  decide

theorem nested_capture :
    checkClosingEffects (.live 3 .unit .unit captured .none .nil) [] = true := by decide

theorem nested_running_rejected : checkClosingEffects
    (.live 3 .unit .unit (.push (.running action .unit
      ⟨trivial, rfl, by intro dependency member; cases member⟩) .nil) .none .nil) [] = false := by decide

end Examples

end Ash.OneShot.ClosingRequirements

#print axioms Ash.OneShot.ClosingRequirements.mem_unmet
#print axioms Ash.OneShot.ClosingRequirements.unmet_subset_iff
#print axioms Ash.OneShot.ClosingRequirements.plan_typed_requires
#print axioms Ash.OneShot.ClosingRequirements.requirements_supply_plan
#print axioms Ash.OneShot.ClosingRequirements.plan_typed_iff_requirements
#print axioms Ash.OneShot.ClosingRequirements.least_plan_row
#print axioms Ash.OneShot.ClosingRequirements.mem_required_append
#print axioms Ash.OneShot.ClosingRequirements.plan_typed_decompose
#print axioms Ash.OneShot.ClosingRequirements.generated_plan_supplies_readiness
#print axioms Ash.OneShot.ClosingRequirements.check_closing_effects_iff
#print axioms Ash.OneShot.ClosingRequirements.Examples.callback_before_release
#print axioms Ash.OneShot.ClosingRequirements.Examples.release_before_callback
#print axioms Ash.OneShot.ClosingRequirements.Examples.nested_capture
#print axioms Ash.OneShot.ClosingRequirements.Examples.nested_running_rejected
