import InitialCleanupRouteGap

/-! A bounded source-rule experiment on the existing Code syntax. Literal
resuming/discarding handlers and literal cleanup callbacks expose the missing
dependency without a runtime plan, a future-state premise, or a new bind.
The full hereditary source judgment and recursive captures are not replaced
by this fragment. Retain it only as evidence for their route annotation. -/
namespace Ash.OneShot.SourceCleanupRoutes
open Instantiation ScopedExpressions

inductive Entry where
  | handler : Effect → Bool → Entry
  | cleanup : List Effect → Entry
  deriving DecidableEq, Repr

abbrev Context := List Entry

/-- Keep the nearest source interpretation occurrence. Skipping a matching
handler is impossible, even if an equal effect occurs farther outside. -/
def select (requested : Effect) : Context → Option (Context × Bool)
  | [] => none
  | .handler effect dispose :: rest =>
      if requested = effect then some ([.handler effect dispose], dispose)
      else (select requested rest).map fun (captured, mode) => (.handler effect dispose :: captured, mode)
  | .cleanup requests :: rest =>
      (select requested rest).map fun (captured, mode) => (.cleanup requests :: captured, mode)

def handlers : Context → List Effect
  | [] => []
  | .handler effect _ :: rest => effect :: handlers rest
  | .cleanup _ :: rest => handlers rest

/-- Each callback can use an outside interpretation, but cannot depend on a
source handler in the suffix that this disposal will remove. The suffix is
relative to the callback's own registration point. -/
inductive Closing : Context → Prop where
  | nil : Closing []
  | handler (tail : Closing rest) : Closing (.handler effect dispose :: rest)
  | cleanup (outside : ∀ effect ∈ requests, effect ∉ handlers rest)
      (tail : Closing rest) : Closing (.cleanup requests :: rest)

def checkClosing : Context → Bool
  | [] => true
  | .handler _ _ :: rest => checkClosing rest
  | .cleanup requests :: rest =>
      requests.all (fun effect => !(handlers rest).contains effect) && checkClosing rest

theorem check_closing_iff : checkClosing context = true ↔ Closing context := by
  induction context with
  | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
  | cons entry rest ih => cases entry with
    | handler effect dispose => exact ⟨fun accepted => .handler (ih.mp accepted),
        fun accepted => by cases accepted with | handler tail => exact ih.mpr tail⟩
    | cleanup requests =>
        have split : checkClosing (.cleanup requests :: rest) = true ↔
            (∀ effect ∈ requests, effect ∉ handlers rest) ∧ Closing rest := by
          simp [checkClosing, ih]
        rw [split]
        exact ⟨fun ⟨outside, tail⟩ => .cleanup outside tail,
          fun accepted => by cases accepted with | cleanup outside tail => exact ⟨outside, tail⟩⟩

inductive Request : Context → Effect → Prop where
  | selected (found : select effect context = some (capture, dispose))
      (closing : dispose = true → Closing capture) : Request context effect

def checkRequest (context : Context) (effect : Effect) : Bool :=
  match select effect context with
  | none => false
  | some (capture, dispose) => !dispose || checkClosing capture

theorem check_request_iff : checkRequest context effect = true ↔ Request context effect := by
  cases found : select effect context with
  | none =>
      constructor
      · simp [checkRequest, found]
      · intro accepted
        cases accepted with
        | selected actual closing => rw [found] at actual; cases actual
  | some selected =>
      rcases selected with ⟨capture, dispose⟩
      cases dispose <;> simp only [checkRequest, found, Bool.not_false, Bool.not_true,
        Bool.true_or, Bool.false_or]
      · exact ⟨fun _ => .selected found (by intro impossible; cases impossible), fun _ => trivial⟩
      · constructor
        · exact fun accepted => .selected found (fun _ => check_closing_iff.mp accepted)
        · intro accepted
          cases accepted with
          | selected actual closing =>
              cases Option.some.inj (found.symm.trans actual)
              exact check_closing_iff.mpr (closing rfl)

def arms (dispose : Bool) : Clauses :=
  if dispose then .cons 0 1 9 (.discard 9) .nil
  else .cons 0 1 8 (.resume 8 .unit) .nil

/-- Effects can occur repeatedly. This annotation collects requests and does
not consume an effect or constrain how many times it is used. -/
inductive Callback : Code → List Effect → Prop where
  | unit : Callback .unit []
  | request : Callback (.perform effect 0 .unit) [effect]
  | bind (left : Callback a first) (right : Callback b second) :
      Callback (.bind parameter a b) (first ++ second)

/-- Syntax-directed route checking for the small diagnostic fragment. Its
callback dependency is extracted from the literal body, not supplied by the
caller. Ordinary value/effect typing remains the existing source judgment. -/
inductive Source : Context → Code → Prop where
  | unit : Source context .unit
  | request (route : Request context effect) : Source context (.perform effect 0 .unit)
  | handler (body : Source (.handler effect dispose :: context) code) :
      Source context (.handle effect code (arms dispose))
  | cleanup (callback : Callback action requests) (body : Source (.cleanup requests :: context) code) :
      Source context (.cleanup (.lambda parameter action) code)

/-- Multiplicity and order within a callback's effect collection do not
affect closing. The order of interpretation scopes remains significant. -/
theorem closing_membership_congr
    (same : ∀ effect, effect ∈ left ↔ effect ∈ right) :
    Closing (.cleanup left :: context) ↔ Closing (.cleanup right :: context) := by
  constructor
  · intro admitted
    cases admitted with
    | cleanup outside tail => exact .cleanup (fun effect member => outside effect ((same effect).mpr member)) tail
  · intro admitted
    cases admitted with
    | cleanup outside tail => exact .cleanup (fun effect member => outside effect ((same effect).mp member)) tail

theorem closing_duplicate :
    Closing (.cleanup (effect :: effect :: rest) :: context) ↔
      Closing (.cleanup (effect :: rest) :: context) :=
  closing_membership_congr (by intro actual; simp)

open ScopedExecution

/-- Realization of the bounded handler/cleanup fragment. Callback access is
empty in this fragment; resource-bearing callbacks and dormant captures are
separate integration obligations. The plan is constructed by these rules. -/
inductive Realizes : Context → Stack → List CloseEntry → List Instance → Prop where
  | nil : Realizes [] .nil [] []
  | handler (tail : Realizes rest stack plan requests) :
      Realizes (.handler (freezeEffect handler.effectInst) dispose :: rest)
        (.push (.handler handler) stack) plan requests
  | cleanup (access : Syntax.resourceDependencies action.action.dependencies = [])
      (tail : Realizes rest stack plan requests) :
      Realizes (.cleanup (action.requests.map freezeEffect) :: rest)
        (.push (.armed action) stack) (.invoke action :: plan) (action.requests ++ requests)

theorem Realizes.built (realized : Realizes context stack plan requests) : makePlan stack = some plan := by
  induction realized with
  | nil => rfl
  | handler tail ih => exact ih
  | cleanup access tail ih => simp [makePlan, ih]

theorem Realizes.unresolved (realized : Realizes context stack plan requests)
    (outside : freezeEffect requested ∉ handlers context) : stack.erase.resolve requested = none := by
  induction realized with
  | nil => rfl
  | @handler rest stack plan requests dispose handler tail ih =>
      have missed : requested ≠ handler.effectInst := by
        intro same
        exact outside (by simp [handlers, same])
      have restOutside : freezeEffect requested ∉ handlers rest := fun member => outside (by simp [handlers, member])
      simpa [Stack.erase, ExecFrame.erase, HandlerData.erase, Control.resolve, Frame.resolve, missed]
        using ih restOutside
  | cleanup access tail ih => exact ih outside

theorem Realizes.plan_unresolved (realized : Realizes context stack plan requests) :
    (planControl (plan.map CloseEntry.erase)).resolve requested = none := by
  induction realized with
  | nil => rfl
  | handler tail ih => exact ih
  | cleanup access tail ih => exact ih

theorem Realizes.required_effects (realized : Realizes context stack plan requests) :
    ClosingRequirements.requiredEffects plan = requests ∧ ScopedPorts.planProvides plan = [] := by
  induction realized with
  | nil => exact ⟨rfl, rfl⟩
  | handler tail ih => exact ih
  | cleanup access tail ih =>
      simp [ClosingRequirements.requiredEffects, ClosingRequirements.unmet, ih.1, ih.2,
        ScopedPorts.planProvides]

/-- Structural source dependencies supply the existing parametric closing
judgment. Outside handlers remain abstract and are not identified by labels. -/
theorem Realizes.open_closing (realized : Realizes context stack plan requests)
    (admitted : Closing context) (bound : requests ⊆ outward) :
    Admission.OpenCloses stack.erase .nil .nil resources outward (plan.map CloseEntry.erase) := by
  induction realized with
  | nil => exact .nil _ _ _ _
  | handler tail ih =>
      cases admitted with
      | handler admitted => exact .handler _ _ _ _ _ _ _ _ _ rfl (ih admitted bound)
  | @cleanup rest stack plan requests action access tail ih =>
      cases admitted with
      | cleanup outside admitted =>
          obtain ⟨headBound, tailBound⟩ := List.append_subset.mp bound
          have routes : Admission.OpenRequests stack.erase (planControl (plan.map CloseEntry.erase))
              outward action.requests := by
            have each : ∀ effect ∈ action.requests,
                stack.erase.resolve effect = none ∧
                (planControl (plan.map CloseEntry.erase)).resolve effect = none ∧ effect ∈ outward := by
              intro effect member
              exact ⟨tail.unresolved (outside _ (List.mem_map.mpr ⟨effect, member, rfl⟩)),
                tail.plan_unresolved, headBound member⟩
            generalize requestsEq : action.requests = requestedList at each ⊢
            clear requestsEq
            induction requestedList with
            | nil => exact .nil
            | cons effect rest ih =>
                obtain ⟨before, after, included⟩ := each effect List.mem_cons_self
                exact .outside effect rest before after included
                  (ih (fun next member => each next (List.mem_cons_of_mem _ member)))
          exact .armed _ _ _ _ _ _ _ _ rfl rfl (by simp [ExecFrame.erase, ActionData.erase, access])
            (by simpa only [append_nil, ExecFrame.erase, ActionData.erase] using routes) (ih admitted tailBound)

theorem Realizes.closing_interfaces (realized : Realizes context stack plan requests)
    (admitted : Closing context) (bound : requests ⊆ outward)
    (contents : ScopedPorts.PlanContentsTyped signature tickets world plan) :
    makePlan stack = some plan ∧ ScopedPorts.PlanTyped signature world outward plan ∧
      Admission.OpenCloses stack.erase .nil .nil [] outward (plan.map CloseEntry.erase) :=
  ⟨realized.built, ClosingRequirements.requirements_supply_plan contents
    (realized.required_effects.1.symm ▸ bound), realized.open_closing admitted bound⟩

theorem Realizes.pending_empty (realized : Realizes context stack plan requests) : stack.erase.pending = [] := by
  induction realized with
  | nil => rfl
  | handler tail ih => exact ih
  | cleanup access tail ih => exact ih

/-- The bounded source rule reaches the existing certificate interface.
Callback type evidence is reused from the ordinary retained contents. -/
def Realizes.certificate (realized : Realizes context stack plan requests)
    (admitted : Closing context) (bound : requests ⊆ record.annotation.closeEffects)
    (contents : ScopedPorts.PlanContentsTyped signature tickets world plan) :
    DeclaredClosingInvariant.Certificate signature world record stack :=
  ⟨plan, realized.built, ClosingRequirements.requirements_supply_plan contents
    (realized.required_effects.1.symm ▸ bound), realized.open_closing admitted bound,
    realized.pending_empty.symm ▸ InternalUses.nil⟩

open InitialCleanupRouteGap (inner outer callback request program)

def e := freezeEffect outer
def f := freezeEffect inner
def badContext : Context := [.cleanup [f], .handler f false, .handler e true]
def survivingContext : Context := [.cleanup [f], .handler e true, .handler f false]
def resumingContext : Context := [.cleanup [f], .handler f false, .handler e false]

theorem removed_handler_rejected : ¬ Request badContext e := by
  intro accepted
  have failed : checkRequest badContext e = false := by decide
  have checked := check_request_iff.mpr accepted
  rw [failed] at checked
  cases checked

theorem surviving_handler_accepted : Request survivingContext e :=
  check_request_iff.mp (by decide)

theorem resume_only_accepted : Request resumingContext e :=
  check_request_iff.mp (by decide)

/-- An outside copy of the same effect cannot replace the nearer handler
selected at cleanup registration. No occurrence counters are needed. -/
theorem outside_copy_rejected :
    ¬ Request [.cleanup [f], .handler f false, .handler e true, .handler f false] e := by
  intro admitted
  have failed : checkRequest [.cleanup [f], .handler f false, .handler e true, .handler f false] e = false := by decide
  have checked := check_request_iff.mpr admitted
  rw [failed] at checked
  cases checked

theorem same_handler_multiset : (handlers badContext).Perm (handlers survivingContext) :=
  .swap _ _ []

/-- Moving the callback's handler outside the disposing boundary makes its
dependency survive; the effect name and callback body remain the same. -/
theorem surviving_program : Source []
    (.handle f (.handle e (.cleanup callback request) (arms true)) (arms false)) :=
  .handler (.handler (.cleanup .request (.request surviving_handler_accepted)))

theorem resuming_program : Source []
    (.handle e (.handle f (.cleanup callback request) (arms false)) (arms false)) :=
  .handler (.handler (.cleanup .request (.request resume_only_accepted)))

theorem repeated_effect_program : Source []
    (.handle f (.handle e
      (.cleanup (.lambda 0 (.bind 2 (.perform f 0 .unit) (.perform f 0 .unit))) request)
      (arms true)) (arms false)) :=
  .handler (.handler (.cleanup (.bind .request .request) (.request (check_request_iff.mp (by decide)))))

theorem source_handler (source : Source context (.handle effect code (arms dispose))) :
    Source (.handler effect dispose :: context) code := by
  generalize same : arms dispose = clauses at source
  cases source with
  | handler body =>
      rename_i actual
      have modes : actual = dispose := by
        cases actual <;> cases dispose <;> simp_all [arms]
      subst actual
      exact body

theorem initial_program_rejected : ¬ Source [] program := by
  intro admitted
  have outerBody := source_handler (dispose := true) admitted
  have innerBody := source_handler (dispose := false) outerBody
  cases innerBody with
  | cleanup callback body =>
      cases callback with
      | request =>
          cases body with
          | request route => exact removed_handler_rejected route

def survivingCapture : Stack :=
  .push (.armed InitialCleanupRouteGap.action) (.push (.handler InitialCleanupRouteGap.outerHandler) .nil)

/-- The accepted arrangement constructs the same certificate that the bad
arrangement provably lacks. The caller provides the surviving inner effect. -/
theorem surviving_certificate (record : CoherentSourceTypes.Owners.Record)
    (bound : [inner] ⊆ record.annotation.closeEffects) :
    Nonempty (DeclaredClosingInvariant.Certificate InitialCleanupRouteGap.operations.ports [] record survivingCapture) := by
  have realized : Realizes [.cleanup [f], .handler e true] survivingCapture
      [.invoke InitialCleanupRouteGap.action] [inner] :=
    .cleanup (action := InitialCleanupRouteGap.action) rfl
      (.handler (handler := InitialCleanupRouteGap.outerHandler) .nil)
  have closing : Closing [.cleanup [f], .handler e true] :=
    check_closing_iff.mp (by decide)
  have callbackTyped : ScopedPorts.Typed InitialCleanupRouteGap.operations.ports [] ScopedPorts.TypeEnv.empty
      .none [] InitialCleanupRouteGap.action.action
      (.function .unit .unit InitialCleanupRouteGap.action.requests) :=
    .lambda (.perform (CoherentSourceTypes.port_lookup InitialCleanupRouteGap.inner_known)
      List.mem_cons_self .unit (by simp [ScopedPorts.InWorld, ScopedPorts.Port.resources]))
      (by simp [ScopedPorts.InWorld, ScopedPorts.Port.resources, InitialCleanupRouteGap.action,
        inner, InitialCleanupRouteGap.inner, Instance.resources])
  exact ⟨realized.certificate closing bound
    (ScopedPorts.PlanContentsTyped.invoke (tickets := fun _ => none) callbackTyped .nil)⟩

end Ash.OneShot.SourceCleanupRoutes

#print axioms Ash.OneShot.SourceCleanupRoutes.check_closing_iff
#print axioms Ash.OneShot.SourceCleanupRoutes.check_request_iff
#print axioms Ash.OneShot.SourceCleanupRoutes.removed_handler_rejected
#print axioms Ash.OneShot.SourceCleanupRoutes.surviving_handler_accepted
#print axioms Ash.OneShot.SourceCleanupRoutes.resume_only_accepted
#print axioms Ash.OneShot.SourceCleanupRoutes.surviving_program
#print axioms Ash.OneShot.SourceCleanupRoutes.resuming_program
#print axioms Ash.OneShot.SourceCleanupRoutes.closing_membership_congr
#print axioms Ash.OneShot.SourceCleanupRoutes.closing_duplicate
#print axioms Ash.OneShot.SourceCleanupRoutes.repeated_effect_program
#print axioms Ash.OneShot.SourceCleanupRoutes.Realizes.built
#print axioms Ash.OneShot.SourceCleanupRoutes.Realizes.unresolved
#print axioms Ash.OneShot.SourceCleanupRoutes.Realizes.plan_unresolved
#print axioms Ash.OneShot.SourceCleanupRoutes.Realizes.required_effects
#print axioms Ash.OneShot.SourceCleanupRoutes.Realizes.open_closing
#print axioms Ash.OneShot.SourceCleanupRoutes.Realizes.closing_interfaces
#print axioms Ash.OneShot.SourceCleanupRoutes.source_handler
#print axioms Ash.OneShot.SourceCleanupRoutes.initial_program_rejected
#print axioms Ash.OneShot.SourceCleanupRoutes.outside_copy_rejected
#print axioms Ash.OneShot.SourceCleanupRoutes.same_handler_multiset
#print axioms Ash.OneShot.SourceCleanupRoutes.Realizes.pending_empty
#print axioms Ash.OneShot.SourceCleanupRoutes.Realizes.certificate
#print axioms Ash.OneShot.SourceCleanupRoutes.surviving_certificate
