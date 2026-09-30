import SourceDependencyReduction
import SourceRecursiveRoutes
import SourceHandlerInterference

/-! Executable local capture guards for hereditary dependency scopes. The
closing checker decides the existing recursive structural judgment. Handler
selection retains the same clause table and dependency families as the source
annotation. This does not yet check whole source computations or clause bodies. -/
namespace Ash.OneShot.SourceDependencyCapture
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies ClauseDependencies)
open SourceResourceRoutes (Entry Route)
open SourceRecursiveRoutes (Shape Closing)

/-- Distinguish an exported request (some none) from failure (none). -/
def route (outward : List Instance) : SourceResourceRoutes.Context → Instance → Option (Option Nat)
  | [], requested => if requested ∈ outward then some none else none
  | .handler effect :: rest, requested => if requested = effect then none else route outward rest requested
  | .cell identity :: rest, requested => if requested = .cell identity then some (some identity) else route outward rest requested
  | .cleanup _ :: rest, requested => route outward rest requested

theorem route_iff : route outward context requested = some target ↔ Route outward context requested target := by
  induction context with
  | nil =>
      by_cases included : requested ∈ outward
      · simp only [route, if_pos included, Option.some.injEq]
        exact ⟨fun same => same ▸ .outside included, fun accepted => by cases accepted; rfl⟩
      · constructor
        · simp [route, included]
        · intro accepted; cases accepted with | outside member => exact False.elim (included member)
  | cons entry rest ih => cases entry with
      | handler effect =>
          by_cases same : requested = effect
          · constructor
            · simp [route, same]
            · intro accepted; cases accepted with | handler different next => exact False.elim (different same)
          · constructor
            · intro checked; exact .handler same (ih.mp (by simpa only [route, if_neg same] using checked))
            · intro accepted; cases accepted with | handler different next => simpa only [route, if_neg same] using ih.mpr next
      | cell identity =>
          by_cases same : requested = .cell identity
          · simp only [route, if_pos same, Option.some.injEq]
            constructor
            · intro targetSame; exact targetSame ▸ .cell same
            · intro accepted; cases accepted with
              | cell found => rfl
              | cellMiss different next => exact False.elim (different same)
          · constructor
            · intro checked; exact .cellMiss same (ih.mp (by simpa only [route, if_neg same] using checked))
            · intro accepted; cases accepted with
              | cell found => exact False.elim (same found)
              | cellMiss different next => simpa only [route, if_neg same] using ih.mpr next
      | cleanup needs =>
          exact ⟨fun checked => .cleanup (ih.mp checked), fun accepted => by cases accepted with | cleanup next => exact ih.mpr next⟩

def sameRoute (outward : List Instance) (original surviving : SourceResourceRoutes.Context) (effect : Instance) : Bool :=
  match route outward original effect, route outward surviving effect with
  | some first, some second => decide (first = second)
  | _, _ => false

theorem same_route_iff : sameRoute outward original surviving effect = true ↔
    ∃ target, Route outward original effect target ∧ Route outward surviving effect target := by
  simp only [← route_iff]
  cases first : route outward original effect <;> cases second : route outward surviving effect <;>
    simp [sameRoute, first, second, eq_comm]

def checkClosing (outward : List Instance) : Shape → SourceResourceRoutes.Context → SourceResourceRoutes.Context → Bool
  | .nil, _, _ => true
  | .plain rest, original, surviving | .handler _ rest, original, surviving |
      .cell _ rest, original, surviving | .spent rest, original, surviving => checkClosing outward rest original surviving
  | .cleanup needs rest, original, surviving =>
      needs.all (sameRoute outward (rest.normal ++ original) (rest.closing ++ surviving)) &&
        checkClosing outward rest original surviving
  | .live captured rest, original, surviving =>
      checkClosing outward captured (rest.normal ++ original) (rest.closing ++ surviving) &&
        checkClosing outward rest original surviving

theorem check_closing_iff : checkClosing outward shape original surviving = true ↔ Closing outward shape original surviving := by
  induction shape generalizing original surviving with
  | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
  | plain rest ih => exact ⟨fun checked => .plain (ih.mp checked), fun accepted => by cases accepted with | plain next => exact ih.mpr next⟩
  | handler effect rest ih => exact ⟨fun checked => .handler (ih.mp checked), fun accepted => by cases accepted with | handler next => exact ih.mpr next⟩
  | cell identity rest ih => exact ⟨fun checked => .cell (ih.mp checked), fun accepted => by cases accepted with | cell next => exact ih.mpr next⟩
  | spent rest ih => exact ⟨fun checked => .spent (ih.mp checked), fun accepted => by cases accepted with | spent next => exact ih.mpr next⟩
  | cleanup needs rest ih =>
      simp only [checkClosing, Bool.and_eq_true, List.all_eq_true, same_route_iff, ih]
      exact ⟨fun ⟨routes, tail⟩ => .cleanup routes tail,
        fun accepted => by cases accepted with | cleanup routes tail => exact ⟨routes, tail⟩⟩
  | live captured rest ihCaptured ihRest =>
      simp only [checkClosing, Bool.and_eq_true, ihCaptured, ihRest]
      exact ⟨fun ⟨inside, outside⟩ => .live inside outside,
        fun accepted => by cases accepted with | live inside outside => exact ⟨inside, outside⟩⟩

/-- Exact factorization of the existing closing checker after insertion of
a handler in the original context. The extra finite check follows callback
positions, including dormant captures, and preserves builtin shielding. -/
theorem check_closing_handler_insert :
    checkClosing outward shape (front ++ .handler effect :: original) surviving =
      (checkClosing outward shape (front ++ original) surviving &&
        SourceHandlerInterference.check effect shape front) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, check_closing_iff, SourceHandlerInterference.check_iff]
  exact SourceHandlerInterference.closing_insert_iff shape front

theorem checked_closing_handler_insert
    (checked : checkClosing outward shape (front ++ original) surviving = true) :
    checkClosing outward shape (front ++ .handler effect :: original) surviving =
      SourceHandlerInterference.check effect shape front := by
  rw [check_closing_handler_insert, checked, Bool.true_and]

/-- Pending code and callback bodies remain in the scope annotation. A
protected marker represents running completion, separately from armed cleanup.
Dormant captures retain their complete recursive scope. -/
inductive Scope where
  | nil
  | plain : Dependencies → Scope → Scope
  | handler : Instance → List (Nat × ClauseContract) → ClauseDependencies → Scope → Scope
  | cell : Nat → Scope → Scope
  | cleanup : List Instance → Dependencies → Scope → Scope
  | running : Scope → Scope
  | live : Nat → Scope → Scope → Scope
  | spent : Nat → Scope → Scope

def Scope.shape : Scope → Shape
  | .nil => .nil
  | .plain _ rest | .running rest => .plain rest.shape
  | .handler effect _ _ rest => .handler effect rest.shape
  | .cell identity rest => .cell identity rest.shape
  | .cleanup needs _ rest => .cleanup needs rest.shape
  | .live _ captured rest => .live captured.shape rest.shape
  | .spent _ rest => .spent rest.shape

def Scope.held : Scope → Bool
  | .nil => false
  | .plain _ rest | .handler _ _ _ rest | .cell _ rest | .cleanup _ _ rest | .spent _ rest => rest.held
  | .running _ => true
  | .live _ captured rest => captured.held || rest.held

def lookupDependencies (operation : Nat) : ClauseDependencies → Option (Option (Nat → Dependencies) × Option (Nat → Dependencies))
  | [] => none
  | (key, modes) :: rest => if operation = key then some modes else lookupDependencies operation rest

def modeDependencies (held : Bool) (modes : Option (Nat → Dependencies) × Option (Nat → Dependencies)) : Option (Nat → Dependencies) :=
  if held then modes.2 else modes.1

inductive Selection where
  | builtin : Nat → Selection
  | handler : Scope → Scope → ClauseContract →
      (Option (Nat → Dependencies) × Option (Nat → Dependencies)) → Selection

def Selection.prepend (frame : Scope → Scope) : Selection → Selection
  | .builtin identity => .builtin identity
  | .handler capture tail contract modes => .handler (frame capture) tail contract modes

/-- Exact lookup stops at a matching builtin or source handler. A missing
operation or annotation on that nearest handler cannot fall through. -/
def select (effect : Instance) (operation : Nat) : Scope → Option Selection
  | .nil => none
  | .handler requested table dependencies rest =>
      if effect = requested then
        match lookup operation table, lookupDependencies operation dependencies with
        | some contract, some modes => some (.handler (.handler requested table dependencies .nil) rest contract modes)
        | _, _ => none
      else (select effect operation rest).map (Selection.prepend (.handler requested table dependencies))
  | .cell identity rest =>
      if effect = .cell identity then some (.builtin identity)
      else (select effect operation rest).map (Selection.prepend (.cell identity))
  | .plain dependencies rest => (select effect operation rest).map (Selection.prepend (.plain dependencies))
  | .cleanup needs callback rest => (select effect operation rest).map (Selection.prepend (.cleanup needs callback))
  | .running rest => (select effect operation rest).map (Selection.prepend .running)
  | .live owner captured rest => (select effect operation rest).map (Selection.prepend (.live owner captured))
  | .spent owner rest => (select effect operation rest).map (Selection.prepend (.spent owner))

/-- This is only the local capture guard. Its selected clause family is
returned for subsequent source checking, not assumed to execute safely. -/
inductive CaptureGuard (outward : List Instance) (scope : Scope) (effect : Instance) (operation : Nat) : Prop where
  | builtin (found : select effect operation scope = some (.builtin identity)) : CaptureGuard outward scope effect operation
  | handler (found : select effect operation scope = some (.handler capture tail contract modes))
      (permission : modeCheck contract.dispose capture.held = true)
      (row : contract.row capture.held = some footprint)
      (body : modeDependencies capture.held modes = some family)
      (closing : contract.dispose = true → Closing outward capture.shape [] []) : CaptureGuard outward scope effect operation

def checkCapture (outward : List Instance) (scope : Scope) (effect : Instance) (operation : Nat) : Bool :=
  match select effect operation scope with
  | none => false
  | some (.builtin _) => true
  | some (.handler capture _ contract modes) =>
      modeCheck contract.dispose capture.held && (contract.row capture.held).isSome &&
        (modeDependencies capture.held modes).isSome && (!contract.dispose || checkClosing outward capture.shape [] [])

theorem check_capture_iff : checkCapture outward scope effect operation = true ↔ CaptureGuard outward scope effect operation := by
  cases found : select effect operation scope with
  | none =>
      constructor
      · simp [checkCapture, found]
      · intro accepted
        cases accepted with
        | builtin actual | handler actual => rw [found] at actual; cases actual
  | some selected => cases selected with
      | builtin identity => exact ⟨fun _ => .builtin found, fun _ => by simp [checkCapture, found]⟩
      | handler capture tail contract modes =>
          constructor
          · intro checked
            simp only [checkCapture, found, Bool.and_eq_true] at checked
            rcases checked with ⟨⟨⟨permission, rowPresent⟩, bodyPresent⟩, closes⟩
            cases row : contract.row capture.held with
            | none => simp [row] at rowPresent
            | some footprint => cases body : modeDependencies capture.held modes with
                | none => simp [body] at bodyPresent
                | some family =>
                    exact .handler found permission row body (fun disposes =>
                      check_closing_iff.mp (by simpa only [disposes, Bool.not_true, Bool.false_or] using closes))
          · intro accepted
            cases accepted with
            | builtin actual => rw [found] at actual; cases Option.some.inj actual
            | handler actual permission row body closing =>
                cases Option.some.inj (found.symm.trans actual)
                have closes : (!contract.dispose || checkClosing outward capture.shape [] []) = true := by
                  cases disposes : contract.dispose with
                  | false => rfl
                  | true => exact check_closing_iff.mpr (closing disposes)
                simp only [checkCapture, found, permission, row, body, Option.isSome_some, Bool.true_and, closes]

/-- Enlarging the outward interface preserves the exact selected target. -/
theorem route_outward_weaken (checked : Route outward context requested target)
    (larger : outward ⊆ next) : Route next context requested target := by
  induction checked with
  | outside included => exact .outside (larger included)
  | cell same => exact .cell same
  | cellMiss different tail ih => exact .cellMiss different ih
  | handler different tail ih => exact .handler different ih
  | cleanup tail ih => exact .cleanup ih

theorem closing_outward_weaken (checked : Closing outward shape original surviving)
    (larger : outward ⊆ next) : Closing next shape original surviving := by
  induction checked with
  | nil => exact .nil
  | plain tail ih => exact .plain ih
  | handler tail ih => exact .handler ih
  | cell tail ih => exact .cell ih
  | spent tail ih => exact .spent ih
  | live inside outside ihInside ihOutside => exact .live ihInside ihOutside
  | cleanup routes tail ih =>
      apply Closing.cleanup _ ih
      intro effect included
      obtain ⟨target, original, surviving⟩ := routes effect included
      exact ⟨target, route_outward_weaken original larger, route_outward_weaken surviving larger⟩

theorem check_capture_outward_weaken (checked : checkCapture outward scope effect operation = true)
    (larger : outward ⊆ next) : checkCapture next scope effect operation = true := by
  apply check_capture_iff.mpr
  cases check_capture_iff.mp checked with
  | builtin found => exact .builtin found
  | handler found permission row body closing =>
      exact .handler found permission row body (fun disposes => closing_outward_weaken (closing disposes) larger)

/-- Extract the closing judgment at the exact selected capture. The old
physical protection flag stays independent of the dependency route check. -/
theorem disposing_capture
    (checked : checkCapture outward scope effect operation = true)
    (found : select effect operation scope = some (.handler capture tail contract modes))
    (disposes : contract.dispose = true) :
    capture.held = false ∧ Closing outward capture.shape [] [] ∧
      ∃ footprint family, contract.row false = some footprint ∧ modeDependencies false modes = some family := by
  cases check_capture_iff.mp checked with
  | builtin actual => rw [found] at actual; cases Option.some.inj actual
  | handler actual permission row body closing =>
      cases Option.some.inj (found.symm.trans actual)
      have unprotected : capture.held = false := by
        cases held : capture.held with
        | false => rfl
        | true => simp [modeCheck, disposes, held] at permission
      exact ⟨unprotected, closing disposes, _, _, unprotected ▸ row, unprotected ▸ body⟩

/-- Reuse the existing recursive certificate constructor for this exact
selected scope and closing-effect bound. Stack realization, ordinary support,
port typing and owner inclusion remain explicit independent premises. -/
def capture_certificate
    (checked : checkCapture record.annotation.closeEffects scope effect operation = true)
    (found : select effect operation scope = some (.handler capture tail contract modes))
    (disposes : contract.dispose = true)
    (realized : SourceRecursiveRoutes.Realizes capture.shape stack plan)
    (supported : Supported stack.erase (Admission.outsideResources stack.erase))
    (typed : ScopedPorts.StackTyped signature tickets world stack input output)
    (internal : InternalUses stack.erase.liveTickets stack.erase.pending) :
    DeclaredClosingInvariant.Certificate signature world record stack :=
  realized.certificate (disposing_capture checked found disposes).2.1 supported typed internal

/-- A source offer has a dependency family exactly when its old mode row is
available. This prevents silently dropping a clause annotation at selection. -/
theorem offer_presence
    (source : SourceDependencyAnnotations.Offer operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held disposes row dependencies) : row.isSome = dependencies.isSome := by
  cases source <;> rfl

/-- Both lookups stop at the same first operation entry. The hereditary source
judgment, rather than an unrelated annotation table, supplies this agreement. -/
theorem declaration_lookup_presence
    (source : SourceDependencyAnnotations.Declarations operations policy contracts world environment allowed effect answer clauses table dependencies) :
    ((lookup operation table).bind (fun contract => contract.row held)).isSome =
      ((lookupDependencies operation dependencies).bind (modeDependencies held)).isSome := by
  induction clauses using Clauses.rec (motive_1 := fun _ => True) generalizing table dependencies
  case nil => cases source; rfl
  case cons key parameter binder body rest ihBody ihRest =>
    cases source with
    | cons known ordinary protectedMode remaining =>
        by_cases same : operation = key
        · subst key
          simp only [lookup, lookupDependencies]
          cases held with
          | false => exact offer_presence ordinary
          | true => exact offer_presence protectedMode
        · simp only [lookup, lookupDependencies, if_neg same]
          exact ihRest remaining
  all_goals trivial

/-- Select the actual hereditary clause body and the same dependency family
used by the local guard. The proof extends the established selected-body
induction; it adds no new clause typing or continuation ownership rule. -/
theorem selected_body
    (source : SourceDependencyAnnotations.Declarations operations policy contracts world environment allowed requested answer clauses table dependencies)
    (selected : ClauseAt operation clauses parameter binder code)
    (found : lookup operation table = some offered)
    (available : offered.row held = some row) :
    ∃ argument input resumeEffects closeEffects family,
      operations requested operation = some (argument, input) ∧
      (code.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.requiredActions.dispose = true → closeEffects = allowed) ∧
      (lookupDependencies operation dependencies).bind (modeDependencies held) = some family ∧
      ∀ owner (contract : SourceDependencyAnnotations.Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = held → contract.closeDemand.Perm contract.resumeDemand →
        SourceDependencyAnnotations.Body operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (environment.extend parameter argument) code answer ⟨owner, contract.erase, offered.dispose, row⟩ (family owner) := by
  induction selected generalizing table dependencies with
  | hit => cases source with
    | cons known ordinary protectedMode rest =>
        simp only [lookup, if_true] at found
        cases Option.some.inj found
        cases held with
        | false =>
            simp [ClauseContract.row] at available
            cases available ▸ ordinary with
            | available resumeInterface closeInterface family =>
                exact ⟨_, _, _, _, _, known, resumeInterface, closeInterface,
                  by simp [lookupDependencies, modeDependencies], family⟩
        | true =>
            simp [ClauseContract.row] at available
            cases available ▸ protectedMode with
            | available resumeInterface closeInterface family =>
                exact ⟨_, _, _, _, _, known, resumeInterface, closeInterface,
                  by simp [lookupDependencies, modeDependencies], family⟩
  | pass different next ih => cases source with
    | cons known ordinary protectedMode rest =>
        obtain ⟨argument, input, resumeEffects, closeEffects, family, signature, resume, close, located, body⟩ :=
          ih rest (by simpa only [lookup, if_neg different] using found)
        exact ⟨argument, input, resumeEffects, closeEffects, family, signature, resume, close,
          by simpa only [lookupDependencies, if_neg different] using located, body⟩

namespace Examples

def effectE : Instance := .user 91 []
def effectF : Instance := .user 92 []
def resumeFamily (owner : Nat) : Dependencies := .sequence .pure (.invoke ⟨owner, .resume⟩)
def disposeFamily (owner : Nat) : Dependencies := .invoke ⟨owner, .dispose⟩
def resumeTable : List (Nat × ClauseContract) := [(0, ⟨false, some [], some []⟩)]
def disposeTable : List (Nat × ClauseContract) := [(0, ⟨true, some [], none⟩)]
def resumeDependencies : ClauseDependencies := [(0, some resumeFamily, some resumeFamily)]
def disposeDependencies : ClauseDependencies := [(0, some disposeFamily, none)]
def handlerE : Scope → Scope := .handler effectE disposeTable disposeDependencies
def handlerF : Scope → Scope := .handler effectF resumeTable resumeDependencies
def callback : Dependencies := .sequence .pure (.request effectF 0)
def bad : Scope := .cleanup [effectF] callback (handlerF (handlerE .nil))
def surviving : Scope := .cleanup [effectF] callback (handlerE (handlerF .nil))

theorem removed_handler_rejected (outward : List Instance) : checkCapture outward bad effectE 0 = false := by
  simp [checkCapture, select, bad, handlerE, handlerF, effectE, effectF, resumeTable, disposeTable,
      resumeDependencies, disposeDependencies, lookup, lookupDependencies, Selection.prepend,
      Scope.held, Scope.shape, modeCheck, ClauseContract.row, modeDependencies,
      checkClosing, Shape.normal, Shape.closing, sameRoute, route]

theorem surviving_handler_accepted : checkCapture [effectF] surviving effectE 0 = true := by decide

theorem repeated_callback_effect_accepted :
    checkCapture [effectF] (.cleanup [effectF, effectF] callback (handlerE (handlerF .nil))) effectE 0 = true := by decide

def nested : Scope := .live 6 (.cleanup [.cell 4] (.request (.cell 4) 0) .nil) (.cell 4 (handlerE .nil))

theorem nested_retained_cell_accepted : checkCapture [] nested effectE 0 = true := by decide

theorem nested_source_override_rejected :
    checkCapture [] (.live 6
      (.cleanup [.cell 4] (.request (.cell 4) 0) (.handler (.cell 4) resumeTable resumeDependencies .nil))
      (.cell 4 (handlerE .nil))) effectE 0 = false := by decide

theorem running_completion_rejected : checkCapture [effectF] (.running surviving) effectE 0 = false := by decide

theorem missing_nearest_operation_rejected :
    checkCapture [] (.handler effectE [] [] (handlerE .nil)) effectE 0 = false := by decide

theorem builtin_blocks_source_handler :
    checkCapture [] (.cell 4 (.handler (.cell 4) disposeTable disposeDependencies .nil)) (.cell 4) 0 = true := by decide

end Examples

end Ash.OneShot.SourceDependencyCapture

#print axioms Ash.OneShot.SourceDependencyCapture.route_iff
#print axioms Ash.OneShot.SourceDependencyCapture.same_route_iff
#print axioms Ash.OneShot.SourceDependencyCapture.check_closing_iff

#print axioms Ash.OneShot.SourceDependencyCapture.check_capture_iff

#print axioms Ash.OneShot.SourceDependencyCapture.offer_presence

#print axioms Ash.OneShot.SourceDependencyCapture.declaration_lookup_presence

#print axioms Ash.OneShot.SourceDependencyCapture.selected_body

#print axioms Ash.OneShot.SourceDependencyCapture.Examples.removed_handler_rejected

#print axioms Ash.OneShot.SourceDependencyCapture.Examples.surviving_handler_accepted

#print axioms Ash.OneShot.SourceDependencyCapture.Examples.repeated_callback_effect_accepted

#print axioms Ash.OneShot.SourceDependencyCapture.Examples.nested_retained_cell_accepted

#print axioms Ash.OneShot.SourceDependencyCapture.Examples.nested_source_override_rejected

#print axioms Ash.OneShot.SourceDependencyCapture.Examples.running_completion_rejected

#print axioms Ash.OneShot.SourceDependencyCapture.Examples.missing_nearest_operation_rejected

#print axioms Ash.OneShot.SourceDependencyCapture.Examples.builtin_blocks_source_handler

#print axioms Ash.OneShot.SourceDependencyCapture.disposing_capture

#print axioms Ash.OneShot.SourceDependencyCapture.route_outward_weaken
#print axioms Ash.OneShot.SourceDependencyCapture.closing_outward_weaken
#print axioms Ash.OneShot.SourceDependencyCapture.check_capture_outward_weaken

#print axioms Ash.OneShot.SourceDependencyCapture.capture_certificate

#print axioms Ash.OneShot.SourceDependencyCapture.check_closing_handler_insert
#print axioms Ash.OneShot.SourceDependencyCapture.checked_closing_handler_insert
