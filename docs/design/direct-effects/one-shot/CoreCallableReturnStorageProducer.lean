import CallableContracts
import CoreCallableReceiverRefinement
import ReturnBoundaries

/-! Finite same-code returned-storage annotations. Successful checks construct
storage derivations; metadata contain no derivation proofs. The bounded producer
covers ordinary values, pairs, lambdas, applications, binds and branches. Control
and resource/cleanup source admission remain separate obligations. -/
namespace Ash.OneShot.CoreCallableReturnStorageProducer
open ScopedExpressions ScopedExecution
open Syntax (Dependency)
open CallableContracts (Contract Derives Captures CaptureAtom Ticket)
open CoreCallableReceiverRefinement (LexicalBounds)

/-- Literal contract templates and child annotations, interpreted against the
original Code. This is annotation data, not an alternative expression syntax. -/
inductive Annotation where
  | node : Option Contract → List Annotation → Annotation
  deriving Repr

abbrev Bindings := List (Nat × Contract)
def lookup : Bindings → Nat → Option Contract
  | [], _ => none
  | (key, value) :: rest, name => if name = key then some value else lookup rest name
def environment (bindings : Bindings) : CallableContracts.Environment := lookup bindings
def extend (bindings : Bindings) (name : Nat) (value : Contract) : Bindings := (name, value) :: bindings
@[simp] theorem environment_extend : environment (extend bindings name value) =
    (environment bindings).extend name value := rfl

def atomCheck (bindings : Bindings) (bound : List Nat) : Dependency → Bool
  | .resource identity => decide (identity ∈ bound)
  | .variable name => match lookup bindings name with
    | none => false
    | some value => decide (value.storageOf ⊆ bound)
  | .ticket _ => false

def captureCheck (bindings : Bindings) (bound : List Nat) (deps : List Dependency) : Bool :=
  deps.all (atomCheck bindings bound)

theorem atomCheck_sound (accepted : atomCheck bindings bound dep = true) :
    CaptureAtom (environment bindings) bound dep := by
  cases dep with
  | resource identity => exact .resource (of_decide_eq_true accepted)
  | «variable» name =>
      simp only [atomCheck] at accepted
      split at accepted
      · contradiction
      · rename_i value found
        exact .variable found (of_decide_eq_true accepted)
  | ticket owner => contradiction

theorem captureCheck_sound (accepted : captureCheck bindings bound deps = true) :
    Captures (environment bindings) bound deps := by
  apply CallableContracts.captures_iff.mpr
  intro dep member
  exact atomCheck_sound ((List.all_eq_true.mp accepted) dep member)

/-- A literal storage bound is validated against the same value's actual
capture dependencies. Function templates are accepted only by the lambda case. -/
def check (bindings : Bindings) : Code → Annotation → Option Contract
  | .unit, .node (some (.storage bound)) [] =>
      if captureCheck bindings bound Code.unit.dependencies then some (.storage bound) else none
  | .boolean value, .node (some (.storage bound)) [] =>
      if captureCheck bindings bound (Code.boolean value).dependencies then some (.storage bound) else none
  | .integer value, .node (some (.storage bound)) [] =>
      if captureCheck bindings bound (Code.integer value).dependencies then some (.storage bound) else none
  | .resourceRef (.activation identity), .node (some (.storage bound)) [] =>
      if captureCheck bindings bound (Code.resourceRef (.activation identity)).dependencies then some (.storage bound) else none
  | .variable name, .node none [] => lookup bindings name
  | .pair left right, .node none [leftAnn, rightAnn] => do
      let a ← check bindings left leftAnn
      let b ← check bindings right rightAnn
      return .pair a b
  | .lambda parameter body, .node (some (.function captures input output)) [bodyAnn] => do
      let actual ← check (extend bindings parameter input) body bodyAnn
      if actual = output ∧ captureCheck bindings captures (Code.lambda parameter body).dependencies = true
        then some (.function captures input output) else none
  | .app function argument, .node none [functionAnn, argumentAnn] => do
      let .function _ input output ← check bindings function functionAnn | none
      let actual ← check bindings argument argumentAnn
      if actual = input then some output else none
  | .bind parameter initializer body, .node none [initialAnn, bodyAnn] => do
      let input ← check bindings initializer initialAnn
      check (extend bindings parameter input) body bodyAnn
  | .branch condition yes no, .node none [conditionAnn, yesAnn, noAnn] => do
      let _ ← check bindings condition conditionAnn
      let result ← check bindings yes yesAnn
      let other ← check bindings no noAnn
      if result = other then some result else none
  | _, _ => none
termination_by code _ => code.nodes
decreasing_by all_goals simp only [Code.nodes]; all_goals omega

set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

theorem check_sound (accepted : check bindings code annotation = some result) :
    Derives declarations (environment bindings) world ticket code result := by
  induction code using Code.rec (motive_2 := fun _ => True) generalizing bindings annotation result ticket with
  | unit | boolean value | integer value | resourceRef value =>
      cases annotation with
      | node template children =>
        cases template <;> cases children <;> try simp [check] at accepted
        next template =>
          cases template <;> try simp [check] at accepted
          next bound =>
            first
            | rcases accepted with ⟨captured, rfl⟩
              exact .leaf (by simp [Code.IsValue]) (by rfl) (captureCheck_sound captured)
            | cases value <;> simp [check] at accepted
              next identity =>
                rcases accepted with ⟨captured, rfl⟩
                exact .leaf (by simp [Code.IsValue]) (by rfl) (captureCheck_sound captured)
  | «variable» name =>
      cases annotation with
      | node template children =>
        cases template <;> cases children <;> try simp [check] at accepted
        exact .variable accepted
  | pair left right ihL ihR =>
      cases annotation with
      | node template children =>
        cases template <;> cases children <;> try simp [check] at accepted
        next first rest =>
          cases rest <;> try simp [check] at accepted
          next second rest =>
            cases rest <;> try simp [check] at accepted
            simp only [Option.bind_eq_some_iff] at accepted
            obtain ⟨a, ha, b, hb, same⟩ := accepted
            cases Option.some.inj same
            exact .pair (ihL ha) (ihR hb)
  | lambda parameter body ih =>
      cases annotation with
      | node template children =>
        cases template <;> cases children <;> try simp [check] at accepted
        next template bodyAnn rest =>
          cases rest <;> cases template <;> try simp [check] at accepted
          next captures input output =>
            simp only [Option.bind_eq_some_iff] at accepted
            obtain ⟨actual, actualChecked, accepted⟩ := accepted
            split at accepted
            next same =>
              cases Option.some.inj accepted
              rcases same with ⟨rfl, captured⟩
              exact .lambda (by simpa using ih actualChecked) (captureCheck_sound captured)
            next => contradiction
  | app function argument ihF ihA =>
      cases annotation with
      | node template children =>
        cases template <;> cases children <;> try simp [check] at accepted
        next first rest =>
          cases rest <;> try simp [check] at accepted
          next second rest =>
            cases rest <;> try simp [check] at accepted
            simp only [Option.bind_eq_some_iff] at accepted
            obtain ⟨functionContract, functionChecked, accepted⟩ := accepted
            cases functionContract
            · contradiction
            · contradiction
            next captures input output =>
              cases argumentChecked : check bindings argument second with
              | none => simp [argumentChecked] at accepted
              | some actual =>
                simp [argumentChecked] at accepted
                rcases accepted with ⟨rfl, rfl⟩
                exact .app (ihF functionChecked) (ihA argumentChecked)
  | bind parameter initial body ihI ihB =>
      cases annotation with
      | node template children =>
        cases template <;> cases children <;> try simp [check] at accepted
        next first rest =>
          cases rest <;> try simp [check] at accepted
          next second rest =>
            cases rest <;> try simp [check] at accepted
            simp only [Option.bind_eq_some_iff] at accepted
            obtain ⟨input, initialChecked, bodyChecked⟩ := accepted
            exact .bind (ihI initialChecked) (by simpa using ihB bodyChecked)
  | branch condition yes no ihC ihY ihN =>
      cases annotation with
      | node template children =>
        cases template <;> cases children <;> try simp [check] at accepted
        next first rest =>
          cases rest <;> try simp [check] at accepted
          next second rest =>
            cases rest <;> try simp [check] at accepted
            next third rest =>
              cases rest <;> try simp [check] at accepted
              simp only [Option.bind_eq_some_iff] at accepted
              obtain ⟨conditionContract, conditionChecked, resultContract, yesChecked, other, noChecked, accepted⟩ := accepted
              split at accepted
              next same =>
                cases Option.some.inj accepted
                subst other
                exact .branch (ihC conditionChecked) (ihY yesChecked) (ihN noChecked)
              next => contradiction
  | perform | handle | resume | discard | resource | cleanup => cases annotation <;> try simp [check] at accepted
  | nil | cons => trivial


/-- Each retained binding names its actual checked initializer and its literal
storage template. A nearest-name extension is produced only after that SAME
initializer succeeds at that EXACT template in the preceding environment. -/
structure BindingAnnotation where
  name : Nat
  initializer : Code
  annotation : Annotation
  expected : Contract
  resources : List Nat
  deriving Repr

/-- The open-root obligation: every nearest binding entry is the initializer
of the SAME enclosing Code.bind. Initial roots have the empty path. No runtime
closure/frame origin is inferred merely from an independently supplied list. -/
inductive BindingAt (root : Code) : Code → List BindingAnnotation → Prop where
  | initial : BindingAt root root []
  | bind (previous : BindingAt root (.bind name initializer body) entries) :
      BindingAt root body
        ({ name := name, initializer := initializer, annotation := annotation,
           expected := expected, resources := resources } :: entries)

theorem BindingAt.nearest
    (origin : BindingAt root body (entry :: entries)) :
    BindingAt root (.bind entry.name entry.initializer body) entries := by
  cases origin with
  | bind previous => exact previous

def checkBindings (receiver : List Nat) : List BindingAnnotation → Option (Bindings × LexicalBounds)
  | [] => some ([], [])
  | entry :: rest => do
      let (bindings, lexical) ← checkBindings receiver rest
      let actual ← check bindings entry.initializer entry.annotation
      if actual = entry.expected ∧ actual.storageOf ⊆ entry.resources ∧ entry.resources ⊆ receiver
        then some (extend bindings entry.name actual, lexical.extend entry.name entry.resources)
        else none

inductive BindingOrigins (declarations : Instantiation.DeclarationRegistry) (world receiver : List Nat) :
    List BindingAnnotation → Bindings → LexicalBounds → Prop where
  | nil : BindingOrigins declarations world receiver [] [] []
  | cons (previous : BindingOrigins declarations world receiver rest bindings lexical)
      (initializer : Derives declarations (environment bindings) world .none entry.initializer entry.expected)
      (included : entry.expected.storageOf ⊆ entry.resources) (received : entry.resources ⊆ receiver) :
      BindingOrigins declarations world receiver (entry :: rest)
        (extend bindings entry.name entry.expected) (lexical.extend entry.name entry.resources)

theorem checkBindings_sound
    (accepted : checkBindings receiver entries = some (bindings, lexical)) :
    BindingOrigins declarations world receiver entries bindings lexical := by
  induction entries generalizing bindings lexical with
  | nil =>
      simp [checkBindings] at accepted
      obtain ⟨rfl, rfl⟩ := accepted
      exact .nil
  | cons entry rest ih =>
      cases previousChecked : checkBindings receiver rest with
      | none => simp [checkBindings, previousChecked] at accepted
      | some previous =>
        rcases previous with ⟨beforeBindings, beforeLexical⟩
        cases initializerChecked : check beforeBindings entry.initializer entry.annotation with
        | none => simp [checkBindings, previousChecked, initializerChecked] at accepted
        | some actual =>
          simp [checkBindings, previousChecked, initializerChecked] at accepted
          obtain ⟨⟨same, included, received⟩, bindingsSame, lexicalSame⟩ := accepted
          subst actual
          subst bindings lexical
          exact .cons (ih previousChecked) (check_sound initializerChecked) included received

/-- The paired projection relates actual storage contracts to the SAME finite
rich lexical support data; shadowed entries cannot replace the nearest origin. -/
def LexicalFits (bindings : Bindings) (lexical : LexicalBounds) (receiver : List Nat) : Prop :=
  ∀ name value, lookup bindings name = some value →
    ∃ resources, lexical.lookup name = some resources ∧ value.storageOf ⊆ resources ∧ resources ⊆ receiver

theorem BindingOrigins.lexical_fits
    (origins : BindingOrigins declarations world receiver entries bindings lexical) :
    LexicalFits bindings lexical receiver := by
  induction origins with
  | nil => intro name value found; contradiction
  | @cons rest bindings lexical entry previous initializer included received ih =>
      intro name value found
      by_cases same : name = entry.name
      · subst name
        simp [lookup, extend] at found
        subst value
        exact ⟨entry.resources, by simp [LexicalBounds.extend, LexicalBounds.lookup], included, received⟩
      · simp only [lookup, extend, if_neg same] at found
        obtain ⟨resources, known, included, received⟩ := ih name value found
        exact ⟨resources, by simpa [LexicalBounds.extend, LexicalBounds.lookup, same] using known, included, received⟩

theorem LexicalFits.world (world : List Nat)
    (fits : LexicalFits bindings lexical receiver) (issued : receiver ⊆ world)
    (known : lookup bindings name = some value) : value.storageOf ⊆ world := by
  obtain ⟨resources, found, included, received⟩ := fits name value known
  exact included.trans (received.trans issued)

/-- Open-root storage evidence retains the checked initializer origins. The
closed empty-root producer below has no unexplained environment-origin input. -/
theorem from_origins
    (origins : BindingOrigins declarations world receiver entries bindings lexical)
    (accepted : check bindings code annotation = some result) :
    Derives declarations (environment bindings) world ticket code result ∧
      LexicalFits bindings lexical receiver :=
  ⟨check_sound accepted, origins.lexical_fits⟩

theorem initial (accepted : check [] code annotation = some result) :
    Derives declarations CallableContracts.Environment.empty world ticket code result :=
  check_sound accepted

/-- Paired actual-input receipt: both derivations are computed from the SAME
body and replacement Code. No replacement contract is inferred from ports. -/
theorem substitution_receipt
    (bodyChecked : check (extend bindings name input) body bodyAnnotation = some result)
    (valueChecked : check bindings value valueAnnotation = some input)
    (closed : ClosedValue value) :
    Derives declarations (environment bindings) world ticket (body.subst name value) result := by
  apply CallableContracts.substitution
  · simpa using (check_sound (declarations := declarations) (world := world) (ticket := ticket) bodyChecked)
  · exact check_sound valueChecked
  · exact closed

/-- Application agreement is the exact storage domain/result, not a signature
projection. The actual argument must independently check at that SAME domain. -/
theorem app_receipt
    (functionChecked : check bindings function functionAnnotation = some (.function captures input output))
    (argumentChecked : check bindings argument argumentAnnotation = some input) :
    Derives declarations (environment bindings) world ticket (.app function argument) output :=
  .app (check_sound functionChecked) (check_sound argumentChecked)

/-- A retaining value cannot pass an outside returned-storage bound, even if
its public result port contains no reference. This uses the existing value
storage theorem, not a new finite example or a conservative syntax observer. -/
theorem retaining_rejected {declarations : Instantiation.DeclarationRegistry} {world : List Nat} {ticket : Ticket} (isValue : value.IsValue)
    (retained : identity ∈ Syntax.resourceDependencies value.dependencies)
    (outside : identity ∉ result.storageOf) :
    check bindings value annotation ≠ some result := by
  intro accepted
  exact outside (CallableContracts.value_support
    (check_sound (declarations := declarations) (world := world) (ticket := ticket) accepted) isValue retained)


/-- Returned-storage validation uses an independently supplied original bound,
which can be smaller than the receiver used by the opened resource body. -/
def returnedCheck (bindings : Bindings) (originalBound : List Nat) (code : Code)
    (annotation : Annotation) : Option Contract := do
  let result ← check bindings code annotation
  if result.storageOf ⊆ originalBound then some result else none

theorem returnedCheck_sound
    (accepted : returnedCheck bindings originalBound code annotation = some result) :
    Derives declarations (environment bindings) world ticket code result ∧ result.storageOf ⊆ originalBound := by
  cases codeChecked : check bindings code annotation with
  | none => simp [returnedCheck, codeChecked] at accepted
  | some actual =>
      simp [returnedCheck, codeChecked] at accepted
      rcases accepted with ⟨bounded, rfl⟩
      exact ⟨check_sound codeChecked, bounded⟩

/-- Finite paired binding and output checks construct the structural body
receipt and rich lexical storage relation on that SAME Code. The actual body
receiver and original returned bound are deliberately separate. -/
theorem paired_receipt
    (bindingsChecked : checkBindings receiver entries = some (bindings, lexical))
    (bodyChecked : returnedCheck bindings originalBound code bodyAnnotation = some result) :
    BindingOrigins declarations world receiver entries bindings lexical ∧
      Derives declarations (environment bindings) world ticket code result ∧
      LexicalFits bindings lexical receiver ∧ result.storageOf ⊆ originalBound := by
  have origins := checkBindings_sound (declarations := declarations) (world := world) bindingsChecked
  obtain ⟨derived, bounded⟩ := returnedCheck_sound (declarations := declarations) (world := world) (ticket := ticket) bodyChecked
  exact ⟨origins, derived, origins.lexical_fits, bounded⟩

theorem paired_world {declarations : Instantiation.DeclarationRegistry} {world : List Nat} {ticket : Ticket}
    (bindingsChecked : checkBindings receiver entries = some (bindings, lexical))
    (bodyChecked : returnedCheck bindings originalBound code annotation = some result)
    (originalIssued : originalBound ⊆ originalWorld) : result.storageOf ⊆ originalWorld :=
  (paired_receipt (declarations := declarations) (world := world) (ticket := ticket) bindingsChecked bodyChecked).2.2.2.trans originalIssued

/-- The source-facing open-body producer retains the exact enclosing-bind
path, checked actual initializer origins and computed lexical/storage pairing.
The root must be the caller's SAME admitted source, not an unrelated template. -/
theorem paired_at_origin
    (origin : BindingAt root code entries)
    (bindingsChecked : checkBindings receiver entries = some (bindings, lexical))
    (bodyChecked : returnedCheck bindings originalBound code annotation = some result) :
    BindingAt root code entries ∧
      BindingOrigins declarations world receiver entries bindings lexical ∧
      Derives declarations (environment bindings) world ticket code result ∧
      LexicalFits bindings lexical receiver ∧ result.storageOf ⊆ originalBound :=
  ⟨origin, paired_receipt bindingsChecked bodyChecked⟩

theorem initial_returned
    (accepted : returnedCheck [] originalBound code annotation = some result) :
    Derives declarations CallableContracts.Environment.empty world ticket code result ∧
      result.storageOf ⊆ originalBound :=
  returnedCheck_sound accepted

/-- Existing retaining-template negative, reused at its actual opening. -/
theorem retaining_template_rejected {declarations : Instantiation.DeclarationRegistry} {world : List Nat} {ticket : Ticket}
    (outside : 7 ∉ result.storageOf) :
    check bindings
      (ReturnBoundaries.Examples.retainingTemplate.instantiate (Instantiation.Environment.empty.bind 4 7))
      annotation ≠ some result := by
  apply retaining_rejected (declarations := declarations) (world := world) (ticket := ticket) (identity := 7)
  · trivial
  · decide
  · exact outside

#print axioms check_sound
#print axioms BindingAt.nearest
#print axioms checkBindings_sound
#print axioms BindingOrigins.lexical_fits
#print axioms LexicalFits.world
#print axioms from_origins
#print axioms initial
#print axioms substitution_receipt
#print axioms app_receipt
#print axioms retaining_rejected
#print axioms returnedCheck_sound
#print axioms paired_receipt
#print axioms paired_world
#print axioms paired_at_origin
#print axioms initial_returned
#print axioms retaining_template_rejected
end Ash.OneShot.CoreCallableReturnStorageProducer
