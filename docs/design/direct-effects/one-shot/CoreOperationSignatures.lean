import CoreTypeSupport
import ScopedPortTyping

/-! Finite declaration-port construction from supplied Core metadata. Exact
instances preserve complete argument trees. Callable retention is erased only
at declared ports and is checked separately by CoreTypeSupport.

These inputs are not an authenticated Rust export. This component constructs
ScopedPorts.Signature, not enriched operation evidence or source admission. Builtin cell signature compatibility and authentication
against the validated Rust registry remain separate obligations. -/
namespace Ash.OneShot.CoreOperationSignatures
open Instantiation CoreTypeSupport

inductive Error where
  | unresolvedResource : Nat → Error
  | typeDecoration : DecorationError → Error
  | conflictingPorts : Instance → Nat → Error
  deriving DecidableEq, Repr

structure RawEntry where
  effect : Effect
  operation : Nat
  input : CoreSyntax.ValueType
  output : CoreSyntax.ValueType
  deriving DecidableEq, Repr

structure ResolvedEntry where
  effect : Instance
  operation : Nat
  input : ScopedPorts.Port
  output : ScopedPorts.Port
  deriving DecidableEq, Repr

abbrev Table := List ResolvedEntry

private theorem bind_ok {α β : Type} (a : Except Error α)
    (f : α → Except Error β) (value : β) (success : a.bind f = .ok value) :
    ∃ item, a = .ok item ∧ f item = .ok value := by
  cases h : a with
  | error e => simp [h, Except.bind] at success
  | ok item => exact ⟨item, rfl, by simpa [h, Except.bind] using success⟩

private theorem mapM_sound {α β : Type} (f : α → Except Error β) (xs : List α)
    (ys : List β) (success : xs.mapM f = .ok ys) :
    ListRealizes (fun x y => f x = .ok y) xs ys := by
  induction xs generalizing ys with
  | nil => simp [List.mapM_nil] at success; cases success; exact .nil
  | cons x xs ih =>
      rw [List.mapM_cons] at success
      obtain ⟨head, first, rest⟩ := bind_ok _ _ _ success
      obtain ⟨tail, remaining, result⟩ := bind_ok _ _ _ rest
      have same : head :: tail = ys := by simpa [Pure.pure, Except.pure] using result
      subst ys
      exact .cons first (ih _ remaining)

private theorem list_rel_mono (related : ListRealizes relation xs ys)
    (convert : ∀ x y, relation x y → other x y) : ListRealizes other xs ys := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (convert _ _ head) ih

/-- Partial executable lookup realizes bound names through the existing lexical
map; already closed activation names are preserved. -/
def realizeName (environment : Instantiation.Environment) : ResourceName → Except Error Nat
  | .activation identity => .ok identity
  | .bound name => match environment name with
    | some identity => .ok identity
    | none => .error (.unresolvedResource name)

def realizeArgument (environment : Instantiation.Environment) : Argument → Except Error TypeArgument
  | .nominal identity => .ok (.nominal identity)
  | .resource name => do pure (.resource (← realizeName environment name))
  | .apply head argument => do
      pure (.apply (← realizeArgument environment head) (← realizeArgument environment argument))

def realizeEffect (environment : Instantiation.Environment) : Effect → Except Error Instance
  | .cell name => do pure (.cell (← realizeName environment name))
  | .user family arguments => do pure (.user family (← arguments.mapM (realizeArgument environment)))

def realizeType (environment : Instantiation.Environment) : Instantiation.ValueType → Except Error Ty
  | .unit => .ok .unit
  | .boolean => .ok .boolean
  | .integer => .ok .integer
  | .reference name => do pure (.reference (← realizeName environment name))
  | .product left right => do
      pure (.product (← realizeType environment left) (← realizeType environment right))
  | .function input output requests retained => do
      pure (.function (← realizeType environment input) (← realizeType environment output)
        (← requests.mapM (realizeEffect environment)) (← retained.mapM (realizeName environment)))

theorem realizeName_sound (success : realizeName environment name = .ok identity) :
    NameRealizes environment name identity := by
  cases name with
  | activation atom => simp [realizeName] at success; cases success; exact .activation
  | bound name =>
      cases known : environment name with
      | none => simp [realizeName, known] at success
      | some actual =>
          simp [realizeName, known] at success
          cases success
          exact .bound known

theorem realizeArgument_sound (success : realizeArgument environment source = .ok target) :
    ArgumentRealizes environment source target := by
  induction source generalizing target with
  | nominal identity => simp [realizeArgument] at success; cases success; exact .nominal
  | resource name =>
      obtain ⟨identity, first, result⟩ := bind_ok _ _ _ success
      have same : TypeArgument.resource identity = target := by simpa [Pure.pure, Except.pure] using result
      subst target
      exact .resource (realizeName_sound first)
  | apply head argument ihHead ihArgument =>
      obtain ⟨a, first, rest⟩ := bind_ok _ _ _ success
      obtain ⟨b, second, result⟩ := bind_ok _ _ _ rest
      have same : TypeArgument.apply a b = target := by simpa [Pure.pure, Except.pure] using result
      subst target
      exact .apply (ihHead first) (ihArgument second)

theorem realizeEffect_sound (success : realizeEffect environment source = .ok target) :
    EffectRealizes environment source target := by
  cases source with
  | cell name =>
      obtain ⟨identity, first, result⟩ := bind_ok _ _ _ success
      have same : Instance.cell identity = target := by simpa [Pure.pure, Except.pure] using result
      subst target
      exact .cell (realizeName_sound first)
  | user family arguments =>
      obtain ⟨actual, first, result⟩ := bind_ok _ _ _ success
      have same : Instance.user family actual = target := by simpa [Pure.pure, Except.pure] using result
      subst target
      exact .user (list_rel_mono (mapM_sound _ _ _ first) (fun _ _ h => realizeArgument_sound h))

theorem realizeType_sound (success : realizeType environment source = .ok target) :
    TypeRealizes environment source target := by
  induction source generalizing target with
  | unit => simp [realizeType] at success; cases success; exact .unit
  | boolean => simp [realizeType] at success; cases success; exact .boolean
  | integer => simp [realizeType] at success; cases success; exact .integer
  | reference name =>
      obtain ⟨identity, first, result⟩ := bind_ok _ _ _ success
      have same : Ty.reference identity = target := by simpa [Pure.pure, Except.pure] using result
      subst target
      exact .reference (realizeName_sound first)
  | product left right ihLeft ihRight =>
      obtain ⟨a, first, rest⟩ := bind_ok _ _ _ success
      obtain ⟨b, second, result⟩ := bind_ok _ _ _ rest
      have same : Ty.product a b = target := by simpa [Pure.pure, Except.pure] using result
      subst target
      exact .product (ihLeft first) (ihRight second)
  | function input output requests retained ihInput ihOutput =>
      obtain ⟨a, first, rest⟩ := bind_ok _ _ _ success
      obtain ⟨b, second, rest⟩ := bind_ok _ _ _ rest
      obtain ⟨row, third, rest⟩ := bind_ok _ _ _ rest
      obtain ⟨support, fourth, result⟩ := bind_ok _ _ _ rest
      have same : Ty.function a b row support = target := by simpa [Pure.pure, Except.pure] using result
      subst target
      exact .function (ihInput first) (ihOutput second)
        (list_rel_mono (mapM_sound _ _ _ third) (fun _ _ h => realizeEffect_sound h))
        (list_rel_mono (mapM_sound _ _ _ fourth) (fun _ _ h => realizeName_sound h))

/-- Declaration ports do not supply callable retention. The canonical empty
annotation is used only to reach the existing supported type realization. -/
def emptySupport : CoreSyntax.ValueType → SupportShape
  | .unit => .unit
  | .boolean => .boolean
  | .integer => .integer
  | .reference _ => .reference
  | .product left right => .product (emptySupport left) (emptySupport right)
  | .function input output _ => .function (emptySupport input) (emptySupport output) []
  | .unsupported _ => .unit

def declarationPort (environment : Instantiation.Environment) (source : CoreSyntax.ValueType) :
    Except Error ScopedPorts.Port := do
  let decorated ← (decorate source (emptySupport source)).mapError Error.typeDecoration
  let actual ← realizeType environment decorated
  pure (ScopedPorts.eraseType actual)

def resolveEntry (environment : Instantiation.Environment) (entry : RawEntry) : Except Error ResolvedEntry := do
  let effect ← realizeEffect environment entry.effect
  let input ← declarationPort environment entry.input
  let output ← declarationPort environment entry.output
  pure ⟨effect, entry.operation, input, output⟩

/-- Repeated keys are allowed only after explicit equality of both ports.
Complete realized instances, including argument trees, participate in the key. -/
def checkPair (a b : ResolvedEntry) : Except Error Unit :=
  if a.effect = b.effect ∧ a.operation = b.operation then
    if a.input = b.input ∧ a.output = b.output then .ok ()
    else .error (.conflictingPorts a.effect a.operation)
  else .ok ()

def checkConflicts : Table → Except Error Unit
  | [] => .ok ()
  | first :: rest => do
      let _ ← rest.mapM (checkPair first)
      checkConflicts rest

/-- Identical repetitions remain in this finite table; each has passed the
explicit equality check. No entry is added or dropped during construction. -/
def build (environment : Instantiation.Environment) (entries : List RawEntry) : Except Error Table := do
  let table ← entries.mapM (resolveEntry environment)
  checkConflicts table
  pure table

def lookup : Table → ScopedPorts.Signature
  | [], _, _ => none
  | entry :: rest, effect, operation =>
      if entry.effect = effect ∧ entry.operation = operation then some (entry.input, entry.output)
      else lookup rest effect operation

private theorem mapError_ok {α ε : Type} (a : Except ε α) (f : ε → Error) (value : α)
    (success : a.mapError f = .ok value) : a = .ok value := by
  cases a with
  | error e => simp [Except.mapError] at success
  | ok item => simpa [Except.mapError] using success

/-- Successful declaration ports use supported Core metadata and exactly the
existing lexical type-realization relation followed by retention erasure. -/
def DeclaredPort (environment : Instantiation.Environment) (source : CoreSyntax.ValueType)
    (port : ScopedPorts.Port) : Prop :=
  ∃ decorated actual, decorate source (emptySupport source) = .ok decorated ∧
    TypeRealizes environment decorated actual ∧ ScopedPorts.eraseType actual = port

theorem declarationPort_sound (success : declarationPort environment source = .ok port) :
    DeclaredPort environment source port := by
  obtain ⟨decorated, first, rest⟩ := bind_ok _ _ _ success
  obtain ⟨actual, second, result⟩ := bind_ok _ _ _ rest
  exact ⟨decorated, actual, mapError_ok _ _ _ first, realizeType_sound second,
    by simpa [Pure.pure, Except.pure] using result⟩

def EntryRealizes (environment : Instantiation.Environment) (raw : RawEntry)
    (resolved : ResolvedEntry) : Prop :=
  EffectRealizes environment raw.effect resolved.effect ∧ raw.operation = resolved.operation ∧
    DeclaredPort environment raw.input resolved.input ∧ DeclaredPort environment raw.output resolved.output

theorem resolveEntry_sound (success : resolveEntry environment raw = .ok resolved) :
    EntryRealizes environment raw resolved := by
  obtain ⟨effect, first, rest⟩ := bind_ok _ _ _ success
  obtain ⟨input, second, rest⟩ := bind_ok _ _ _ rest
  obtain ⟨output, third, result⟩ := bind_ok _ _ _ rest
  have same : ResolvedEntry.mk effect raw.operation input output = resolved := by
    simpa [Pure.pure, Except.pure] using result
  subst resolved
  exact ⟨realizeEffect_sound first, rfl, declarationPort_sound second, declarationPort_sound third⟩

theorem DeclaredPort.unique (first : DeclaredPort environment source a)
    (second : DeclaredPort environment source b) : a = b := by
  obtain ⟨decoratedA, actualA, successA, realizedA, rfl⟩ := first
  obtain ⟨decoratedB, actualB, successB, realizedB, rfl⟩ := second
  have same : decoratedA = decoratedB := Except.ok.inj (successA.symm.trans successB)
  subst decoratedB
  exact congrArg ScopedPorts.eraseType (type_realization_unique realizedA realizedB)

theorem EntryRealizes.unique (first : EntryRealizes environment raw a)
    (second : EntryRealizes environment raw b) : a = b := by
  have effect := effect_realization_unique first.1 second.1
  have operation := first.2.1.symm.trans second.2.1
  have input := DeclaredPort.unique first.2.2.1 second.2.2.1
  have output := DeclaredPort.unique first.2.2.2 second.2.2.2
  cases a
  cases b
  simp_all

/-- This equality deliberately ignores only callable retention. All reference
identities, nested ports and exact function request trees remain compared. -/
theorem realized_port_unique
    (first : TypeRealizes environment sourceA actualA)
    (second : TypeRealizes environment sourceB actualB)
    (same : CoreTypeSupport.erase sourceA = CoreTypeSupport.erase sourceB) :
    ScopedPorts.eraseType actualA = ScopedPorts.eraseType actualB := by
  induction first generalizing sourceB actualB with
  | unit => cases second <;> simp [CoreTypeSupport.erase] at same; rfl
  | boolean => cases second <;> simp [CoreTypeSupport.erase] at same; rfl
  | integer => cases second <;> simp [CoreTypeSupport.erase] at same; rfl
  | reference name =>
      cases second <;> simp [CoreTypeSupport.erase] at same
      case reference other =>
        cases same
        exact congrArg ScopedPorts.Port.reference (name_realization_unique name other)
  | product left right ihLeft ihRight =>
      cases second <;> simp [CoreTypeSupport.erase] at same
      case product otherLeft otherRight =>
        simp only [ScopedPorts.eraseType, ihLeft otherLeft same.1, ihRight otherRight same.2]
  | function input output requests retained ihInput ihOutput =>
      cases second <;> simp [CoreTypeSupport.erase] at same
      case function otherInput otherOutput otherRequests otherRetained =>
        obtain ⟨sameInput, sameOutput, sameRequests⟩ := same
        cases sameRequests
        have row := list_realization_unique (relation := EffectRealizes environment)
          (fun _ _ _ a b => effect_realization_unique a b) requests otherRequests
        simp only [ScopedPorts.eraseType, ihInput otherInput sameInput, ihOutput otherOutput sameOutput, row]

/-- Any supplied support annotation that successfully decorates and realizes
this raw type produces the same declaration port as the canonical empty one.
It need not realize its retained names to construct the declaration itself. -/
theorem declared_port_support_independent
    (declared : DeclaredPort environment source port)
    (success : decorate source support = .ok decorated)
    (realized : TypeRealizes environment decorated actual) :
    ScopedPorts.eraseType actual = port := by
  obtain ⟨canonical, canonicalActual, canonicalSuccess, canonicalRealized, rfl⟩ := declared
  exact realized_port_unique realized canonicalRealized
    ((successful_erasure success).trans (successful_erasure canonicalSuccess).symm)

private theorem source_member_has_target (related : ListRealizes relation xs ys)
    (member : x ∈ xs) : ∃ y, y ∈ ys ∧ relation x y := by
  induction related with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons_self, head⟩
      · obtain ⟨y, present, checked⟩ := ih later
        exact ⟨y, List.mem_cons_of_mem _ present, checked⟩

/-- Validation compares every realized alias before first-key lookup is used. -/
def Compatible (table : Table) : Prop :=
  ∀ a, a ∈ table → ∀ b, b ∈ table → a.effect = b.effect → a.operation = b.operation →
    a.input = b.input ∧ a.output = b.output

private theorem checkPair_sound (success : checkPair a b = .ok ())
    (effect : a.effect = b.effect) (operation : a.operation = b.operation) :
    a.input = b.input ∧ a.output = b.output := by
  unfold checkPair at success
  simp only [effect, operation, and_self, ite_true] at success
  split at success
  · assumption
  · simp at success

theorem checkConflicts_sound (success : checkConflicts table = .ok ()) : Compatible table := by
  induction table with
  | nil => intro a member; cases member
  | cons first rest ih =>
      obtain ⟨checks, heads, tail⟩ := bind_ok _ _ _ success
      have headChecked := mapM_sound _ _ _ heads
      have tailChecked := ih tail
      intro a aMember b bMember effects operations
      rcases List.mem_cons.mp aMember with rfl | aRest
      · rcases List.mem_cons.mp bMember with rfl | bRest
        · exact ⟨rfl, rfl⟩
        · obtain ⟨result, _, checked⟩ := source_member_has_target headChecked bRest
          cases result
          exact checkPair_sound checked effects operations
      · rcases List.mem_cons.mp bMember with rfl | bRest
        · obtain ⟨result, _, checked⟩ := source_member_has_target headChecked aRest
          cases result
          have pair := checkPair_sound checked effects.symm operations.symm
          exact ⟨pair.1.symm, pair.2.symm⟩
        · exact tailChecked a aRest b bRest effects operations

/-- Acceptance preserves a realization for every entry in both directions,
including explicitly checked identical repetitions. -/
theorem build_sound (success : build environment entries = .ok table) :
    ListRealizes (EntryRealizes environment) entries table ∧ Compatible table := by
  obtain ⟨resolved, first, rest⟩ := bind_ok _ _ _ success
  obtain ⟨checked, second, result⟩ := bind_ok _ _ _ rest
  have same : resolved = table := by simpa [Pure.pure, Except.pure] using result
  subst table
  cases checked
  exact ⟨list_rel_mono (mapM_sound _ _ _ first) (fun _ _ h => resolveEntry_sound h),
    checkConflicts_sound second⟩

/-- Every returned operation key is an actual finite table entry. -/
theorem lookup_sound (known : lookup table effect operation = some ports) :
    ∃ entry, entry ∈ table ∧ entry.effect = effect ∧ entry.operation = operation ∧
      (entry.input, entry.output) = ports := by
  induction table with
  | nil => simp [lookup] at known
  | cons first rest ih =>
      unfold lookup at known
      split at known
      · rename_i matching
        have same : (first.input, first.output) = ports := Option.some.inj known
        exact ⟨first, List.mem_cons_self, matching.1, matching.2, same⟩
      · obtain ⟨entry, member, effects, operations, same⟩ := ih known
        exact ⟨entry, List.mem_cons_of_mem _ member, effects, operations, same⟩

/-- Pairwise validation makes first-key lookup complete for every accepted
entry, even when distinct bound names realize to the same exact key. -/
theorem lookup_complete (compatible : Compatible table) (member : entry ∈ table) :
    lookup table entry.effect entry.operation = some (entry.input, entry.output) := by
  induction table with
  | nil => cases member
  | cons first rest ih =>
      rw [lookup]
      split
      · rename_i matching
        have ports := compatible first List.mem_cons_self entry member matching.1 matching.2
        rw [ports.1, ports.2]
      · rename_i different
        rcases List.mem_cons.mp member with rfl | later
        · exact False.elim (different ⟨rfl, rfl⟩)
        · apply ih (fun a ha b hb => compatible a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)) later

/-- A successful table exposes exactly its accepted source operation keys and
ports. The characterization needs no resolved-table membership premise. -/
theorem accepted_lookup_iff (success : build environment entries = .ok table) :
    lookup table effect operation = some ports ↔
      ∃ raw, raw ∈ entries ∧ ∃ resolved, EntryRealizes environment raw resolved ∧
        resolved.effect = effect ∧ resolved.operation = operation ∧
        (resolved.input, resolved.output) = ports := by
  have accepted := build_sound success
  constructor
  · intro known
    obtain ⟨resolved, member, effects, operations, equal⟩ := lookup_sound known
    obtain ⟨raw, origin, related⟩ := realized_member_has_origin accepted.1 member
    exact ⟨raw, origin, resolved, related, effects, operations, equal⟩
  · rintro ⟨raw, origin, resolved, related, rfl, rfl, rfl⟩
    obtain ⟨stored, member, storedRelated⟩ := source_member_has_target accepted.1 origin
    have same := EntryRealizes.unique related storedRelated
    subst stored
    exact lookup_complete accepted.2 member

/-- Every accepted raw declaration has a realized entry and a successful
lookup; identical duplicates cannot silently discard a conflicting port. -/
theorem accepted_entry_lookup (success : build environment entries = .ok table)
    (present : raw ∈ entries) :
    ∃ resolved, EntryRealizes environment raw resolved ∧
      lookup table resolved.effect resolved.operation = some (resolved.input, resolved.output) := by
  have accepted := build_sound success
  obtain ⟨resolved, member, related⟩ := source_member_has_target accepted.1 present
  exact ⟨resolved, related, lookup_complete accepted.2 member⟩

/-- A key with no source declaration realizing to it is rejected by lookup. -/
theorem absent_key (success : build environment entries = .ok table)
    (absent : ∀ raw, raw ∈ entries → ∀ resolved, EntryRealizes environment raw resolved →
      resolved.effect ≠ effect ∨ resolved.operation ≠ operation) :
    lookup table effect operation = none := by
  cases found : lookup table effect operation with
  | none => rfl
  | some ports =>
      obtain ⟨raw, member, resolved, related, effects, operations, _⟩ :=
        (accepted_lookup_iff success).mp found
      rcases absent raw member resolved related with noEffect | noOperation
      · exact False.elim (noEffect effects)
      · exact False.elim (noOperation operations)

namespace Examples

def entry (effect : Effect) (operation : Nat) (input output : CoreSyntax.ValueType) : RawEntry :=
  ⟨effect, operation, input, output⟩

def empty := Instantiation.Environment.empty
def outer := empty.bind 3 7
def inner := outer.bind 3 11
def aliases := inner.bind 4 11

def distinct : List RawEntry := [
  entry (.user 7 []) 0 .unit .boolean,
  entry (.user 8 []) 0 .integer .unit]

example : build empty distinct = .ok [
    ⟨.user 7 [], 0, .unit, .boolean⟩, ⟨.user 8 [], 0, .integer, .unit⟩] := rfl

/-- Family equality alone does not identify complete closed argument trees. -/
def exactTrees : List RawEntry := [
  entry (.user 9 [.nominal 1]) 2 .unit .unit,
  entry (.user 9 [.resource (.activation 1)]) 2 .integer .integer,
  entry (.user 9 [.apply (.nominal 1) (.nominal 2)]) 2 .boolean .boolean]

example : build empty exactTrees = .ok [
    ⟨.user 9 [.nominal 1], 2, .unit, .unit⟩,
    ⟨.user 9 [.resource 1], 2, .integer, .integer⟩,
    ⟨.user 9 [.apply (.nominal 1) (.nominal 2)], 2, .boolean, .boolean⟩] := rfl

def resourceEntry : RawEntry := entry (.user 31 [.apply (.nominal 4) (.resource (.bound 3))]) 5
  (.reference (.bound 3))
  (.function .unit (.reference (.bound 3)) [.user 33 [.apply (.resource (.bound 3)) (.nominal 8)]])

example : resolveEntry outer resourceEntry = .ok
    ⟨.user 31 [.apply (.nominal 4) (.resource 7)], 5, .reference 7,
      .function .unit (.reference 7) [.user 33 [.apply (.resource 7) (.nominal 8)]]⟩ := rfl

example : resolveEntry inner resourceEntry = .ok
    ⟨.user 31 [.apply (.nominal 4) (.resource 11)], 5, .reference 11,
      .function .unit (.reference 11) [.user 33 [.apply (.resource 11) (.nominal 8)]]⟩ := rfl

/-- Aliased source names conflict after realization, even though raw keys differ.
This is generic declaration data, not builtin cell-registry authentication. -/
example : build aliases [entry (.cell (.bound 3)) 0 .unit .unit,
    entry (.cell (.bound 4)) 0 .integer .unit] = .error (.conflictingPorts (.cell 11) 0) := rfl

example : build aliases [entry (.cell (.bound 3)) 0 .unit .unit,
    entry (.cell (.bound 4)) 0 .unit .unit] = .ok [
      ⟨.cell 11, 0, .unit, .unit⟩, ⟨.cell 11, 0, .unit, .unit⟩] := rfl

example : resolveEntry empty (entry (.cell (.bound 99)) 0 .unit .unit) =
    .error (.unresolvedResource 99) := rfl

example : resolveEntry empty (entry (.user 1 []) 0 (.reference (.bound 99)) .unit) =
    .error (.unresolvedResource 99) := rfl

example : resolveEntry empty (entry (.user 1 []) 0 (.unsupported .nominal) .unit) =
    .error (.typeDecoration (.unsupportedSource .nominal)) := rfl

example : lookup [⟨.user 7 [], 0, .unit, .boolean⟩, ⟨.user 8 [], 0, .integer, .unit⟩]
    (.user 7 []) 99 = none := rfl

example : lookup [⟨.user 9 [.nominal 1], 2, .unit, .unit⟩]
    (.user 9 [.resource 1]) 2 = none := rfl

/-- A resource-free declaration port needs no retention annotation. Authentication
and realization of any captured support remain a separate obligation. -/
example : declarationPort empty (.function .unit .unit []) = .ok (.function .unit .unit []) := rfl

example : realizeType empty (.function .unit .unit [] [.bound 99]) =
    .error (.unresolvedResource 99) := rfl

end Examples

#print axioms realizeName_sound
#print axioms realizeArgument_sound
#print axioms realizeEffect_sound
#print axioms realizeType_sound
#print axioms declarationPort_sound
#print axioms resolveEntry_sound
#print axioms declared_port_support_independent
#print axioms checkConflicts_sound
#print axioms build_sound
#print axioms accepted_lookup_iff
#print axioms accepted_entry_lookup
#print axioms absent_key
end Ash.OneShot.CoreOperationSignatures
