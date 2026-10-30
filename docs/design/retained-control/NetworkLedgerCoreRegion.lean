import NetworkLedgerCoreStrict

/-
Restricted operational region state for the checked default provider. Context
queries and allocation requests each resume once on success, but the older
allocation model counts only allocation resumptions. The projection below keeps
those counters distinct. These functions describe the selected host path; the
actual linked caller and interpreter correspondence still have to establish
that this path is selected and cannot be reentered.
-/
namespace Ash.NetworkLedger.CoreRegion

open Ash.NetworkLedger.Allocation
open Ash.NetworkLedger.CoreRemoval

structure State (Value : Type) where
  protocolVersion : Nat
  nextLocation : Nat
  allocationResumes : Nat
  queryResumes : Nat
  pending : List (Nat × Nat)
  cells : List (Nat × List Value)
  recursivePending : List Nat
  aliases : List (Nat × Nat)

def project {Value : Type} (s : State Value) : Allocation.State :=
  { protocolVersion := s.protocolVersion
    nextLocation := s.nextLocation
    continuationResumes := s.allocationResumes }

/-- A successful Unit context request resumes its caller once. -/
def query {Value : Type} (selected : Selection) (s : State Value) : Option (Selection × State Value) :=
  match selected with
  | .hostDefault => some (.hostDefault, { s with queryResumes := s.queryResumes + 1 })
  | .intercepted | .localProvider | .unknown => none

/-- The host allocation records a fresh pending location; refusal has no return. -/
def allocate {Value : Type} (selected : Selection) (fields : Nat) (available : Bool)
    (s : State Value) : Option (Nat × State Value) :=
  if !available then none
  else match selected with
    | .hostDefault => some (s.nextLocation,
        { s with nextLocation := s.nextLocation + 1
                 allocationResumes := s.allocationResumes + 1
                 pending := (s.nextLocation, fields) :: s.pending })
    | .intercepted | .localProvider | .unknown => none

/-- Initialization consumes the exact pending storage and records whole fields. -/
def initializeStorage {Value : Type} (location fields : Nat) (values : List Value)
    (s : State Value) : Option (List Value × State Value) :=
  if values.length = fields ∧ (location, fields) ∈ s.pending then
    some (values, { s with pending := s.pending.erase (location, fields)
                           cells := (location, values) :: s.cells })
  else none

/-- Reserve the heap slot used by an ordinary recursive binding. -/
def reserveRecursive {Value : Type} (s : State Value) : Nat × State Value :=
  (s.nextLocation, { s with nextLocation := s.nextLocation + 1
                            recursivePending := s.nextLocation :: s.recursivePending })

/-- Completing a recursive initializer installs an alias at its reserved slot. -/
def initializeAlias {Value : Type} (slot target : Nat) (s : State Value) : Option (State Value) :=
  if slot ∈ s.recursivePending then
    some { s with recursivePending := s.recursivePending.erase slot
                  aliases := (slot, target) :: s.aliases }
  else none

/-- Query resumption is invisible only to the older allocation-only projection. -/
theorem query_projects {Value : Type} (s out : State Value) (selected chosen : Selection)
    (returns : query selected s = some (chosen, out)) :
    chosen = .hostDefault ∧ project out = project s ∧
      out.queryResumes = s.queryResumes + 1 ∧ out.pending = s.pending ∧ out.cells = s.cells := by
  cases selected with
  | hostDefault =>
    simp only [query, Option.some.injEq, Prod.mk.injEq] at returns
    rcases returns with ⟨rfl, rfl⟩
    simp [project]
  | intercepted => simp [query] at returns
  | localProvider => simp [query] at returns
  | unknown => simp [query] at returns

/-- The actual query step maps to the allocation model's state-preserving view. -/
theorem query_corresponds {Value : Type} (s out : State Value) (selected chosen : Selection)
    (returns : query selected s = some (chosen, out)) :
    Query .hostDefault (project s) chosen (project out) := by
  have result := query_projects s out selected chosen returns
  rcases result with ⟨rfl, same, _⟩
  rw [same]
  exact Query.host (project s)

/-- Successful host allocation matches the older allocation-only model. -/
theorem allocation_projects {Value : Type} (s out : State Value) (selected : Selection)
    (fields : Nat) (available : Bool) (location : Nat)
    (returns : allocate selected fields available s = some (location, out)) :
    execute selected (project s) available = .returned location (project out) ∧
      out.queryResumes = s.queryResumes ∧ out.pending = (location, fields) :: s.pending ∧
      out.cells = s.cells := by
  cases available with
  | false => simp [allocate] at returns
  | true =>
    cases selected with
    | hostDefault =>
      simp only [allocate, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        Option.some.injEq, Prod.mk.injEq] at returns
      rcases returns with ⟨rfl, rfl⟩
      simp [execute, project]
    | intercepted => simp [allocate] at returns
    | localProvider => simp [allocate] at returns
    | unknown => simp [allocate] at returns

/-- Existing live storage and cells lie below the fresh-location counter. -/
def BoundedLocations {Value : Type} (s : State Value) : Prop :=
  (∀ location fields, (location, fields) ∈ s.pending → location < s.nextLocation) ∧
  (∀ location values, (location, values) ∈ s.cells → location < s.nextLocation) ∧
  (∀ location, location ∈ s.recursivePending → location < s.nextLocation) ∧
  (∀ location target, (location, target) ∈ s.aliases → location < s.nextLocation)

/-- A successful query preserves the live-location bound. -/
theorem query_preserves_bounded {Value : Type} (s out : State Value) (selected chosen : Selection)
    (bounded : BoundedLocations s)
    (returns : query selected s = some (chosen, out)) : BoundedLocations out := by
  cases selected with
  | hostDefault =>
    simp only [query, Option.some.injEq, Prod.mk.injEq] at returns
    rcases returns with ⟨rfl, rfl⟩
    exact bounded
  | intercepted => simp [query] at returns
  | localProvider => simp [query] at returns
  | unknown => simp [query] at returns

/-- A successful allocation extends the live-location bound. -/
theorem allocation_preserves_bounded {Value : Type} (s out : State Value) (selected : Selection)
    (fields : Nat) (available : Bool) (location : Nat) (bounded : BoundedLocations s)
    (returns : allocate selected fields available s = some (location, out)) : BoundedLocations out := by
  cases available with
  | false => simp [allocate] at returns
  | true =>
    cases selected with
    | hostDefault =>
      simp only [allocate, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        Option.some.injEq, Prod.mk.injEq] at returns
      rcases returns with ⟨rfl, rfl⟩
      rcases bounded with ⟨pending, cells, recursive, aliases⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro loc count member
        change loc < s.nextLocation + 1
        simp only [List.mem_cons, Prod.mk.injEq] at member
        rcases member with ⟨rfl, rfl⟩ | old
        · omega
        · have := pending loc count old
          omega
      · intro loc values member
        change loc < s.nextLocation + 1
        have := cells loc values member
        omega
      · intro loc member
        change loc < s.nextLocation + 1
        have := recursive loc member
        omega
      · intro loc target member
        change loc < s.nextLocation + 1
        have := aliases loc target member
        omega
    | intercepted => simp [allocate] at returns
    | localProvider => simp [allocate] at returns
    | unknown => simp [allocate] at returns

/-- Storage initialization keeps every live location below the counter. -/
theorem initialization_preserves_bounded {Value : Type} (s out : State Value)
    (location fields : Nat) (values actual : List Value) (bounded : BoundedLocations s)
    (returns : initializeStorage location fields values s = some (actual, out)) : BoundedLocations out := by
  by_cases accepted : values.length = fields ∧ (location, fields) ∈ s.pending
  · simp only [initializeStorage, if_pos accepted, Option.some.injEq, Prod.mk.injEq] at returns
    rcases returns with ⟨rfl, rfl⟩
    rcases bounded with ⟨pending, cells, recursive, aliases⟩
    refine ⟨?_, ?_, recursive, aliases⟩
    · intro loc count member
      exact pending loc count (List.mem_of_mem_erase member)
    · intro loc contents member
      simp only [List.mem_cons, Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩ | old
      · exact pending loc fields accepted.2
      · exact cells loc contents old
  · simp [initializeStorage, accepted] at returns

/-- Reserving a recursive slot extends the live-location bound. -/
theorem recursive_reservation_preserves_bounded {Value : Type} (s : State Value)
    (bounded : BoundedLocations s) : BoundedLocations (reserveRecursive s).2 := by
  rcases bounded with ⟨pending, cells, recursive, aliases⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro loc fields member
    have := pending loc fields member
    simp only [reserveRecursive]
    omega
  · intro loc contents member
    have := cells loc contents member
    simp only [reserveRecursive]
    omega
  · intro loc member
    simp only [reserveRecursive, List.mem_cons] at member ⊢
    rcases member with rfl | old
    · omega
    · have := recursive loc old
      omega
  · intro loc target member
    have := aliases loc target member
    simp only [reserveRecursive]
    omega

/-- Installing a reserved recursive alias preserves the live-location bound. -/
theorem alias_initialization_preserves_bounded {Value : Type} (s out : State Value)
    (slot target : Nat) (bounded : BoundedLocations s)
    (returns : initializeAlias slot target s = some out) : BoundedLocations out := by
  by_cases present : slot ∈ s.recursivePending
  · simp only [initializeAlias, if_pos present, Option.some.injEq] at returns
    subst out
    rcases bounded with ⟨pending, cells, recursive, aliases⟩
    refine ⟨pending, cells, ?_, ?_⟩
    · intro loc member
      exact recursive loc (List.mem_of_mem_erase member)
    · intro loc destination member
      simp only [List.mem_cons, Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl⟩ | old
      · exact recursive loc present
      · exact aliases loc destination old
  · simp [initializeAlias, present] at returns

/-- Under the live-store invariant a returned location has never been used. -/
theorem allocation_fresh {Value : Type} (s out : State Value) (selected : Selection)
    (fields : Nat) (available : Bool) (location : Nat)
    (bounded : BoundedLocations s)
    (returns : allocate selected fields available s = some (location, out)) :
    (∀ oldFields, (location, oldFields) ∉ s.pending) ∧
      (∀ oldValues, (location, oldValues) ∉ s.cells) := by
  have same : location = s.nextLocation := by
    cases selected <;> cases available <;> simp_all [allocate]
  subst location
  constructor
  · intro oldFields present
    have less := bounded.1 s.nextLocation oldFields present
    omega
  · intro oldValues present
    have less := bounded.2.1 s.nextLocation oldValues present
    omega

/-- Refusal cannot produce a normal allocation result. -/
theorem allocation_refuses {Value : Type} (s : State Value) (selected : Selection) (fields : Nat) :
    allocate selected fields false s = none := by
  simp [allocate]

/-- Initialization stores the exact fields, without changing either resume count. -/
theorem initialization_preserves {Value : Type} (s out : State Value)
    (location fields : Nat) (values actual : List Value)
    (returns : initializeStorage location fields values s = some (actual, out)) :
    actual = values ∧ out.cells = (location, values) :: s.cells ∧
      project out = project s ∧ out.queryResumes = s.queryResumes := by
  simp only [initializeStorage] at returns
  split at returns
  · simp only [Option.some.injEq, Prod.mk.injEq] at returns
    rcases returns with ⟨rfl, rfl⟩
    simp [project]
  · simp_all

end Ash.NetworkLedger.CoreRegion
