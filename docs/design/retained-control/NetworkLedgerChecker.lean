import NetworkLedgerCollections

/-
An initial restricted removal checker over explicit linked-body syntax and
fuel-bounded normal evaluation. This is one schema only; it is not the complete
CP-0028 checker or a proof of Rust/Core correspondence.
-/
namespace Ash.NetworkLedger.Checker

open Ash.NetworkLedger

inductive Comparator where
  | nominal | alwaysTrue
  deriving DecidableEq, Repr
inductive EmptyArm where
  | missing | found
  deriving DecidableEq, Repr
inductive HitArm where
  | tailFound | tailMissing
  deriving DecidableEq, Repr
inductive MissArm where
  | recurseTailKeep | recurseTailDrop | recurseWhole
  deriving DecidableEq, Repr

structure Body where
  comparator : Comparator
  empty : EmptyArm
  hit : HitArm
  miss : MissArm
  deriving DecidableEq, Repr

structure Definition where
  binder : Nat
  listNominal : Nat
  entryNominal : Nat
  keyProjection : Nat
  body : Body
  deriving DecidableEq, Repr

structure Plan where
  binder : Nat
  listNominal : Nat
  entryNominal : Nat
  keyProjection : Nat
  deriving DecidableEq, Repr

def acceptedBody : Body := ⟨.nominal, .missing, .tailFound, .recurseTailKeep⟩

def check (plan : Plan) (defn : Definition) : Bool :=
  decide (plan.binder = defn.binder ∧ plan.listNominal = defn.listNominal ∧
    plan.entryNominal = defn.entryNominal ∧ plan.keyProjection = defn.keyProjection ∧
    defn.body = acceptedBody)

/- Nomination selects exactly one actual definition in the modeled linked set. -/
def resolve (plan : Plan) (definitions : List Definition) : Option Definition :=
  match definitions.filter (fun defn ↦ defn.binder == plan.binder) with
  | [defn] => some defn
  | _ => none

def checkLinked (plan : Plan) (definitions : List Definition) : Bool :=
  match resolve plan definitions with
  | none => false
  | some defn => check plan defn

theorem linked_accepts_selected (plan : Plan) (definitions : List Definition)
    (accepted : checkLinked plan definitions = true) :
    ∃ defn, resolve plan definitions = some defn ∧ check plan defn = true := by
  unfold checkLinked at accepted
  cases found : resolve plan definitions with
  | none => simp [found] at accepted
  | some defn => exact ⟨defn, rfl, by simpa [found] using accepted⟩

def compare (mode : Comparator) (a b : Id) : Bool :=
  match mode with
  | .nominal => decide (a = b)
  | .alwaysTrue => true

variable {Entry : Type} (key : Entry → Id)

def eval (body : Body) (q : Id) : Nat → List Entry → Option (List Entry × Status)
  | 0, _ => none
  | fuel + 1, xs =>
    match xs with
    | [] => some ([], match body.empty with | .missing => .missing | .found => .found)
    | x :: tail =>
      if compare body.comparator (key x) q then
        some (tail, match body.hit with | .tailFound => .found | .tailMissing => .missing)
      else
        match body.miss with
        | .recurseTailKeep => (eval body q fuel tail).map (fun (ys, tag) ↦ (x :: ys, tag))
        | .recurseTailDrop => eval body q fuel tail
        | .recurseWhole => eval body q fuel xs

theorem accepted_bound (plan : Plan) (defn : Definition) (accepted : check plan defn = true) :
    plan.binder = defn.binder ∧ plan.listNominal = defn.listNominal ∧
    plan.entryNominal = defn.entryNominal ∧ plan.keyProjection = defn.keyProjection ∧
    defn.body = acceptedBody := by
  simpa [check] using accepted

theorem eval_accepted (q : Id) (fuel : Nat) (xs : List Entry) (result : List Entry × Status)
    (returns : eval key acceptedBody q fuel xs = some result) : result = remove key q xs := by
  induction fuel generalizing xs result with
  | zero => simp [eval] at returns
  | succ fuel ih =>
    cases xs with
    | nil => simpa [eval, acceptedBody, remove] using returns.symm
    | cons x tail =>
      by_cases equal : key x = q
      · simpa [eval, acceptedBody, compare, remove, equal] using returns.symm
      · simp only [eval, acceptedBody, compare, equal, decide_false, Bool.false_eq_true,
          ↓reduceIte] at returns
        change (eval key acceptedBody q fuel tail).map
          (fun pair ↦ (x :: pair.1, pair.2)) = some result at returns
        cases sub : eval key acceptedBody q fuel tail with
        | none => simp [sub] at returns
        | some pair =>
          have recurse := ih tail pair sub
          cases pair with
          | mk ys tag =>
            rw [sub] at returns
            simp only [Option.map_some, Option.some.injEq] at returns
            cases returns
            simp [remove, equal, ← recurse]

theorem remove_checker_returns (plan : Plan) (defn : Definition) (q : Id) (fuel : Nat)
    (xs : List Entry) (result : List Entry × Status) (accepted : check plan defn = true)
    (returns : eval key defn.body q fuel xs = some result) : result = remove key q xs := by
  have body := (accepted_bound plan defn accepted).2.2.2.2
  rw [body] at returns
  exact eval_accepted key q fuel xs result returns

theorem remove_checker_sound (plan : Plan) (defn : Definition) (q : Id) (fuel : Nat)
    (xs : List Entry) (result : List Entry × Status) (accepted : check plan defn = true)
    (returns : eval key defn.body q fuel xs = some result) :
    result.1 = erase key q xs ∧
    (result.2 = .found ↔ q ∈ xs.map key) ∧
    (result.2 = .missing ↔ q ∉ xs.map key) ∧
    List.Sublist result.1 xs ∧ (Unique key xs → Unique key result.1) := by
  have body := (accepted_bound plan defn accepted).2.2.2.2
  rw [body] at returns
  have value := eval_accepted key q fuel xs result returns
  rw [value]
  refine ⟨remove_sequence key q xs, remove_found_iff key q xs,
    remove_missing_iff key q xs, erase_retains_whole_order key q xs, ?_⟩
  intro unique
  rw [remove_sequence]
  exact erase_finite_unique key q xs unique

theorem linked_remove_sound (plan : Plan) (definitions : List Definition) (defn : Definition)
    (q : Id) (fuel : Nat) (xs : List Entry) (result : List Entry × Status)
    (accepted : checkLinked plan definitions = true)
    (resolved : resolve plan definitions = some defn)
    (returns : eval key defn.body q fuel xs = some result) :
    result.1 = erase key q xs ∧
    (result.2 = .found ↔ q ∈ xs.map key) ∧
    (result.2 = .missing ↔ q ∉ xs.map key) ∧
    List.Sublist result.1 xs ∧ (Unique key xs → Unique key result.1) := by
  have bodyChecked : check plan defn = true := by simpa [checkLinked, resolved] using accepted
  exact remove_checker_sound key plan defn q fuel xs result bodyChecked returns

inductive LookupHit where
  | returnHead | returnNone
  deriving DecidableEq, Repr
inductive LookupMiss where
  | recurseTail | returnNone | recurseWhole
  deriving DecidableEq, Repr
structure LookupBody where
  comparator : Comparator
  hit : LookupHit
  miss : LookupMiss
  deriving DecidableEq, Repr

def acceptedLookup : LookupBody := ⟨.nominal, .returnHead, .recurseTail⟩

def checkLookup (body : LookupBody) : Bool := decide (body = acceptedLookup)

def evalLookup (body : LookupBody) (q : Id) : Nat → List Entry → Option (Option Entry)
  | 0, _ => none
  | fuel + 1, xs =>
    match xs with
    | [] => some none
    | x :: tail =>
      if compare body.comparator (key x) q then
        match body.hit with
        | .returnHead => some (some x)
        | .returnNone => some none
      else
        match body.miss with
        | .recurseTail => evalLookup body q fuel tail
        | .returnNone => some none
        | .recurseWhole => evalLookup body q fuel xs

theorem eval_lookup_accepted (q : Id) (fuel : Nat) (xs : List Entry) (result : Option Entry)
    (returns : evalLookup key acceptedLookup q fuel xs = some result) :
    result = lookup key q xs := by
  induction fuel generalizing xs result with
  | zero => simp [evalLookup] at returns
  | succ fuel ih =>
    cases xs with
    | nil => simpa [evalLookup, lookup] using returns.symm
    | cons x tail =>
      by_cases equal : key x = q
      · simpa [evalLookup, acceptedLookup, compare, lookup, equal] using returns.symm
      · simp only [evalLookup, acceptedLookup, compare, equal, decide_false, Bool.false_eq_true,
          ↓reduceIte] at returns
        have recursive : evalLookup key acceptedLookup q fuel tail = some result := returns
        simpa [lookup, equal] using ih tail result recursive

theorem lookup_checker_sound (body : LookupBody) (q : Id) (fuel : Nat) (xs : List Entry)
    (result : Option Entry) (accepted : checkLookup body = true)
    (returns : evalLookup key body q fuel xs = some result) : result = lookup key q xs := by
  have same : body = acceptedLookup := by simpa [checkLookup] using accepted
  rw [same] at returns
  exact eval_lookup_accepted key q fuel xs result returns

inductive InsertBody where
  | appendOne | prependOne
  deriving DecidableEq, Repr

def checkInsert (body : InsertBody) : Bool := decide (body = .appendOne)

def evalInsert (body : InsertBody) (entry : Entry) (xs : List Entry) : List Entry :=
  match body with
  | .appendOne => xs ++ [entry]
  | .prependOne => entry :: xs

theorem insert_checker_sound (body : InsertBody) (entry : Entry) (xs : List Entry)
    (accepted : checkInsert body = true) : evalInsert body entry xs = insert entry xs := by
  have same : body = .appendOne := by simpa [checkInsert] using accepted
  subst body
  rfl

inductive UpdateHit where
  | replace | retain
  deriving DecidableEq, Repr
inductive UpdateMiss where
  | recurseTailKeep | recurseTailDrop | recurseWhole
  deriving DecidableEq, Repr
structure UpdateBody where
  comparator : Comparator
  hit : UpdateHit
  miss : UpdateMiss
  deriving DecidableEq, Repr

def acceptedUpdate : UpdateBody := ⟨.nominal, .replace, .recurseTailKeep⟩
def checkUpdate (body : UpdateBody) : Bool := decide (body = acceptedUpdate)

def evalUpdate (body : UpdateBody) (q : Id) (replacement : Entry) :
    Nat → List Entry → Option (List Entry)
  | 0, _ => none
  | fuel + 1, xs =>
    match xs with
    | [] => some []
    | x :: tail =>
      if compare body.comparator (key x) q then
        match body.hit with
        | .replace => some (replacement :: tail)
        | .retain => some (x :: tail)
      else
        match body.miss with
        | .recurseTailKeep => (evalUpdate body q replacement fuel tail).map (fun ys ↦ x :: ys)
        | .recurseTailDrop => evalUpdate body q replacement fuel tail
        | .recurseWhole => evalUpdate body q replacement fuel xs

theorem eval_update_accepted (q : Id) (replacement : Entry) (fuel : Nat) (xs : List Entry)
    (result : List Entry) (returns : evalUpdate key acceptedUpdate q replacement fuel xs = some result) :
    result = update key q replacement xs := by
  induction fuel generalizing xs result with
  | zero => simp [evalUpdate] at returns
  | succ fuel ih =>
    cases xs with
    | nil => simpa [evalUpdate, update] using returns.symm
    | cons x tail =>
      by_cases equal : key x = q
      · simpa [evalUpdate, acceptedUpdate, compare, update, equal] using returns.symm
      · simp only [evalUpdate, acceptedUpdate, compare, equal, decide_false, Bool.false_eq_true,
          ↓reduceIte] at returns
        change (evalUpdate key acceptedUpdate q replacement fuel tail).map (fun ys ↦ x :: ys) =
          some result at returns
        cases sub : evalUpdate key acceptedUpdate q replacement fuel tail with
        | none => simp [sub] at returns
        | some ys =>
          have recurse := ih tail ys sub
          rw [sub] at returns
          simp only [Option.map_some, Option.some.injEq] at returns
          cases returns
          simp [update, equal, ← recurse]

theorem update_checker_sound (body : UpdateBody) (q : Id) (replacement : Entry) (fuel : Nat)
    (xs : List Entry) (result : List Entry) (accepted : checkUpdate body = true)
    (returns : evalUpdate key body q replacement fuel xs = some result) :
    result = update key q replacement xs := by
  have same : body = acceptedUpdate := by simpa [checkUpdate] using accepted
  rw [same] at returns
  exact eval_update_accepted key q replacement fuel xs result returns

def checkComparator (mode : Comparator) : Bool := decide (mode = .nominal)

theorem comparator_checker_sound (mode : Comparator) (a b : Id)
    (accepted : checkComparator mode = true) : (compare mode a b = true ↔ a = b) := by
  have same : mode = .nominal := by simpa [checkComparator] using accepted
  subst mode
  simp [compare]

/- Dependency ranks are supplied by discovery but checked at each edge. They
   bound ordinary dependency recursion; self-induction is a different rule. -/
structure Dependency where
  rank : Nat
  helpers : List Nat
  deriving Repr

def checkDependencies (dep : Dependency) : Bool := dep.helpers.all (fun rank ↦ rank < dep.rank)

theorem dependency_decreases (dep : Dependency) (helper : Nat)
    (checked : checkDependencies dep = true) (member : helper ∈ dep.helpers) : helper < dep.rank := by
  have all := List.all_eq_true.mp checked
  exact of_decide_eq_true (all helper member)

theorem dependency_no_two_cycle (a b : Dependency) (ab : b.rank ∈ a.helpers)
    (ba : a.rank ∈ b.helpers) (aChecked : checkDependencies a = true)
    (bChecked : checkDependencies b = true) : False := by
  have first := dependency_decreases a b.rank aChecked ab
  have second := dependency_decreases b a.rank bChecked ba
  omega

/- The registry rule is shared by other modeled schema checkers. It resolves
   exactly one candidate, validates its metadata and then checks its body. -/
structure LinkedDefinition (Body : Type) where
  binder : Nat
  listNominal : Nat
  entryNominal : Nat
  keyProjection : Nat
  body : Body

def resolveLinked {Body : Type} (plan : Plan) (definitions : List (LinkedDefinition Body)) :
    Option (LinkedDefinition Body) :=
  match definitions.filter (fun defn ↦ defn.binder == plan.binder) with
  | [defn] => some defn
  | _ => none

def checkLinkedSchema {Body : Type} (plan : Plan) (definitions : List (LinkedDefinition Body))
    (checkBody : Body → Bool) : Bool :=
  match resolveLinked plan definitions with
  | none => false
  | some defn =>
    decide (plan.binder = defn.binder ∧ plan.listNominal = defn.listNominal ∧
      plan.entryNominal = defn.entryNominal ∧ plan.keyProjection = defn.keyProjection) &&
      checkBody defn.body

theorem linked_schema_binding {Body : Type} (plan : Plan) (definitions : List (LinkedDefinition Body))
    (checkBody : Body → Bool) (defn : LinkedDefinition Body)
    (accepted : checkLinkedSchema plan definitions checkBody = true)
    (resolved : resolveLinked plan definitions = some defn) :
    plan.binder = defn.binder ∧ plan.listNominal = defn.listNominal ∧
      plan.entryNominal = defn.entryNominal ∧ plan.keyProjection = defn.keyProjection ∧
      checkBody defn.body = true := by
  simpa [checkLinkedSchema, resolved, and_assoc] using accepted

theorem linked_schema_sound {Body : Type} (plan : Plan) (definitions : List (LinkedDefinition Body))
    (checkBody : Body → Bool) (spec : Body → Prop)
    (bodySound : ∀ body, checkBody body = true → spec body)
    (defn : LinkedDefinition Body) (accepted : checkLinkedSchema plan definitions checkBody = true)
    (resolved : resolveLinked plan definitions = some defn) : spec defn.body := by
  exact bodySound defn.body (linked_schema_binding plan definitions checkBody defn accepted resolved).2.2.2.2

inductive DependencyPath : Nat → Nat → Prop where
  | edge (dep : Dependency) (helper : Nat) (checked : checkDependencies dep = true)
      (member : helper ∈ dep.helpers) : DependencyPath dep.rank helper
  | next {source middle target : Nat} :
      DependencyPath source middle → DependencyPath middle target → DependencyPath source target

theorem dependency_path_decreases {source target : Nat} (path : DependencyPath source target) :
    target < source := by
  induction path with
  | edge dep helper checked member => exact dependency_decreases dep helper checked member
  | next _ _ ihLeft ihRight => omega

theorem dependency_no_cycle (rank : Nat) (path : DependencyPath rank rank) : False := by
  have decreasing := dependency_path_decreases path
  omega

end Ash.NetworkLedger.Checker
