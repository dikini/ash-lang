import Ownership


/-
Bounded C3 work and port projection. The concrete pair distinguishes the
current root from other unfinished work; it is not an evaluator representation.
Facts are indexed by bounded actual ports. The compiler correspondence must
establish the remaining premises for its selected paths and solver closure.
-/
namespace Ash.RetainedControl.PortCases

inductive Work where
  | empty | activeOnly | pending | unknown
  deriving DecidableEq, Repr

structure ConcreteWork where
  active : Bool
  other : Bool
  deriving DecidableEq, Repr

def Work.allows (work : Work) (actual : ConcreteWork) : Prop :=
  match work with
  | .empty => actual.active = false ∧ actual.other = false
  | .activeOnly => actual.active = true ∧ actual.other = false
  | .pending => actual.other = true
  | .unknown => True

def ConcreteWork.quiet (actual : ConcreteWork) : Bool :=
  !(actual.active || actual.other)

def Work.enterRoot : Work → Work
  | .empty => .activeOnly
  | .pending => .pending
  | .activeOnly | .unknown => .unknown

def ConcreteWork.enterRoot (actual : ConcreteWork) : ConcreteWork :=
  ⟨true, actual.active || actual.other⟩

theorem enter_root_sound {work : Work} {actual : ConcreteWork}
    (sound : work.allows actual) : work.enterRoot.allows actual.enterRoot := by
  cases work <;> cases actual with
  | mk active other => cases active <;> cases other <;>
      simp_all [Work.allows, Work.enterRoot, ConcreteWork.enterRoot]

def Work.finishRoot : Work → Work
  | .activeOnly => .empty
  | other => other

def ConcreteWork.finishRoot (actual : ConcreteWork) : ConcreteWork :=
  ⟨false, actual.other⟩

theorem finish_root_sound {work : Work} {actual : ConcreteWork}
    (sound : work.allows actual) (running : actual.active = true) :
    work.finishRoot.allows actual.finishRoot := by
  cases work <;> cases actual with
  | mk active other => cases active <;> cases other <;>
      simp_all [Work.allows, Work.finishRoot, ConcreteWork.finishRoot]

def ConcreteWork.retain (actual : ConcreteWork) : ConcreteWork :=
  { actual with other := true }

theorem retain_sound (actual : ConcreteWork) : Work.pending.allows actual.retain := by
  simp [Work.allows, ConcreteWork.retain]

def Work.probeMay (work : Work) (answer : Bool) : Prop :=
  match work with
  | .empty => answer = true
  | .activeOnly | .pending => answer = false
  | .unknown => True

def Work.afterProbe (answer : Bool) : Work := if answer then .empty else .pending

theorem selected_probe_sound {work : Work} {actual : ConcreteWork}
    (sound : work.allows actual) (driver : actual.active = false) :
    work.probeMay actual.quiet ∧ (Work.afterProbe actual.quiet).allows actual := by
  cases work <;> cases actual with
  | mk active other => cases active <;> cases other <;>
      simp_all [Work.allows, Work.probeMay, Work.afterProbe, ConcreteWork.quiet]

inductive Case (constructors : Nat) where
  | boolean (value : Bool)
  | constructor (name : Fin constructors)
  | tuple
  deriving DecidableEq, Repr

structure CaseFact (ports constructors : Nat) where
  value : Case constructors
  fresh : Bool
  origin : Option (Fin ports)
  deriving DecidableEq, Repr

structure ConcretePort (ports constructors : Nat) where
  value : Case constructors
  origin : Option (Fin ports)
  deriving DecidableEq, Repr

abbrev Facts (ports constructors : Nat) := Fin ports → Option (CaseFact ports constructors)
abbrev Values (ports constructors : Nat) := Fin ports → ConcretePort ports constructors

def agrees {ports constructors : Nat} (facts : Facts ports constructors)
    (values : Values ports constructors) (work : ConcreteWork) : Prop :=
  ∀ port fact, facts port = some fact →
    fact.value = (values port).value ∧
    (fact.origin = none ∨ fact.origin = (values port).origin) ∧
    (fact.fresh = true → fact.value = .boolean work.quiet)

def assign {ports : Nat} {α : Type} (values : Fin ports → α) (port : Fin ports)
    (value : α) : Fin ports → α := fun index ↦ if index = port then value else values index

theorem copy_fact_sound {ports constructors : Nat} {facts : Facts ports constructors}
    {values : Values ports constructors} {work : ConcreteWork} (sound : agrees facts values work)
    (source target : Fin ports) :
    agrees (assign facts target (facts source)) (assign values target (values source)) work := by
  intro port fact present
  by_cases equal : port = target
  · subst port
    simpa [assign] using sound source fact (by simpa [assign] using present)
  · have factSound := sound port fact (by simpa [assign, equal] using present)
    simpa [assign, equal] using factSound

def clearFresh {ports constructors : Nat} (facts : Facts ports constructors) :
    Facts ports constructors :=
  fun port ↦ (facts port).map fun fact ↦ { fact with fresh := false }

theorem mutation_expires_probe_facts {ports constructors : Nat}
    {facts : Facts ports constructors} {values : Values ports constructors}
    {before after : ConcreteWork} (sound : agrees facts values before) :
    agrees (clearFresh facts) values after := by
  intro port fact present
  cases prior : facts port with
  | none => simp [clearFresh, prior] at present
  | some original =>
      have originalSound := sound port original prior
      simp [clearFresh, prior] at present
      subst fact
      constructor
      · exact originalSound.1
      constructor
      · exact originalSound.2.1
      · intro impossible
        contradiction

theorem forget_facts_sound {ports constructors : Nat} (values : Values ports constructors)
    (work : ConcreteWork) : agrees (fun _ ↦ none) values work := by
  intro port fact impossible
  contradiction


def probeFact {ports constructors : Nat} (answer : Bool) : CaseFact ports constructors :=
  ⟨.boolean answer, true, none⟩

def probeValue {ports constructors : Nat} (answer : Bool) : ConcretePort ports constructors :=
  ⟨.boolean answer, none⟩

theorem selected_probe_port_sound {ports constructors : Nat}
    {facts : Facts ports constructors} {values : Values ports constructors}
    {work : ConcreteWork} (sound : agrees facts values work) (port : Fin ports) :
    agrees (assign facts port (some (probeFact work.quiet)))
      (assign values port (probeValue work.quiet)) work := by
  intro index fact present
  by_cases equal : index = port
  · subst index
    simp [assign, probeFact, probeValue] at present ⊢
    subst fact
    simp
  · have original := sound index fact (by simpa [assign, equal] using present)
    simpa [assign, equal] using original

def withoutOrigin {ports constructors : Nat} (fact : CaseFact ports constructors) :
    CaseFact ports constructors := { fact with origin := none }

def forgetOrigins {ports constructors : Nat} (facts : Facts ports constructors) :
    Facts ports constructors := fun port ↦ (facts port).map withoutOrigin

theorem forget_origins_sound {ports constructors : Nat}
    {facts : Facts ports constructors} {values : Values ports constructors}
    {work : ConcreteWork} (sound : agrees facts values work) :
    agrees (forgetOrigins facts) values work := by
  intro port fact present
  cases prior : facts port with
  | none => simp [forgetOrigins, prior] at present
  | some original =>
      have originalSound := sound port original prior
      simp [forgetOrigins, prior, withoutOrigin] at present
      subst fact
      exact ⟨originalSound.1, Or.inl rfl, originalSound.2.2⟩

theorem selected_probe_forget_origins_sound {ports constructors : Nat}
    {facts : Facts ports constructors} {values : Values ports constructors}
    {work : ConcreteWork} (sound : agrees facts values work) (port : Fin ports) :
    agrees (assign (forgetOrigins facts) port (some (probeFact work.quiet)))
      (assign values port (probeValue work.quiet)) work :=
  selected_probe_port_sound (forget_origins_sound sound) port

theorem forget_origin_sound {ports constructors : Nat}
    {facts : Facts ports constructors} {values : Values ports constructors}
    {work : ConcreteWork} (sound : agrees facts values work) (port : Fin ports) :
    agrees (assign facts port ((facts port).map withoutOrigin)) values work := by
  intro index fact present
  by_cases equal : index = port
  · subst index
    cases previous : facts port with
    | none => simp [assign, previous] at present
    | some original =>
        have originalSound := sound port original previous
        simp [assign, previous, withoutOrigin] at present
        subst fact
        exact ⟨originalSound.1, Or.inl rfl, originalSound.2.2⟩
  · exact sound index fact (by simpa [assign, equal] using present)


theorem case_construction_sound {ports constructors : Nat}
    {facts : Facts ports constructors} {values : Values ports constructors}
    {work : ConcreteWork} (sound : agrees facts values work) (port : Fin ports)
    (value : Case constructors) (origin : Option (Fin ports)) :
    agrees (assign facts port (some ⟨value, false, origin⟩))
      (assign values port ⟨value, origin⟩) work := by
  intro index fact present
  by_cases equal : index = port
  · subst index
    simp [assign] at present ⊢
    subst fact
    simp
  · have original := sound index fact (by simpa [assign, equal] using present)
    simpa [assign, equal] using original

theorem copied_result_without_origin_sound {ports constructors : Nat}
    {facts : Facts ports constructors} {values : Values ports constructors}
    {work : ConcreteWork} (sound : agrees facts values work) (source target : Fin ports) :
    agrees (assign (fun _ ↦ none) target ((facts source).map withoutOrigin))
      (assign values target (values source)) work := by
  intro index fact present
  by_cases equal : index = target
  · subst index
    cases prior : facts source with
    | none => simp [assign, prior] at present
    | some original =>
        have originalSound := sound source original prior
        simp [assign, prior, withoutOrigin] at present
        subst fact
        simp only [assign]
        exact ⟨originalSound.1, Or.inl trivial, originalSound.2.2⟩
  · simp [assign, equal] at present

inductive Pattern (constructors : Nat) where
  | any | opaque | test (expected : Case constructors) (total : Bool)
  deriving DecidableEq, Repr

def Pattern.mayMatch {constructors : Nat} (pattern : Pattern constructors)
    (actual : Case constructors) : Prop :=
  match pattern with
  | .any | .opaque => True
  | .test expected _ => expected = actual

def Pattern.decision {constructors : Nat} (pattern : Pattern constructors)
    (known : Option (Case constructors)) : Bool × Bool :=
  match pattern, known with
  | .any, _ => (true, true)
  | .opaque, _ => (true, false)
  | .test _ _, none => (true, false)
  | .test expected total, some actual =>
      (decide (expected = actual), decide (expected = actual) && total)

theorem ordered_case_keeps_matching_arm {constructors : Nat}
    (pattern : Pattern constructors) (actual : Case constructors)
    (known : Option (Case constructors)) (valid : known = none ∨ known = some actual)
    (compatible : pattern.mayMatch actual) : (pattern.decision known).1 = true := by
  cases pattern <;> cases known <;> simp_all [Pattern.mayMatch, Pattern.decision]

theorem decisive_case_matches {constructors : Nat}
    (pattern : Pattern constructors) (actual : Case constructors)
    (known : Option (Case constructors)) (valid : known = none ∨ known = some actual)
    (decisive : (pattern.decision known).2 = true) : pattern.mayMatch actual := by
  cases pattern <;> cases known <;> simp_all [Pattern.mayMatch, Pattern.decision]


def Pattern.actualMatches {constructors : Nat} (pattern : Pattern constructors)
    (actual : Case constructors) (payloadMatches : Bool) : Prop :=
  match pattern with
  | .any => True
  | .opaque => payloadMatches = true
  | .test expected total => expected = actual ∧ (total = true ∨ payloadMatches = true)

theorem actual_match_is_possible {constructors : Nat} (pattern : Pattern constructors)
    (actual : Case constructors) (payloadMatches : Bool)
    (matched : pattern.actualMatches actual payloadMatches) : pattern.mayMatch actual := by
  cases pattern <;> simp_all [Pattern.actualMatches, Pattern.mayMatch]

theorem decisive_case_actually_matches {constructors : Nat}
    (pattern : Pattern constructors) (actual : Case constructors) (payloadMatches : Bool)
    (known : Option (Case constructors)) (valid : known = none ∨ known = some actual)
    (decisive : (pattern.decision known).2 = true) :
    pattern.actualMatches actual payloadMatches := by
  cases pattern <;> cases known <;>
    simp_all [Pattern.actualMatches, Pattern.decision]

/-- A real ordered arm is never removed by a known or unknown case. -/
theorem ordered_selection_sound {constructors : Nat}
    (before : List (Pattern constructors × Bool)) (chosen : Pattern constructors × Bool)
    (actual : Case constructors) (known : Option (Case constructors))
    (valid : known = none ∨ known = some actual)
    (earlier : ∀ entry ∈ before, ¬ entry.1.actualMatches actual entry.2)
    (matched : chosen.1.actualMatches actual chosen.2) :
    (chosen.1.decision known).1 = true ∧
      ∀ entry ∈ before, (entry.1.decision known).2 = false := by
  constructor
  · exact ordered_case_keeps_matching_arm chosen.1 actual known valid
      (actual_match_is_possible chosen.1 actual chosen.2 matched)
  · intro entry member
    cases decisive : (entry.1.decision known).2 with
    | false => rfl
    | true =>
        exact False.elim (earlier entry member
          (decisive_case_actually_matches entry.1 actual entry.2 known valid decisive))

#print axioms Ash.RetainedControl.PortCases.enter_root_sound
#print axioms Ash.RetainedControl.PortCases.finish_root_sound
#print axioms Ash.RetainedControl.PortCases.retain_sound
#print axioms Ash.RetainedControl.PortCases.selected_probe_sound
#print axioms Ash.RetainedControl.PortCases.mutation_expires_probe_facts
#print axioms Ash.RetainedControl.PortCases.case_construction_sound
#print axioms Ash.RetainedControl.PortCases.forget_facts_sound
#print axioms Ash.RetainedControl.PortCases.forget_origins_sound
#print axioms Ash.RetainedControl.PortCases.selected_probe_forget_origins_sound
#print axioms Ash.RetainedControl.PortCases.ordered_selection_sound


structure Projection (ports constructors : Nat) where
  work : Work
  facts : Facts ports constructors

end Ash.RetainedControl.PortCases


/- Local correspondence between the retained C1 ownership model and the
concrete work view. It says nothing about abstract slot addresses or Rust
solver states; their correspondence remains a separate obligation. -/
namespace Ash.RetainedControl.PortCases

open Ash.RetainedControl

def slotHasCapture (slot : Slot) : Bool :=
  match slot.phase with
  | .live _ => true
  | _ => false

def c1Work (state : State) : ConcreteWork :=
  ⟨state.active.isSome || state.clause.isSome, state.slots.any slotHasCapture⟩

theorem c1_quiet_has_no_work (state : State) (quiet : (c1Work state).quiet = true) :
    NoWork state := by
  have activeNone : state.active = none := by
    cases found : state.active with
    | none => rfl
    | some value => simp [ConcreteWork.quiet, c1Work, found] at quiet
  have clauseNone : state.clause = none := by
    cases found : state.clause with
    | none => rfl
    | some value => simp [ConcreteWork.quiet, c1Work, found] at quiet
  have noSlots : state.slots.any slotHasCapture = false := by
    cases found : state.slots.any slotHasCapture with
    | false => rfl
    | true => simp [ConcreteWork.quiet, c1Work, found] at quiet
  have slotOwnersEmpty : state.slots.flatMap slotOwners = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro slot member
    have absent := (List.any_eq_false.mp noSlots) slot member
    cases phase : slot.phase <;> simp_all [slotHasCapture, slotOwners]
  simp [NoWork, liveOwners, optionOwners, activeNone, clauseNone, slotOwnersEmpty]

theorem c1_no_work_is_quiet (state : State) (safe : ContextSafe state) (empty : NoWork state) :
    (c1Work state).quiet = true := by
  have activeNone : state.active = none := by
    cases found : state.active with
    | none => rfl
    | some value =>
        rcases value with ⟨capture, consumer⟩
        exact False.elim ((no_work_excludes_active state safe empty capture consumer) found)
  have clauseNone : state.clause = none := by
    cases found : state.clause with
    | none => rfl
    | some value =>
        rcases value with ⟨capture, consumer⟩
        exact False.elim ((no_work_excludes_clause state safe empty capture consumer) found)
  have noSlots : state.slots.any slotHasCapture = false := by
    apply List.any_eq_false.mpr
    intro slot member live
    cases phase : slot.phase with
    | vacant => simp [slotHasCapture, phase] at live
    | spent => simp [slotHasCapture, phase] at live
    | live capture => exact (no_work_excludes_slot state safe empty slot member capture) phase
  simp [ConcreteWork.quiet, c1Work, activeNone, clauseNone, noSlots]


def ActiveClauseSeparate (state : State) : Prop :=
  state.active = none ∨ state.clause = none

theorem c1_step_preserves_active_clause_separation {start finish : State} {created : List Nat}
    (step : Step start created finish) (separate : ActiveClauseSeparate start) :
    ActiveClauseSeparate finish := by
  cases step <;> simp_all [ActiveClauseSeparate]

theorem c1_launch_matches_root_entry (state : State) (capture : Capture) (consumer : Consumer)
    (noActive : state.active = none) (noClause : state.clause = none) :
    c1Work { state with active := some (capture, consumer), result := none } =
      (c1Work state).enterRoot := by
  simp [c1Work, ConcreteWork.enterRoot, noActive, noClause]

theorem c1_checkpoint_preserves_work (state : State) (capture : Capture) (consumer : Consumer)
    (active : state.active = some (capture, consumer)) (noClause : state.clause = none) :
    c1Work { state with active := none, clause := some (capture, consumer) } = c1Work state := by
  simp [c1Work, active, noClause]

theorem c1_finish_matches_root_return (state : State) (capture : Capture) (consumer : Consumer)
    (active : state.active = some (capture, consumer)) (noClause : state.clause = none) :
    c1Work { state with
      active := none
      completed := capture.owners ++ state.completed
      result := some (respond consumer .finished) } = (c1Work state).finishRoot := by
  simp [c1Work, ConcreteWork.finishRoot, active, noClause]

theorem c1_retain_adds_saved_work (state : State) (pre post : List Slot) (old : Slot)
    (capture : Capture) (consumer : Consumer) :
    (c1Work { state with
      clause := none
      slots := pre ++ { old with phase := .live capture } :: post
      result := some (respond consumer (.suspended ⟨state.storeId, old.id, old.generation⟩))
    }).other = true := by
  simp [c1Work, slotHasCapture, List.any_append]


theorem c1_launch_projection_sound (state : State) (capture : Capture) (consumer : Consumer)
    (work : Work) (sound : work.allows (c1Work state))
    (noActive : state.active = none) (noClause : state.clause = none) :
    work.enterRoot.allows (c1Work { state with
      active := some (capture, consumer), result := none }) := by
  rw [c1_launch_matches_root_entry state capture consumer noActive noClause]
  exact enter_root_sound sound

theorem c1_finish_projection_sound (state : State) (capture : Capture) (consumer : Consumer)
    (work : Work) (sound : work.allows (c1Work state))
    (active : state.active = some (capture, consumer)) (noClause : state.clause = none) :
    work.finishRoot.allows (c1Work { state with
      active := none
      completed := capture.owners ++ state.completed
      result := some (respond consumer .finished) }) := by
  rw [c1_finish_matches_root_return state capture consumer active noClause]
  apply finish_root_sound sound
  simp [c1Work, active]

theorem c1_retain_projection_sound (state : State) (pre post : List Slot) (old : Slot)
    (capture : Capture) (consumer : Consumer) :
    Work.pending.allows (c1Work { state with
      clause := none
      slots := pre ++ { old with phase := .live capture } :: post
      result := some (respond consumer (.suspended ⟨state.storeId, old.id, old.generation⟩))
    }) := by
  exact c1_retain_adds_saved_work state pre post old capture consumer

#print axioms Ash.RetainedControl.PortCases.c1_launch_projection_sound
#print axioms Ash.RetainedControl.PortCases.c1_finish_projection_sound
#print axioms Ash.RetainedControl.PortCases.c1_retain_projection_sound

#print axioms Ash.RetainedControl.PortCases.c1_step_preserves_active_clause_separation
#print axioms Ash.RetainedControl.PortCases.c1_launch_matches_root_entry
#print axioms Ash.RetainedControl.PortCases.c1_finish_matches_root_return
#print axioms Ash.RetainedControl.PortCases.c1_retain_adds_saved_work

#print axioms Ash.RetainedControl.PortCases.c1_quiet_has_no_work
#print axioms Ash.RetainedControl.PortCases.c1_no_work_is_quiet

end Ash.RetainedControl.PortCases


/-
Local reading rules for the finite-port projection. `Node` describes only the
transparent fragment read by `case_of`; untracked or ambiguous expressions have
no rule. `LocalSemantics` states the concrete meaning of the actual evaluated
ports, including an aggregate's own creation port and its payload. Establishing
that relation for every retained incoming origin and each restored value context
remains part of the compiler correspondence; it is not inferred from a joined
value edge or from static port identity alone.
-/
namespace Ash.RetainedControl.PortCases.Routing

inductive Node (ports constructors : Nat) where
  | boolean (value : Bool)
  | aggregate (tag : Case constructors) (fields : List (Fin ports))
  | forward (source : Fin ports)
  | project (aggregate : Fin ports) (field : Nat) (tag : Case constructors)
  | other
  deriving DecidableEq, Repr

abbrev Nodes (ports constructors : Nat) := Fin ports → Node ports constructors

/-- The local value equations of the actually evaluated port fragment. -/
structure LocalSemantics {ports constructors : Nat}
    (nodes : Nodes ports constructors) (values : Values ports constructors) : Prop where
  boolean : ∀ port value, nodes port = .boolean value →
    values port = ⟨.boolean value, none⟩
  aggregate : ∀ port tag fields, nodes port = .aggregate tag fields →
    values port = ⟨tag, some port⟩
  forward : ∀ port source, nodes port = .forward source → values port = values source
  project : ∀ port aggregate field tag origin fields child,
    nodes port = .project aggregate field tag →
    (values aggregate).value = tag → (values aggregate).origin = some origin →
    nodes origin = .aggregate tag fields → fields[field]? = some child →
    values port = values child

/-- A successful finite read. A missing fact or unstable origin has no rule. -/
inductive Read {ports constructors : Nat}
    (nodes : Nodes ports constructors) (facts : Facts ports constructors) :
    Fin ports → CaseFact ports constructors → Prop where
  | fact (port fact) : facts port = some fact → Read nodes facts port fact
  | boolean (port value) : facts port = none → nodes port = .boolean value →
      Read nodes facts port ⟨.boolean value, false, none⟩
  | aggregate (port tag fields) : facts port = none → nodes port = .aggregate tag fields →
      Read nodes facts port ⟨tag, false, some port⟩
  | forward (port source fact) : facts port = none → nodes port = .forward source →
      Read nodes facts source fact → Read nodes facts port fact
  | project (port aggregate field tag origin fields child aggregateFact fact) :
      facts port = none → nodes port = .project aggregate field tag →
      Read nodes facts aggregate aggregateFact → aggregateFact.value = tag →
      aggregateFact.origin = some origin → nodes origin = .aggregate tag fields →
      fields[field]? = some child → Read nodes facts child fact →
      Read nodes facts port fact

def Correct {ports constructors : Nat} (values : Values ports constructors)
    (work : ConcreteWork) (port : Fin ports) (fact : CaseFact ports constructors) : Prop :=
  fact.value = (values port).value ∧
    (fact.origin = none ∨ fact.origin = (values port).origin) ∧
    (fact.fresh = true → fact.value = .boolean work.quiet)

/-- Transparent reads and exact payload projection preserve path-local facts. -/
theorem read_sound {ports constructors : Nat}
    {nodes : Nodes ports constructors} {facts : Facts ports constructors}
    {values : Values ports constructors} {work : ConcreteWork}
    (semantics : LocalSemantics nodes values) (sound : agrees facts values work)
    {port : Fin ports} {fact : CaseFact ports constructors}
    (read : Read nodes facts port fact) : Correct values work port fact := by
  induction read with
  | fact port fact present => exact sound port fact present
  | boolean port value absent node =>
      have actual := semantics.boolean port value node
      simp [Correct, actual]
  | aggregate port tag fields absent node =>
      have actual := semantics.aggregate port tag fields node
      simp [Correct, actual]
  | forward port source fact absent node read ih =>
      have equal := semantics.forward port source node
      simpa [Correct, equal] using ih
  | project port aggregate field tag origin fields child aggregateFact fact
      absent node aggregateRead tagEq originEq originNode index childRead aggregateIH childIH =>
      have aggregateCase : (values aggregate).value = tag := by
        exact aggregateIH.1.symm.trans tagEq
      have aggregateOrigin : (values aggregate).origin = some origin := by
        rcases aggregateIH.2.1 with missing | exactOrigin
        · rw [originEq] at missing
          contradiction
        · exact exactOrigin.symm.trans originEq
      have equal := semantics.project port aggregate field tag origin fields child node
        aggregateCase aggregateOrigin originNode index
      simpa [Correct, equal] using childIH

/-- An executed Bind or arm transfer forgets old origins and copies its read. -/
theorem read_assign_sound {ports constructors : Nat}
    {nodes : Nodes ports constructors} {facts : Facts ports constructors}
    {values : Values ports constructors} {work : ConcreteWork}
    (semantics : LocalSemantics nodes values) (sound : agrees facts values work)
    {source target : Fin ports} {observed : CaseFact ports constructors}
    (read : Read nodes facts source observed) :
    agrees (assign (forgetOrigins facts) target (some observed))
      (assign values target (values source)) work := by
  have correct := read_sound semantics sound read
  have forgotten := forget_origins_sound sound
  intro port fact present
  by_cases same : port = target
  · subst port
    simp [assign] at present
    subst fact
    simpa [assign, Correct] using correct
  · have prior := forgotten port fact (by simpa [assign, same] using present)
    simpa [assign, same] using prior

/-- Call, handler and Resume returns drop the caller map and the read origin. -/
theorem read_return_sound {ports constructors : Nat}
    {nodes : Nodes ports constructors} {facts : Facts ports constructors}
    {values : Values ports constructors} {work : ConcreteWork}
    (semantics : LocalSemantics nodes values) (sound : agrees facts values work)
    {source target : Fin ports} {observed : CaseFact ports constructors}
    (read : Read nodes facts source observed) :
    agrees (assign (fun _ ↦ none) target (some (withoutOrigin observed)))
      (assign values target (values source)) work := by
  have correct := read_sound semantics sound read
  intro port fact present
  by_cases same : port = target
  · subst port
    simp [assign] at present
    subst fact
    rcases correct with ⟨value, _, fresh⟩
    have latest : observed.fresh = true → (values source).value = .boolean work.quiet := by
      intro current
      exact value.symm.trans (fresh current)
    simp [assign, withoutOrigin, value]
    exact latest
  · simp [assign, same] at present

/-- A failed read also forgets old origins and cannot assert a new case. -/
theorem absent_read_assign_sound {ports constructors : Nat}
    {facts : Facts ports constructors} {values : Values ports constructors} {work : ConcreteWork}
    (sound : agrees facts values work) (source target : Fin ports) :
    agrees (assign (forgetOrigins facts) target none)
      (assign values target (values source)) work := by
  have forgotten := forget_origins_sound sound
  intro port fact present
  by_cases same : port = target
  · subst port
    simp [assign] at present
  · have prior := forgotten port fact (by simpa [assign, same] using present)
    simpa [assign, same] using prior

/-- One formal assignment uses a read captured before any formals were assigned. -/
theorem snapshot_formal_assign_sound {ports constructors : Nat}
    {nodes : Nodes ports constructors} {oldFacts currentFacts : Facts ports constructors}
    {oldValues currentValues : Values ports constructors} {work : ConcreteWork}
    (semantics : LocalSemantics nodes oldValues) (oldSound : agrees oldFacts oldValues work)
    (currentSound : agrees currentFacts currentValues work)
    {source target : Fin ports} {observed : CaseFact ports constructors}
    (read : Read nodes oldFacts source observed) :
    agrees (assign (forgetOrigins currentFacts) target (some (withoutOrigin observed)))
      (assign currentValues target (oldValues source)) work := by
  have correct := read_sound semantics oldSound read
  have forgotten := forget_origins_sound currentSound
  intro port fact present
  by_cases same : port = target
  · subst port
    simp [assign] at present
    subst fact
    rcases correct with ⟨value, _, fresh⟩
    have latest : observed.fresh = true → (oldValues source).value = .boolean work.quiet := by
      intro current
      exact value.symm.trans (fresh current)
    simp [assign, withoutOrigin, value]
    exact latest
  · have prior := forgotten port fact (by simpa [assign, same] using present)
    simpa [assign, same] using prior

/-- An absent snapshotted case forgets its formal without changing other formals. -/
theorem absent_snapshot_formal_sound {ports constructors : Nat}
    {facts : Facts ports constructors} {values : Values ports constructors} {work : ConcreteWork}
    (sound : agrees facts values work) (target : Fin ports)
    (value : ConcretePort ports constructors) :
    agrees (assign (forgetOrigins facts) target none) (assign values target value) work := by
  have forgotten := forget_origins_sound sound
  intro port fact present
  by_cases same : port = target
  · subst port
    simp [assign] at present
  · have prior := forgotten port fact (by simpa [assign, same] using present)
    simpa [assign, same] using prior

#print axioms Ash.RetainedControl.PortCases.Routing.snapshot_formal_assign_sound
#print axioms Ash.RetainedControl.PortCases.Routing.absent_snapshot_formal_sound

#print axioms Ash.RetainedControl.PortCases.Routing.read_assign_sound
#print axioms Ash.RetainedControl.PortCases.Routing.read_return_sound
#print axioms Ash.RetainedControl.PortCases.Routing.absent_read_assign_sound

#print axioms Ash.RetainedControl.PortCases.Routing.read_sound

end Ash.RetainedControl.PortCases.Routing

/- Finite reachability over the analysis's bounded, normalized full States.
The product correspondence must establish the initial seed, every actual
successor edge after value/revision replay, and the close-predecessor test.
This theorem does not enumerate runtime states or claim execution terminates. -/
namespace Ash.RetainedControl.PortCases.Worklist

open Ash.RetainedControl

theorem finite_union_bounded {α : Type} (entries : List α) (relation : Nat → α → Prop)
    (mono : ∀ n m, n ≤ m → ∀ x, relation n x → relation m x) :
    ∃ n, ∀ x, x ∈ entries → (∃ m, relation m x) → relation n x := by
  classical
  induction entries with
  | nil =>
      refine ⟨0, ?_⟩
      intro x member
      exact False.elim (List.not_mem_nil member)
  | cons entry remaining ih =>
      obtain ⟨n, bound⟩ := ih
      by_cases occurs : ∃ m, relation m entry
      · obtain ⟨m, earlier⟩ := occurs
        refine ⟨max n m, ?_⟩
        intro x member found
        rcases List.mem_cons.mp member with rfl | member
        · exact mono m (max n m) (Nat.le_max_right n m) _ earlier
        · exact mono n (max n m) (Nat.le_max_left n m) x (bound x member found)
      · refine ⟨n, ?_⟩
        intro x member found
        rcases List.mem_cons.mp member with rfl | member
        · exact False.elim (occurs found)
        · exact bound x member found


/-- The finite normal path retains whole-State identities at each edge. -/
inductive Path {count : Nat} (step : Fin count → Fin count → Prop) :
    Fin count → Fin count → Prop where
  | start (state) : Path step state state
  | next {start middle finish} :
      Path step start middle → step middle finish → Path step start finish

/-- Successive reachability approximations include the prior frontier. -/
def Reach {count : Nat} (step : Fin count → Fin count → Prop) (seed : Fin count) :
    Nat → Fin count → Prop
  | 0 => fun state ↦ state = seed
  | n + 1 => fun state ↦ Reach step seed n state ∨
      ∃ previous, Reach step seed n previous ∧ step previous state

theorem reach_succ {count : Nat} {step : Fin count → Fin count → Prop} {seed : Fin count}
    (n : Nat) (state : Fin count) (present : Reach step seed n state) :
    Reach step seed (n + 1) state := Or.inl present

theorem reach_mono {count : Nat} {step : Fin count → Fin count → Prop} {seed : Fin count}
    {n m : Nat} (order : n ≤ m) : ∀ state, Reach step seed n state → Reach step seed m state := by
  induction order with
  | refl => intro state present; exact present
  | @step m order ih =>
      intro state present
      exact reach_succ m state (ih state present)

/-- Some finite approximation contains the union of all finite approximations. -/
theorem finite_reach_converges {count : Nat}
    (step : Fin count → Fin count → Prop) (seed : Fin count) :
    ∃ n, ∀ state, Reach step seed (n + 1) state → Reach step seed n state := by
  obtain ⟨n, bound⟩ := finite_union_bounded
    (List.finRange count) (Reach step seed) (by
      intro n m order state present
      exact reach_mono order state present)
  refine ⟨n, ?_⟩
  intro state present
  exact bound state (List.mem_finRange state) ⟨n + 1, present⟩

/-- Convergence closes every reached full State under the existing successor relation. -/
theorem converged_reach_closed {count : Nat}
    {step : Fin count → Fin count → Prop} {seed : Fin count} {n : Nat}
    (converged : ∀ state, Reach step seed (n + 1) state → Reach step seed n state)
    {state next : Fin count} (present : Reach step seed n state) (edge : step state next) :
    Reach step seed n next := converged next (Or.inr ⟨state, present, edge⟩)

/-- A seed and successor-closed visited set contain every finite path. -/
theorem path_is_visited {count : Nat}
    {step : Fin count → Fin count → Prop} {visited : Fin count → Prop} {seed finish : Fin count}
    (initial : visited seed)
    (closed : ∀ state next, visited state → step state next → visited next)
    (path : Path step seed finish) : visited finish := by
  induction path with
  | start => exact initial
  | next _ edge ih => exact closed _ _ ih edge

/-- Every finite path belongs to the converged reachable approximation. -/
theorem path_at_convergence {count : Nat}
    {step : Fin count → Fin count → Prop} {seed finish : Fin count} {n : Nat}
    (converged : ∀ state, Reach step seed (n + 1) state → Reach step seed n state)
    (path : Path step seed finish) : Reach step seed n finish := by
  apply path_is_visited (visited := Reach step seed n)
    (reach_mono (Nat.zero_le n) seed rfl) ?_ path
  intro state next present edge
  exact converged_reach_closed converged present edge

/-- A normal return pairs the actual call-entry and matching returned State. -/
def NormalReturn {count : Nat} (step : Fin count → Fin count → Prop)
    (corresponds : Fin count → Fin count → Prop) (entry result : Fin count) : Prop :=
  Path step entry result ∧ corresponds entry result

theorem matching_return_is_visited {count : Nat}
    {step : Fin count → Fin count → Prop} {visited : Fin count → Prop}
    {corresponds : Fin count → Fin count → Prop} {entry result : Fin count}
    (initial : visited entry)
    (closed : ∀ state next, visited state → step state next → visited next)
    (normal : NormalReturn step corresponds entry result) :
    visited result ∧ corresponds entry result := by
  exact ⟨path_is_visited initial closed normal.1, normal.2⟩

/-- A finite normal path appears in some approximation for its actual entry. -/
theorem normal_return_is_approximated {count : Nat}
    {step : Fin count → Fin count → Prop} {corresponds : Fin count → Fin count → Prop}
    {entry result : Fin count} (normal : NormalReturn step corresponds entry result) :
    ∃ n, Reach step entry n result ∧ corresponds entry result := by
  have reachable : ∀ {start finish}, Path step start finish → ∃ n, Reach step start n finish := by
    intro start finish path
    induction path with
    | start => exact ⟨0, rfl⟩
    | next _ edge ih =>
        obtain ⟨n, present⟩ := ih
        exact ⟨n + 1, Or.inr ⟨_, present, edge⟩⟩
  obtain ⟨n, present⟩ := reachable normal.1
  exact ⟨n, present, normal.2⟩

/-- A result is related only to its matching full-State call entry. -/
def ReturnApprox {count : Nat} (step : Fin count → Fin count → Prop)
    (corresponds : Fin count → Fin count → Prop) (n : Nat) (entry result : Fin count) : Prop :=
  Reach step entry n result ∧ corresponds entry result

/-- A single finite bound contains every finite matching normal-return pair. -/
theorem finite_return_bound {count : Nat} (step : Fin count → Fin count → Prop)
    (corresponds : Fin count → Fin count → Prop) :
    ∃ n, ∀ entry result, (∃ m, ReturnApprox step corresponds m entry result) →
      ReturnApprox step corresponds n entry result := by
  let pairs : List (Fin count × Fin count) :=
    (List.finRange count).flatMap fun entry ↦
      (List.finRange count).map fun result ↦ (entry, result)
  let relation : Nat → Fin count × Fin count → Prop :=
    fun n pair ↦ ReturnApprox step corresponds n pair.1 pair.2
  have monotone : ∀ n m, n ≤ m → ∀ pair, relation n pair → relation m pair := by
    intro n m order pair present
    exact ⟨reach_mono order pair.2 present.1, present.2⟩
  obtain ⟨n, bound⟩ := finite_union_bounded pairs relation monotone
  refine ⟨n, ?_⟩
  intro entry result present
  have member : (entry, result) ∈ pairs := by
    simp [pairs, List.mem_finRange]
  exact bound (entry, result) member present

/-- The final close is safe only if every reached close predecessor was checked. -/
theorem checked_close_is_quiet {count ports constructors : Nat}
    {step : Fin count → Fin count → Prop} {visited close : Fin count → Prop}
    {project : Fin count → Projection ports constructors} {seed finish : Fin count}
    {actual : ConcreteWork} (initial : visited seed)
    (closed : ∀ state next, visited state → step state next → visited next)
    (checked : ∀ state, visited state → close state → (project state).work = .empty)
    (path : Path step seed finish) (closing : close finish)
    (represented : (project finish).work.allows actual) : actual.quiet = true := by
  have present := path_is_visited initial closed path
  have empty := checked finish present closing
  have actualEmpty : Work.empty.allows actual := by simpa [empty] using represented
  rcases actualEmpty with ⟨noActive, noOther⟩
  simp [ConcreteWork.quiet, noActive, noOther]

/-- C1's no-work predecessor follows only at that same checked close. -/
theorem checked_c1_close_has_no_work {count ports constructors : Nat}
    {step : Fin count → Fin count → Prop} {visited close : Fin count → Prop}
    {project : Fin count → Projection ports constructors} {seed finish : Fin count}
    (state : State) (initial : visited seed)
    (closed : ∀ current next, visited current → step current next → visited next)
    (checked : ∀ current, visited current → close current → (project current).work = .empty)
    (path : Path step seed finish) (closing : close finish)
    (represented : (project finish).work.allows (c1Work state)) : NoWork state := by
  apply c1_quiet_has_no_work state
  exact checked_close_is_quiet initial closed checked path closing represented

#print axioms Ash.RetainedControl.PortCases.Worklist.finite_reach_converges
#print axioms Ash.RetainedControl.PortCases.Worklist.converged_reach_closed
#print axioms Ash.RetainedControl.PortCases.Worklist.path_at_convergence
#print axioms Ash.RetainedControl.PortCases.Worklist.matching_return_is_visited
#print axioms Ash.RetainedControl.PortCases.Worklist.normal_return_is_approximated
#print axioms Ash.RetainedControl.PortCases.Worklist.finite_return_bound
#print axioms Ash.RetainedControl.PortCases.Worklist.checked_close_is_quiet
#print axioms Ash.RetainedControl.PortCases.Worklist.checked_c1_close_has_no_work

end Ash.RetainedControl.PortCases.Worklist
