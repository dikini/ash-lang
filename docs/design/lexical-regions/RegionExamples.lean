import RegionCoherence

/- Concrete finite controls for the R1 draft. These are model examples, not
source/Core correspondence or native-storage evidence. -/
namespace Ash.Regions.Examples

abbrev R := Fin 2
abbrev O := Fin 2
abbrev T := Fin 1

def association : Association := ⟨10, 11, 12, 13⟩
def liveRegion : Region 2 := { phase := .live, association := association, parent := none }
def left : R := 0
def right : R := 1

def empty : State 2 2 1 where
  regions := fun _ => some liveRegion
  objects := fun _ => none
  selected := some left
  pending := none
  tickets := fun _ => none
  completionOrder := [right, left]
  operandHistory := 7

theorem empty_live (r : R) : Live empty r :=
  ⟨liveRegion, rfl, rfl⟩

theorem empty_valid : Valid empty := by
  refine ⟨?_, ?_, ?_⟩
  · intro i o found
    simp [empty] at found
  · intro r info parent found enclosing
    simp [empty] at found
    subst info
    simp [liveRegion] at enclosing
  · intro r selected
    exact empty_live r

theorem pending_read_rejects : ¬ Readable (reserve empty 0 left) 0 := by
  apply pending_not_readable (reserve empty 0 left) 0 ⟨left, .pending, [], [], 0⟩
  · simp [reserve, replace]
  · rfl

def captured : Captured 2 2 := { selected := some left, pending := none, completionOrder := [right, left] }
def suspended : State 2 2 1 :=
  { empty with selected := some right, tickets := fun _ => some captured }

/-- Resume restores the captured allocation context, not the caller's default. -/
theorem resume_uses_captured_selection :
    (resume suspended 0 captured).selected = some left := rfl

theorem resume_cannot_reuse_same_ticket :
    (resume suspended 0 captured).tickets 0 ≠ some captured := by
  simp [resume, replace]

def selfOwner : Region 2 := { phase := .live, association := association, parent := some left }
def selfOwnerState : State 2 2 1 :=
  { empty with regions := fun _ => some selfOwner }

theorem resource_owner_cycle_rejects : ¬ OwnersOrdered selfOwnerState := by
  intro ordered
  have impossible := ordered left selfOwner left rfl rfl
  exact Nat.lt_irrefl left.val impossible

def requestLeft : Requirements 2 := ⟨left, 8, 8⟩
def replyLeft (i : O) : Backing 2 2 := ⟨left, i, association, 8, 8⟩
def continuation (i : O) : Pending 2 2 :=
  { object := i, selected := left, nextInitializer := 0, operandHistory := 7,
    continuationContext := some left, continuationCut := 0 }
def privateObject : Object 2 2 := ⟨left, .pending, [], [], 0⟩
def initializedObject (field : O) : Object 2 2 := ⟨left, .initialized, [], [field], 1⟩

def request0 := requestStorage empty 0 requestLeft liveRegion
def supplied0 := supplyStorage request0 0 requestLeft (replyLeft 0) (continuation 0)
def request1 := requestStorage supplied0 1 requestLeft liveRegion
def supplied1 := supplyStorage request1 1 requestLeft (replyLeft 1) (continuation 1)
def initialized0 := initializeSlot supplied1 0 privateObject [] [1]
def initialized1 := initializeSlot initialized0 1 privateObject [] [0]
def usableCycle := publishGroup initialized1 [0, 1]

theorem request0_admitted : ConstructionStep empty request0 := by
  apply ConstructionStep.request empty 0 requestLeft liveRegion
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro r found; cases found
  · simp [empty, liveRegion]

theorem supply0_admitted : ConstructionStep request0 supplied0 := by
  apply ConstructionStep.supply request0 0 requestLeft (replyLeft 0) (continuation 0)
  · rfl
  · rfl
  · rfl
  · simp [request0, requestStorage, replace]
  · rfl
  · exact ⟨rfl, rfl, Nat.le_refl 8, by decide, rfl, liveRegion, rfl, rfl, rfl⟩

theorem request1_admitted : ConstructionStep supplied0 request1 := by
  apply ConstructionStep.request supplied0 1 requestLeft liveRegion
  · rfl
  · simp [supplied0, supplyStorage, reserve, request0, requestStorage, replace, empty]
  · simp [supplied0, supplyStorage, reserve, replace, request0, requestStorage, empty]
  · rfl
  · rfl
  · intro r found; cases found
  · simp [supplied0, supplyStorage, reserve, request0, requestStorage, empty, liveRegion]

theorem supply1_admitted : ConstructionStep request1 supplied1 := by
  apply ConstructionStep.supply request1 1 requestLeft (replyLeft 1) (continuation 1)
  · rfl
  · rfl
  · rfl
  · simp [request1, requestStorage, replace]
  · simp [request1, requestStorage, supplied0, supplyStorage, reserve, replace,
          request0, empty]
  · exact ⟨rfl, rfl, Nat.le_refl 8, by decide, rfl, liveRegion, rfl, rfl, rfl⟩

theorem initialize0_admitted : ConstructionStep supplied1 initialized0 := by
  apply ConstructionStep.initializeSlot supplied1 0 privateObject [] [1]
  · simp [supplied1, supplyStorage, reserve, replace, request1, requestStorage,
          supplied0, request0, empty, privateObject, requestLeft]
  · rfl
  · intro r member; cases member
  · intro j member
    have same : j = 1 := List.mem_singleton.mp member
    subst j
    exact ⟨privateObject, by simp [supplied1, supplyStorage, reserve, replace,
      privateObject, requestLeft]⟩

theorem initialize1_admitted : ConstructionStep initialized0 initialized1 := by
  apply ConstructionStep.initializeSlot initialized0 1 privateObject [] [0]
  · simp [initialized0, initializeSlot, replace, supplied1, supplyStorage, reserve,
          privateObject, requestLeft]
  · rfl
  · intro r member; cases member
  · intro j member
    have same : j = 0 := List.mem_singleton.mp member
    subst j
    exact ⟨initializedObject 1, by simp [initialized0, initializeSlot, replace,
      privateObject, initializedObject]⟩

theorem cyclic_group_ready : GroupReady initialized1 [0, 1] := by
  refine ⟨(by intro i _; rfl), ?_⟩
  intro i member
  have which : i = 0 ∨ i = 1 := by simpa using member
  rcases which with same | same
  · subst i
    refine ⟨initializedObject 1, ?_, Or.inl rfl, ?_, ?_⟩
    · simp [initialized1, initializeSlot, replace, initialized0, privateObject, initializedObject]
    · intro r impossible; cases impossible
    · intro j member
      have same : j = 1 := List.mem_singleton.mp member
      subst j
      exact ⟨Or.inr (by simp), initializedObject 0,
        by simp [initialized1, initializeSlot, replace, privateObject, initializedObject],
        Or.inl rfl⟩
  · subst i
    refine ⟨initializedObject 0, ?_, Or.inl rfl, ?_, ?_⟩
    · simp [initialized1, initializeSlot, replace, privateObject, initializedObject]
    · intro r impossible; cases impossible
    · intro j member
      have same : j = 0 := List.mem_singleton.mp member
      subst j
      exact ⟨Or.inr (by simp), initializedObject 1,
        by simp [initialized1, initializeSlot, replace, initialized0, privateObject,
          initializedObject], Or.inl rfl⟩

/-- Pending slots are initialized in order, then made usable as one closed field graph. -/
theorem pending_to_cyclic_graph_trace : ConstructionTrace empty usableCycle := by
  exact .next _ _ _ request0_admitted (.next _ _ _ supply0_admitted
    (.next _ _ _ request1_admitted (.next _ _ _ supply1_admitted
      (.next _ _ _ initialize0_admitted (.next _ _ _ initialize1_admitted
        (.next _ _ _ (.publish _ _ cyclic_group_ready) (.refl _)))))))

theorem cyclic_aliases_are_usable : usableCycle.exposed 0 = true ∧ usableCycle.exposed 1 = true := by
  simp [usableCycle, publishGroup]

theorem cyclic_edges_preserved :
    usableCycle.objects 0 = some (initializedObject 1) ∧
    usableCycle.objects 1 = some (initializedObject 0) := by
  simp [usableCycle, publishGroup, initialized1, initializeSlot, replace, initialized0,
        initializedObject, privateObject]

end Ash.Regions.Examples

#print axioms Ash.Regions.Examples.empty_valid
#print axioms Ash.Regions.Examples.pending_read_rejects
#print axioms Ash.Regions.Examples.resume_uses_captured_selection
#print axioms Ash.Regions.Examples.resume_cannot_reuse_same_ticket
#print axioms Ash.Regions.Examples.resource_owner_cycle_rejects

#print axioms Ash.Regions.Examples.pending_to_cyclic_graph_trace
#print axioms Ash.Regions.Examples.cyclic_aliases_are_usable
#print axioms Ash.Regions.Examples.cyclic_edges_preserved

/- The outer-residency trace uses actual request, supply, initialization and publication.
It is finite model evidence, not source/Core or native-storage correspondence. -/
namespace Ash.Regions.Examples

def outerCapturedObject : Object 2 2 :=
  { region := left, phase := .initialized, required := [right], fields := [],
    initializer := 1 }

def outerInitialized := initializeSlot supplied0 0 privateObject [right] []
def outerPublished := publishGroup outerInitialized [0]
def outerDropped := dropAccess outerPublished [0]
def outerSelected := select outerDropped left
def outerClosed := closeRegion outerSelected right liveRegion

theorem outer_initialize_admitted : ConstructionStep supplied0 outerInitialized := by
  apply ConstructionStep.initializeSlot supplied0 0 privateObject [right] []
  · simp [supplied0, supplyStorage, reserve, replace, privateObject, requestLeft]
  · rfl
  · intro r member
    have same : r = right := List.mem_singleton.mp member
    subst r
    exact empty_live right
  · intro j impossible
    cases impossible

theorem outer_initialized_record :
    outerInitialized.objects 0 = some outerCapturedObject := by
  simp [outerInitialized, initializeSlot, replace, privateObject, outerCapturedObject]

theorem outer_private_flags (i : O) : outerInitialized.exposed i = false := rfl

theorem outer_group_ready : GroupReady outerInitialized [0] := by
  refine ⟨(by intro i _; rfl), ?_⟩
  intro i member
  have same : i = 0 := List.mem_singleton.mp member
  subst i
  refine ⟨outerCapturedObject, outer_initialized_record, Or.inl rfl, ?_, ?_⟩
  · intro r member
    have same : r = right := List.mem_singleton.mp member
    subst r
    exact empty_live right
  · intro j impossible
    cases impossible

theorem outer_published_safe : PublicationSafe outerPublished := by
  apply publish_group_preserves outerInitialized [0] _ outer_group_ready
  intro i visible
  simp [outer_private_flags] at visible

theorem outer_capture_usable_while_younger_live :
    outerPublished.exposed 0 = true ∧ Readable outerPublished 0 ∧
    Live outerPublished right := by
  have exposed : outerPublished.exposed 0 = true := by simp [outerPublished, publishGroup]
  exact ⟨exposed, public_read_is_initialized outerPublished outer_published_safe 0 exposed,
    empty_live right⟩

theorem outer_drop_admitted : ConstructionStep outerPublished outerDropped := by
  apply ConstructionStep.drop outerPublished [0]
  intro i o visible outside found j field
  have member : i ∈ ([0] : List O) := by
    by_cases member : i ∈ ([0] : List O)
    · exact member
    · have eq : i = 0 := by simpa [outerPublished, publishGroup, outer_private_flags] using visible
      exact List.mem_singleton.mpr eq
  exact False.elim (outside member)

/-- Request/supply, local initialization, publication and revocation use local admission facts. -/
theorem outer_capture_construction_trace : ConstructionTrace empty outerDropped := by
  exact .next _ _ _ request0_admitted (.next _ _ _ supply0_admitted
    (.next _ _ _ outer_initialize_admitted
      (.next _ _ _ (.publish _ _ outer_group_ready)
        (.next _ _ _ outer_drop_admitted (.refl _)))))

theorem outer_all_access_dropped (i : O) : outerDropped.exposed i = false := by
  simp [outerDropped, dropAccess, outerPublished, publishGroup, outer_private_flags]

/-- Dead younger dependencies in inaccessible outer bytes do not prevent safe close. -/
theorem outer_close_keeps_publication_safe : PublicationSafe outerClosed := by
  apply close_preserves_publication outerSelected right liveRegion
  · intro i visible
    have absent : outerSelected.exposed i = false := outer_all_access_dropped i
    simp [absent] at visible
  · intro i o visible found outside
    have absent : outerSelected.exposed i = false := outer_all_access_dropped i
    simp [absent] at visible

/-- Closing T leaves the initialized outer-S allocation record and backing exact. -/
theorem outer_stale_capture_stays_physical :
    outerClosed.objects 0 = some outerCapturedObject ∧
    outerClosed.backing 0 = some (replyLeft 0) ∧
    outerClosed.selected = some left ∧ ¬ Live outerClosed right := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · apply close_preserves_other_objects outerSelected right liveRegion 0 outerCapturedObject
    · exact outer_initialized_record
    · change left ≠ right
      decide
  · simp [outerClosed, closeRegion, outerSelected, select, outerDropped, dropAccess,
      outerPublished, publishGroup, outerInitialized, initializeSlot, supplied0,
      supplyStorage, replace]
  · simp [Live, outerClosed, closeRegion, replace, liveRegion]

end Ash.Regions.Examples

#print axioms Ash.Regions.Examples.outer_capture_construction_trace
#print axioms Ash.Regions.Examples.outer_capture_usable_while_younger_live
#print axioms Ash.Regions.Examples.outer_close_keeps_publication_safe
#print axioms Ash.Regions.Examples.outer_stale_capture_stays_physical

/- Finite admitted construction and authenticated inline-view examples.
Source/Core lowering and physical storage are separate correspondence assumptions. -/
namespace Ash.Regions.Examples.CallerPlacement

abbrev Slot := Fin 3

def initial : State 2 3 1 where
  regions := fun _ => some liveRegion
  objects := fun _ => none
  selected := some left
  pending := none
  tickets := fun _ => none
  completionOrder := [right, left]
  operandHistory := 7

def requestLeft : Requirements 2 := { owner := left, extent := 8, alignment := 8 }
def requestRight : Requirements 2 := { owner := right, extent := 8, alignment := 8 }
def backing0 : Backing 2 3 :=
  { owner := left, identity := 0, association := association, extent := 8, alignment := 8 }
def continuation0 : Pending 2 3 :=
  { object := 0, selected := left, nextInitializer := 0, operandHistory := 7,
    continuationContext := some left, continuationCut := 0 }
def pending0 : Object 2 3 :=
  { region := left, phase := .pending, required := [], fields := [], initializer := 0 }
def closureRecord : Object 2 3 :=
  { region := left, phase := .initialized, required := [right], fields := [], initializer := 1 }

def requested := requestStorage initial 0 requestLeft liveRegion
def supplied := supplyStorage requested 0 requestLeft backing0 continuation0
def initialized := initializeSlot supplied 0 pending0 [right] []
def published := publishGroup initialized [0]
def callerRight := select published right
def callerLeft := select callerRight left

def freshRight := requestStorage callerRight 1 requestRight liveRegion
def freshLeft := requestStorage callerLeft 2 requestLeft liveRegion

theorem request_admitted : ConstructionStep initial requested := by
  apply ConstructionStep.request initial 0 requestLeft liveRegion
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro r found
    cases found
  · simp [initial, liveRegion]

theorem supply_admitted : ConstructionStep requested supplied := by
  apply ConstructionStep.supply requested 0 requestLeft backing0 continuation0
  · rfl
  · rfl
  · rfl
  · simp [requested, requestStorage, replace]
  · rfl
  · exact ⟨rfl, rfl, Nat.le_refl 8, by decide, rfl, liveRegion, rfl, rfl, rfl⟩

theorem initialize_admitted : ConstructionStep supplied initialized := by
  apply ConstructionStep.initializeSlot supplied 0 pending0 [right] []
  · simp [supplied, supplyStorage, reserve, replace, pending0, requestLeft]
  · rfl
  · intro r member
    have same : r = right := List.mem_singleton.mp member
    subst r
    exact ⟨liveRegion, rfl, rfl⟩
  · intro j impossible
    cases impossible

theorem initialized_record : initialized.objects 0 = some closureRecord := by
  simp [initialized, initializeSlot, replace, pending0, closureRecord]

theorem closure_ready : GroupReady initialized [0] := by
  refine ⟨(by intro i _; rfl), ?_⟩
  intro i member
  have same : i = 0 := List.mem_singleton.mp member
  subst i
  refine ⟨closureRecord, initialized_record, Or.inl rfl, ?_, ?_⟩
  · intro r member
    have same : r = right := List.mem_singleton.mp member
    subst r
    exact ⟨liveRegion, rfl, rfl⟩
  · intro j impossible
    cases impossible

theorem construction_trace : ConstructionTrace initial published := by
  exact .next _ _ _ request_admitted (.next _ _ _ supply_admitted
    (.next _ _ _ initialize_admitted (.next _ _ _ (.publish _ _ closure_ready) (.refl _))))

theorem published_safe : PublicationSafe published := by
  apply publish_group_preserves initialized [0] _ closure_ready
  intro i visible
  have absent : initialized.exposed i = false := rfl
  simp [absent] at visible

theorem published_usable : published.exposed 0 = true ∧ Readable published 0 ∧
    Live published right := by
  have visible : published.exposed 0 = true := by simp [published, publishGroup]
  exact ⟨visible, public_read_is_initialized published published_safe 0 visible,
    liveRegion, rfl, rfl⟩

/-- Both caller selections preserve the closure's storage and captured dependency. -/
theorem caller_selection_preserves_closure :
    callerRight.objects 0 = some closureRecord ∧ callerRight.backing 0 = some backing0 ∧
    callerLeft.objects 0 = some closureRecord ∧ callerLeft.backing 0 = some backing0 := by
  refine ⟨initialized_record, ?_, initialized_record, ?_⟩ <;>
    simp [callerRight, callerLeft, select, published, publishGroup, initialized,
      initializeSlot, supplied, supplyStorage, replace]

theorem select_caller_right_admitted :
    Transition (fun _ => []) (⟨published, fun _ => none, fun _ => none⟩ : Machine 2 3 1)
      ⟨callerRight, fun _ => none, fun _ => none⟩ := by
  exact .select _ right ⟨liveRegion, rfl, rfl⟩ (by intro c found; cases found)

theorem select_explicit_left_admitted :
    Transition (fun _ => []) (⟨callerRight, fun _ => none, fun _ => none⟩ : Machine 2 3 1)
      ⟨callerLeft, fun _ => none, fun _ => none⟩ := by
  exact .select _ left ⟨liveRegion, rfl, rfl⟩ (by intro c found; cases found)

/-- The fresh request is admitted in the caller's selected right region. -/
theorem caller_right_request_admitted : ConstructionStep callerRight freshRight := by
  apply ConstructionStep.request callerRight 1 requestRight liveRegion
  · rfl
  · simp [callerRight, select, published, publishGroup, initialized, initializeSlot,
      supplied, supplyStorage, reserve, requested, requestStorage, replace, initial]
  · simp [callerRight, select, published, publishGroup, initialized, initializeSlot,
      supplied, supplyStorage, reserve, replace, requested, requestStorage, initial]
  · rfl
  · rfl
  · intro r found
    cases found
  · simp [callerRight, select, published, publishGroup, initialized, initializeSlot,
      supplied, supplyStorage, reserve, requested, requestStorage, initial, liveRegion]

/-- Explicit reselection admits a separate fresh request in left. -/
theorem explicit_left_request_admitted : ConstructionStep callerLeft freshLeft := by
  apply ConstructionStep.request callerLeft 2 requestLeft liveRegion
  · rfl
  · simp [callerLeft, callerRight, select, published, publishGroup, initialized,
      initializeSlot, supplied, supplyStorage, reserve, requested, requestStorage, replace, initial]
  · simp [callerLeft, callerRight, select, published, publishGroup, initialized,
      initializeSlot, supplied, supplyStorage, reserve, replace, requested, requestStorage, initial]
  · rfl
  · rfl
  · intro r found
    cases found
  · simp [callerLeft, callerRight, select, published, publishGroup, initialized,
      initializeSlot, supplied, supplyStorage, reserve, requested, requestStorage, initial, liveRegion]

/-- Requests record fresh placement independently of the preexisting closure's placement. -/
theorem caller_and_explicit_fresh_placement :
    callerRight.selected = some requestRight.owner ∧
    freshRight.requirements 1 = some requestRight ∧
    callerLeft.selected = some requestLeft.owner ∧
    freshLeft.requirements 2 = some requestLeft ∧
    freshRight.objects 0 = some closureRecord ∧ freshRight.backing 0 = some backing0 ∧
    freshLeft.objects 0 = some closureRecord ∧ freshLeft.backing 0 = some backing0 := by
  refine ⟨rfl, ?_, rfl, ?_, initialized_record,
    caller_selection_preserves_closure.2.1, initialized_record,
    caller_selection_preserves_closure.2.2.2⟩
  · simp [freshRight, requestStorage, replace]
  · simp [freshLeft, requestStorage, replace]

end Ash.Regions.Examples.CallerPlacement

#print axioms Ash.Regions.Examples.CallerPlacement.construction_trace
#print axioms Ash.Regions.Examples.CallerPlacement.published_usable
#print axioms Ash.Regions.Examples.CallerPlacement.caller_selection_preserves_closure
#print axioms Ash.Regions.Examples.CallerPlacement.caller_right_request_admitted
#print axioms Ash.Regions.Examples.CallerPlacement.explicit_left_request_admitted
#print axioms Ash.Regions.Examples.CallerPlacement.caller_and_explicit_fresh_placement

/- Finite admitted construction and authenticated inline-view examples.
Source/Core lowering and physical storage are separate correspondence assumptions. -/
namespace Ash.Regions.Examples.InlineAccess

/-- Part 0 is independent; part 1 actually captures the younger right region. -/
def inlineLayout : Layout 2 2 := fun _ => [[], [right]]
def independentPart : View 2 := { object := 0, inlinePart := some 0 }
def dependentPart : View 2 := { object := 0, inlinePart := some 1 }

theorem published_whole_safe : ViewSafe inlineLayout outerPublished (WholeView 0) := by
  exact ⟨outerCapturedObject, outer_initialized_record, Or.inl rfl,
    empty_live left, outer_capture_usable_while_younger_live.1⟩

/-- A usable whole value with a younger capture fails the heap close admission. -/
theorem exposed_whole_blocks_younger_close :
    ¬ NoOutsideUsableDependency outerPublished right := by
  intro admitted
  have blocked := admitted 0 outerCapturedObject
    outer_capture_usable_while_younger_live.1 outer_initialized_record (by decide)
  exact blocked (by simp [outerCapturedObject])

/-- Both inline parts are derived while the whole value and younger dependency are live. -/
theorem derived_inline_parts_safe :
    ViewSafe inlineLayout outerPublished independentPart ∧
    ViewSafe inlineLayout outerPublished dependentPart := by
  constructor
  · apply inline_view_safe inlineLayout outerPublished (WholeView 0) published_whole_safe 0 []
    · rfl
    · intro r impossible
      cases impossible
    · rfl
  · apply inline_view_safe inlineLayout outerPublished (WholeView 0)
      published_whole_safe 1 [right]
    · rfl
    · intro r member
      have same : r = right := List.mem_singleton.mp member
      subst r
      exact empty_live right
    · rfl

/-- Revoking all whole aliases preserves already derived inline parts. -/
theorem inline_parts_survive_whole_drop :
    ViewSafe inlineLayout outerDropped independentPart ∧
    ViewSafe inlineLayout outerDropped dependentPart := by
  constructor
  · apply view_drop inlineLayout outerPublished [0] independentPart derived_inline_parts_safe.1
    intro impossible
    cases impossible
  · apply view_drop inlineLayout outerPublished [0] dependentPart derived_inline_parts_safe.2
    intro impossible
    cases impossible

theorem independent_part_avoids_younger :
    ViewAvoids inlineLayout outerSelected right independentPart := by
  intro o found
  have stored : outerSelected.objects 0 = some outerCapturedObject := outer_initialized_record
  have same : o = outerCapturedObject := Option.some.inj (found.symm.trans stored)
  subst o
  refine ⟨by decide, ?_⟩
  intro p deps kind actual
  have same : p = 0 := by simpa [independentPart] using kind.symm
  subst p
  have emptyDeps : deps = [] := by simpa [inlineLayout, independentPart] using actual.symm
  subst deps
  simp

/-- An independent inline part retains outer residency and survives younger close. -/
theorem independent_inline_usable_after_close :
    ViewSafe inlineLayout outerClosed independentPart := by
  exact view_close inlineLayout outerSelected right liveRegion independentPart
    inline_parts_survive_whole_drop.1 independent_part_avoids_younger

/-- No whole view survives the explicit revocation, even though outer bytes remain. -/
theorem whole_unusable_after_close :
    ¬ ViewSafe inlineLayout outerClosed (WholeView 0) := by
  intro safe
  rcases safe with ⟨o, found, ready, resident, visible⟩
  have absent : outerClosed.exposed 0 = false := by
    change (closeRegion outerSelected right liveRegion).exposed 0 = false
    have stored : outerSelected.objects 0 = some outerCapturedObject := outer_initialized_record
    change (match outerSelected.objects 0 with
      | none => false
      | some o => if o.region = right then false else outerSelected.exposed 0) = false
    rw [stored]
    simp [outerCapturedObject, left, right, outerSelected, select, outer_all_access_dropped]
  change outerClosed.exposed 0 = true at visible
  simp [absent] at visible

/-- Authenticated dependence on right prevents using the dependent inline part after close. -/
theorem dependent_inline_unusable_after_close :
    ¬ ViewSafe inlineLayout outerClosed dependentPart := by
  intro safe
  rcases safe with ⟨o, found, ready, resident, published, deps, actual, live⟩
  have actualDeps : deps = [right] := by
    simpa [inlineLayout, dependentPart] using actual.symm
  subst deps
  exact outer_stale_capture_stays_physical.2.2.2 (live right (by simp))

end Ash.Regions.Examples.InlineAccess

#print axioms Ash.Regions.Examples.InlineAccess.exposed_whole_blocks_younger_close
#print axioms Ash.Regions.Examples.InlineAccess.derived_inline_parts_safe
#print axioms Ash.Regions.Examples.InlineAccess.inline_parts_survive_whole_drop
#print axioms Ash.Regions.Examples.InlineAccess.independent_inline_usable_after_close
#print axioms Ash.Regions.Examples.InlineAccess.whole_unusable_after_close
#print axioms Ash.Regions.Examples.InlineAccess.dependent_inline_unusable_after_close
