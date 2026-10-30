import NetworkLedgerCoreEval

/-
Finite representations of the ordinary Ash values inspected by RemoveById.
These are relations over the actual modeled heap, not a claim that all Ash
recursive values are finite. The successful resolve premises retain alias
semantics; each recursive list premise consumes the actual tail value. Their
preservation across allocation and connection to checked nodes remain to prove.
-/
namespace Ash.NetworkLedger.CoreValues

open Ash.NetworkLedger
open Ash.NetworkLedger.CoreEval
open Ash.NetworkLedger.CoreRegion

structure Constructors where
  root : Constructor
  work : Constructor
  child : Constructor
  empty : Constructor
  more : Constructor
  found : Constructor
  missing : Constructor

/-- A Root or Work identity, with a nonnegative checked allocator label. -/
inductive Ident (c : Constructors) (store : Store) : Value → Id → Prop where
  | root (address resolved : Nat)
      (resolution : Resolve store address resolved)
      (cell : readCell store resolved = some [.tag c.root]) :
      Ident c store (.location address) .root
  | work (address resolved payload tuple : Nat) (allocator : Nat) (serial : Int)
      (resolution : Resolve store address resolved)
      (cell : readCell store resolved = some [.tag c.work, .location payload])
      (payloadResolution : Resolve store payload tuple)
      (fields : readCell store tuple = some [.integer (Int.ofNat allocator), .integer serial]) :
      Ident c store (.location address) (.work allocator serial)

/-- Retained cells and alias links preserve a represented nominal identity. -/
theorem ident_retained (c : Constructors) (before after : Store) (value : Value) (id : Id)
    (aliasesSame : after.aliases = before.aliases)
    (cellsRetained : ∀ location values, readCell before location = some values →
      readCell after location = some values)
    (representation : Ident c before value id) : Ident c after value id := by
  cases representation with
  | root address resolved resolution cell =>
    exact Ident.root address resolved (resolve_preserved aliasesSame cellsRetained resolution)
      (cellsRetained resolved _ cell)
  | work address resolved payload tuple allocator serial resolution cell payloadResolution fields =>
    exact Ident.work address resolved payload tuple allocator serial
      (resolve_preserved aliasesSame cellsRetained resolution) (cellsRetained resolved _ cell)
      (resolve_preserved aliasesSame cellsRetained payloadResolution) (cellsRetained tuple _ fields)

/-- Checked comparator tuple evaluation retains both represented IDs. -/
theorem checked_id_pair_tuple (c : Constructors) (program : Program)
    (root left right : NodeId) (env : Environment) (start finish : Store)
    (result leftValue rightValue : Value) (leftId rightId : Id)
    (checked : CheckedTuple program root none [left, right])
    (leftName rightName : Binder)
    (leftShape : program left = some (.variable leftName))
    (rightShape : program right = some (.variable rightName))
    (leftFresh : leftName ≠ checked.contextBinder)
    (rightFresh : rightName ≠ checked.contextBinder)
    (leftBinding : CoreEval.lookup env leftName = some leftValue)
    (rightBinding : CoreEval.lookup env rightName = some rightValue)
    (bounded : BoundedLocations start)
    (leftRepresentation : Ident c start leftValue leftId)
    (rightRepresentation : Ident c start rightValue rightId)
    (evaluation : Eval program env root start result finish) :
    ∃ location, result = .location location ∧ Resolve finish location location ∧
      readCell finish location = some [leftValue, rightValue] ∧
      Ident c finish leftValue leftId ∧ Ident c finish rightValue rightId ∧ BoundedLocations finish := by
  obtain ⟨location, fresh, resultEq, pairCell, aliasesSame, finishBound, cellsRetained⟩ :=
    checked_variable_pair_retains checked leftName rightName leftShape rightShape leftFresh rightFresh
      leftBinding rightBinding bounded evaluation
  have noAlias : readAlias finish location = none := by
    rw [fresh]
    simpa [readAlias, aliasesSame] using bounded_fresh_no_alias start bounded
  exact ⟨location, resultEq, Resolve.cell location [leftValue, rightValue] noAlias pairCell, pairCell,
    ident_retained c start finish leftValue leftId aliasesSame cellsRetained leftRepresentation,
    ident_retained c start finish rightValue rightId aliasesSame cellsRetained rightRepresentation,
    finishBound⟩

/-- The complete child entry and its key, with the other field retained. -/
inductive Entry (c : Constructors) (store : Store) : Value → Value → Value → Prop where
  | child (address resolved payload tuple : Nat) (key destination : Value)
      (resolution : Resolve store address resolved)
      (cell : readCell store resolved = some [.tag c.child, .location payload])
      (payloadResolution : Resolve store payload tuple)
      (fields : readCell store tuple = some [key, destination]) :
      Entry c store (.location address) key destination

/-- Only a finite constructor chain ending in Empty denotes an ordinary list. -/
inductive Children (c : Constructors) (store : Store) : Value → List Value → Prop where
  | empty (address resolved : Nat)
      (resolution : Resolve store address resolved)
      (cell : readCell store resolved = some [.tag c.empty]) :
      Children c store (.location address) []
  | more (address resolved payload tuple : Nat) (head tail : Value) (entries : List Value)
      (resolution : Resolve store address resolved)
      (cell : readCell store resolved = some [.tag c.more, .location payload])
      (payloadResolution : Resolve store payload tuple)
      (fields : readCell store tuple = some [head, tail])
      (remaining : Children c store tail entries) :
      Children c store (.location address) (head :: entries)

/-- A result tuple contains the actual returned list and status values. -/
inductive Result (store : Store) : Value → Value → Value → Prop where
  | pair (address resolved : Nat) (list status : Value)
      (resolution : Resolve store address resolved)
      (fields : readCell store resolved = some [list, status]) :
      Result store (.location address) list status

/-- Matching an actual nullary constructor with the same identity succeeds. -/
theorem nullary_constructor_match (store : Store) (tag : Constructor) (address resolved : Nat)
    (resolution : Resolve store address resolved)
    (cell : readCell store resolved = some [.tag tag])
    {result : Option Environment}
    (attempt : Attempt store (.constructor tag none) (.location address) result) : result = some [] := by
  cases attempt with
  | constructorNotLocation _ _ _ notLocation =>
    exact False.elim (notLocation address rfl)
  | constructorWrongKind _ _ _ other stored otherResolution otherRead wrong =>
    have equal := resolved_fields_unique resolution otherResolution cell otherRead
    subst stored
    simp [constructorFields] at wrong
  | constructorWrongTag _ found _ _ other stored actual otherResolution otherRead view different =>
    have equal := resolved_fields_unique resolution otherResolution cell otherRead
    subst stored
    simp [constructorFields] at view
    simp_all
  | constructorNoPayload => rfl
  | constructorUnexpectedPayload _ _ other stored value otherResolution otherRead view =>
    have equal := resolved_fields_unique resolution otherResolution cell otherRead
    subst stored
    simp [constructorFields] at view


/-- An actual two-field tuple binds both complete values in source order. -/
theorem pair_binders_match (store : Store) (address resolved : Nat)
    (leftName rightName : Binder) (left right : Value)
    (resolution : Resolve store address resolved)
    (cell : readCell store resolved = some [left, right])
    (plain : tupleFields [left, right] = some [left, right])
    {result : Option Environment}
    (attempt : Attempt store (.tuple [.binder leftName, .binder rightName])
      (.location address) result) : result = some [(leftName, left), (rightName, right)] := by
  cases attempt with
  | tupleNotLocation _ _ notLocation => exact False.elim (notLocation address rfl)
  | tupleWrongKind _ _ other stored otherResolution otherRead wrong =>
    have equal := resolved_fields_unique resolution otherResolution cell otherRead
    subst stored
    simp_all
  | tupleFields _ _ other stored values found otherResolution otherRead view attempts =>
    have equal := resolved_fields_unique resolution otherResolution cell otherRead
    subst stored
    rw [plain] at view
    have valueEq := Option.some.inj view
    subst values
    cases attempts with
    | headMiss _ _ _ _ miss => cases miss
    | tailMiss _ _ _ _ bindings hit miss =>
      cases hit
      cases miss with
      | headMiss _ _ _ _ miss => cases miss
      | tailMiss _ _ _ _ bindings hit miss => cases hit; cases miss
    | hit _ _ _ _ first rest head tail =>
      cases head
      cases tail with
      | hit _ _ _ _ second rest head tail =>
        cases head
        cases tail
        rfl


/-- A different nominal constructor cannot match the nullary pattern. -/
theorem different_nullary_constructor_misses (store : Store) (wanted actual : Constructor)
    (address resolved : Nat) (different : actual ≠ wanted)
    (resolution : Resolve store address resolved)
    (cell : readCell store resolved = some [.tag actual])
    {result : Option Environment}
    (attempt : Attempt store (.constructor wanted none) (.location address) result) : result = none := by
  cases attempt with
  | constructorNotLocation _ _ _ notLocation => exact False.elim (notLocation address rfl)
  | constructorWrongKind => rfl
  | constructorWrongTag => rfl
  | constructorNoPayload _ _ other stored otherResolution otherRead view =>
    have equal := resolved_fields_unique resolution otherResolution cell otherRead
    subst stored
    simp [constructorFields] at view
    simp_all
  | constructorUnexpectedPayload _ _ other stored value otherResolution otherRead view =>
    have equal := resolved_fields_unique resolution otherResolution cell otherRead
    subst stored
    simp [constructorFields] at view


/-- The checked list match selects its first arm for an actual Empty value. -/
theorem empty_selects_first (store : Store) (empty more : Constructor)
    (address resolved : Nat) (emptyBody moreBody : NodeId) (payload : Pattern)
    (resolution : Resolve store address resolved)
    (cell : readCell store resolved = some [.tag empty])
    {chosen : NodeId} {bindings : Environment}
    (selected : Selected store (.location address)
      [(.constructor empty none, emptyBody), (.constructor more (some payload), moreBody)] chosen bindings) :
    chosen = emptyBody ∧ bindings = [] := by
  cases selected with
  | first _ _ _ actual hit =>
    have same := nullary_constructor_match store empty address resolved resolution cell hit
    cases same
    exact ⟨rfl, rfl⟩
  | later _ _ _ _ _ miss _ =>
    have impossible := nullary_constructor_match store empty address resolved resolution cell miss
    contradiction


/-- A populated nominal value misses any nullary pattern. -/
theorem different_payload_constructor_misses (store : Store) (wanted actual : Constructor)
    (address resolved payload : Nat)
    (resolution : Resolve store address resolved)
    (cell : readCell store resolved = some [.tag actual, .location payload])
    {result : Option Environment}
    (attempt : Attempt store (.constructor wanted none) (.location address) result) : result = none := by
  cases attempt with
  | constructorNotLocation _ _ _ notLocation => exact False.elim (notLocation address rfl)
  | constructorWrongKind => rfl
  | constructorWrongTag => rfl
  | constructorNoPayload _ _ other stored otherResolution otherRead view =>
    have equal := resolved_fields_unique resolution otherResolution cell otherRead
    subst stored
    simp [constructorFields] at view
  | constructorUnexpectedPayload => rfl

/-- More selects the exact payload and binds the original entry and proper tail. -/
theorem more_constructor_match (store : Store) (tag : Constructor)
    (address resolved payload tuple entryAddress : Nat) (tail : Value)
    (entryName tailName : Binder)
    (resolution : Resolve store address resolved)
    (cell : readCell store resolved = some [.tag tag, .location payload])
    (payloadResolution : Resolve store payload tuple)
    (fields : readCell store tuple = some [.location entryAddress, tail])
    {result : Option Environment}
    (attempt : Attempt store (.constructor tag (some (.tuple [.binder entryName, .binder tailName])))
      (.location address) result) :
    result = some [(entryName, .location entryAddress), (tailName, tail)] := by
  cases attempt with
  | constructorNotLocation _ _ _ notLocation => exact False.elim (notLocation address rfl)
  | constructorWrongKind _ _ _ other stored otherResolution otherRead wrong =>
    have equal := resolved_fields_unique resolution otherResolution cell otherRead
    subst stored
    simp [constructorFields] at wrong
  | constructorWrongTag _ found _ _ other stored actual otherResolution otherRead view different =>
    have equal := resolved_fields_unique resolution otherResolution cell otherRead
    subst stored
    simp [constructorFields] at view
    simp_all
  | constructorPayload _ _ _ other stored value found otherResolution otherRead view inner =>
    have equal := resolved_fields_unique resolution otherResolution cell otherRead
    subst stored
    simp only [constructorFields, Option.some.injEq, Prod.mk.injEq, Option.some.injEq] at view
    rcases view with ⟨_, rfl⟩
    exact pair_binders_match store payload tuple entryName tailName (.location entryAddress) tail
      payloadResolution fields rfl inner
  | constructorMissingPayload _ _ _ other stored otherResolution otherRead view =>
    have equal := resolved_fields_unique resolution otherResolution cell otherRead
    subst stored
    simp [constructorFields] at view


/-- The checked list match selects More and binds its original fields. -/
theorem more_selects_second (store : Store) (empty more : Constructor)
    (address resolved payload tuple entryAddress : Nat) (tail : Value)
    (emptyBody moreBody : NodeId) (entryName tailName : Binder)
    (resolution : Resolve store address resolved)
    (cell : readCell store resolved = some [.tag more, .location payload])
    (payloadResolution : Resolve store payload tuple)
    (fields : readCell store tuple = some [.location entryAddress, tail])
    {chosen : NodeId} {bindings : Environment}
    (selected : Selected store (.location address)
      [(.constructor empty none, emptyBody),
       (.constructor more (some (.tuple [.binder entryName, .binder tailName])), moreBody)]
      chosen bindings) :
    chosen = moreBody ∧ bindings = [(entryName, .location entryAddress), (tailName, tail)] := by
  cases selected with
  | first _ _ _ _ hit =>
    have impossible := different_payload_constructor_misses store empty more address resolved payload
      resolution cell hit
    contradiction
  | later _ _ _ _ _ _ next =>
    cases next with
    | first _ _ _ actual hit =>
      have same := more_constructor_match store more address resolved payload tuple entryAddress tail
        entryName tailName resolution cell payloadResolution fields hit
      cases same
      exact ⟨rfl, rfl⟩
    | later _ _ _ _ _ _ next => cases next


/-- A checked Empty/More Core match on an actual Empty executes its Empty body. -/
theorem empty_match_executes_first (program : Program) (store finish : Store)
    (env : Environment) (node scrutinee : NodeId) (binder : Binder)
    (empty more : Constructor) (emptyBody moreBody : NodeId) (payload : Pattern)
    (address resolved : Nat) (result : Value)
    (shape : program node = some (.caseMatch scrutinee
      [(.constructor empty none, emptyBody), (.constructor more (some payload), moreBody)]))
    (variableShape : program scrutinee = some (.variable binder))
    (binding : CoreEval.lookup env binder = some (.location address))
    (resolution : Resolve store address resolved)
    (cell : readCell store resolved = some [.tag empty])
    (evaluation : Eval program env node store result finish) :
    Eval program env emptyBody store result finish := by
  obtain ⟨middle, value, chosen, bindings, scrutineeEval, selected, bodyEval⟩ :=
    case_match_inversion shape evaluation
  obtain ⟨actualBinding, sameStore⟩ := variable_inversion variableShape scrutineeEval
  have sameValue : value = .location address := by simp_all
  subst value
  subst middle
  obtain ⟨sameBody, sameBindings⟩ :=
    empty_selects_first store empty more address resolved emptyBody moreBody payload
      resolution cell selected
  subst chosen
  subst bindings
  simpa using bodyEval


/-- A checked More match executes with the original entry and proper tail. -/
theorem more_match_executes_second (program : Program) (store finish : Store)
    (env : Environment) (node scrutinee : NodeId) (binder : Binder)
    (empty more : Constructor) (emptyBody moreBody : NodeId) (entryName tailName : Binder)
    (address resolved payload tuple entryAddress : Nat) (tail result : Value)
    (shape : program node = some (.caseMatch scrutinee
      [(.constructor empty none, emptyBody),
       (.constructor more (some (.tuple [.binder entryName, .binder tailName])), moreBody)]))
    (variableShape : program scrutinee = some (.variable binder))
    (binding : CoreEval.lookup env binder = some (.location address))
    (resolution : Resolve store address resolved)
    (cell : readCell store resolved = some [.tag more, .location payload])
    (payloadResolution : Resolve store payload tuple)
    (fields : readCell store tuple = some [.location entryAddress, tail])
    (evaluation : Eval program env node store result finish) :
    Eval program ((tailName, tail) :: (entryName, .location entryAddress) :: env)
      moreBody store result finish := by
  obtain ⟨middle, value, chosen, bindings, scrutineeEval, selected, bodyEval⟩ :=
    case_match_inversion shape evaluation
  obtain ⟨actualBinding, sameStore⟩ := variable_inversion variableShape scrutineeEval
  have sameValue : value = .location address := by simp_all
  subst value
  subst middle
  obtain ⟨sameBody, sameBindings⟩ :=
    more_selects_second store empty more address resolved payload tuple entryAddress tail
      emptyBody moreBody entryName tailName resolution cell payloadResolution fields selected
  subst chosen
  subst bindings
  simpa using bodyEval


/-- The checked projection returns the actual first field of a Child entry. -/
theorem child_projection_returns_key (program : Program) (store finish : Store)
    (env : Environment) (node scrutinee body : NodeId) (parameter keyName destinationName : Binder)
    (child : Constructor) (address resolved payload tuple keyAddress : Nat) (destination result : Value)
    (distinct : keyName ≠ destinationName)
    (shape : program node = some (.caseMatch scrutinee
      [(.constructor child (some (.tuple [.binder keyName, .binder destinationName])), body)]))
    (scrutineeShape : program scrutinee = some (.variable parameter))
    (bodyShape : program body = some (.variable keyName))
    (binding : CoreEval.lookup env parameter = some (.location address))
    (resolution : Resolve store address resolved)
    (cell : readCell store resolved = some [.tag child, .location payload])
    (payloadResolution : Resolve store payload tuple)
    (fields : readCell store tuple = some [.location keyAddress, destination])
    (evaluation : Eval program env node store result finish) :
    result = .location keyAddress ∧ finish = store := by
  obtain ⟨middle, value, chosen, bindings, scrutineeEval, selected, bodyEval⟩ :=
    case_match_inversion shape evaluation
  obtain ⟨actualBinding, sameStore⟩ := variable_inversion scrutineeShape scrutineeEval
  have sameValue : value = .location address := by simp_all
  subst value
  subst middle
  have selectedFacts : chosen = body ∧
      bindings = [(keyName, .location keyAddress), (destinationName, destination)] := by
    cases selected with
    | first _ _ _ actual hit =>
      have same := more_constructor_match store child address resolved payload tuple keyAddress destination
        keyName destinationName resolution cell payloadResolution fields hit
      cases same
      exact ⟨rfl, rfl⟩
    | later _ _ _ _ _ _ next => cases next
  rcases selectedFacts with ⟨rfl, rfl⟩
  obtain ⟨found, unchanged⟩ := variable_inversion bodyShape bodyEval
  simp [CoreEval.lookup, Ne.symm distinct] at found
  exact ⟨found.symm, unchanged⟩


/-- A nominal identity location has at most one represented abstract identity. -/
theorem ident_unique (c : Constructors) (store : Store) (value : Value) (left right : Id)
    (leftRep : Ident c store value left) (rightRep : Ident c store value right) : left = right := by
  cases leftRep with
  | root address resolved resolution cell =>
    cases rightRep with
    | root => rfl
    | work _ other payload tuple allocator serial otherResolution otherCell _ _ =>
      have equal := resolved_fields_unique resolution otherResolution cell otherCell
      simp at equal
  | work address resolved payload tuple allocator serial resolution cell payloadResolution fields =>
    cases rightRep with
    | root _ other otherResolution otherCell =>
      have equal := resolved_fields_unique resolution otherResolution cell otherCell
      simp at equal
    | work _ other otherPayload otherTuple otherAllocator otherSerial otherResolution otherCell otherPayloadResolution otherFields =>
      have sameCell := resolved_fields_unique resolution otherResolution cell otherCell
      have samePayload : payload = otherPayload := by simpa using sameCell
      subst otherPayload
      have sameFields := resolved_fields_unique payloadResolution otherPayloadResolution fields otherFields
      simp at sameFields
      rcases sameFields with ⟨sameAllocator, sameSerial⟩
      have allocatorEq : allocator = otherAllocator := by omega
      simp [allocatorEq, sameSerial]


/-- The checked equality node compares its two actual integer bindings. -/
theorem integer_equal_variables (program : Program) (store finish : Store) (env : Environment)
    (node left right : NodeId) (leftName rightName : Binder) (leftValue rightValue : Int)
    (result : Value)
    (shape : program node = some (.integerEqual left right))
    (leftShape : program left = some (.variable leftName))
    (rightShape : program right = some (.variable rightName))
    (leftBinding : CoreEval.lookup env leftName = some (.integer leftValue))
    (rightBinding : CoreEval.lookup env rightName = some (.integer rightValue))
    (evaluation : Eval program env node store result finish) :
    result = .boolean (decide (leftValue = rightValue)) ∧ finish = store := by
  obtain ⟨middle, actualLeft, actualRight, leftEval, rightEval, resultEq⟩ :=
    integer_equal_inversion shape evaluation
  obtain ⟨leftFound, leftStore⟩ := variable_inversion leftShape leftEval
  obtain ⟨rightFound, rightStore⟩ := variable_inversion rightShape rightEval
  have leftSame : actualLeft = leftValue := by simpa [leftBinding] using leftFound.symm
  have rightSame : actualRight = rightValue := by simpa [rightBinding] using rightFound.symm
  subst actualLeft
  subst actualRight
  subst middle
  exact ⟨resultEq, rightStore⟩


/-- Boolean patterns have the same truth value as the scrutinee. -/
theorem boolean_pattern_result (store : Store) (expected actual : Bool)
    {result : Option Environment}
    (attempt : Attempt store (.boolean expected) (.boolean actual) result) :
    result = if expected = actual then some [] else none := by
  cases attempt with
  | booleanHit => simp
  | booleanMiss _ _ different =>
    have unequal : expected ≠ actual := by
      intro same
      subst expected
      exact different rfl
    simp [unequal]

/-- The checked true/false match selects the arm matching the actual boolean. -/
theorem boolean_selects (store : Store) (actual : Bool) (trueBody falseBody : NodeId)
    {chosen : NodeId} {bindings : Environment}
    (selected : Selected store (.boolean actual)
      [(.boolean true, trueBody), (.boolean false, falseBody)] chosen bindings) :
    chosen = (if actual then trueBody else falseBody) ∧ bindings = [] := by
  cases actual with
  | false =>
    cases selected with
    | first _ _ _ _ hit =>
      have impossible := boolean_pattern_result store true false hit
      contradiction
    | later _ _ _ _ _ _ next =>
      cases next with
      | first _ _ _ _ hit =>
        have same := boolean_pattern_result store false false hit
        simp at same
        cases same
        exact ⟨rfl, rfl⟩
      | later _ _ _ _ _ _ next => cases next
  | true =>
    cases selected with
    | first _ _ _ _ hit =>
      have same := boolean_pattern_result store true true hit
      simp at same
      cases same
      exact ⟨rfl, rfl⟩
    | later _ _ _ _ _ miss _ =>
      have impossible := boolean_pattern_result store true true miss
      contradiction


/-- A checked integer-comparison branch executes the arm for its real operands. -/
theorem integer_equal_match_executes (program : Program) (store finish : Store) (env : Environment)
    (node comparison left right trueBody falseBody : NodeId) (leftName rightName : Binder)
    (leftValue rightValue : Int) (result : Value)
    (shape : program node = some (.caseMatch comparison
      [(.boolean true, trueBody), (.boolean false, falseBody)]))
    (comparisonShape : program comparison = some (.integerEqual left right))
    (leftShape : program left = some (.variable leftName))
    (rightShape : program right = some (.variable rightName))
    (leftBinding : CoreEval.lookup env leftName = some (.integer leftValue))
    (rightBinding : CoreEval.lookup env rightName = some (.integer rightValue))
    (evaluation : Eval program env node store result finish) :
    Eval program env (if leftValue = rightValue then trueBody else falseBody) store result finish := by
  obtain ⟨middle, value, chosen, bindings, compareEval, selected, bodyEval⟩ :=
    case_match_inversion shape evaluation
  obtain ⟨sameValue, sameStore⟩ := integer_equal_variables program store middle env comparison left right
    leftName rightName leftValue rightValue value comparisonShape leftShape rightShape
    leftBinding rightBinding compareEval
  subst value
  subst middle
  obtain ⟨sameBody, sameBindings⟩ :=
    boolean_selects store (decide (leftValue = rightValue)) trueBody falseBody selected
  subst chosen
  subst bindings
  simpa using bodyEval


/-- The comparator's pair-of-Root pattern matches two actual Root values. -/
theorem root_pair_pattern_match (store : Store) (root : Constructor)
    (pair pairResolved left leftResolved right rightResolved : Nat)
    (pairResolution : Resolve store pair pairResolved)
    (pairCell : readCell store pairResolved = some [.location left, .location right])
    (leftResolution : Resolve store left leftResolved)
    (leftCell : readCell store leftResolved = some [.tag root])
    (rightResolution : Resolve store right rightResolved)
    (rightCell : readCell store rightResolved = some [.tag root])
    {result : Option Environment}
    (attempt : Attempt store (.tuple [.constructor root none, .constructor root none])
      (.location pair) result) : result = some [] := by
  cases attempt with
  | tupleNotLocation _ _ notLocation => exact False.elim (notLocation pair rfl)
  | tupleWrongKind _ _ other stored otherResolution otherRead wrong =>
    have equal := resolved_fields_unique pairResolution otherResolution pairCell otherRead
    subst stored
    simp [tupleFields] at wrong
  | tupleFields _ _ other stored values found otherResolution otherRead view attempts =>
    have equal := resolved_fields_unique pairResolution otherResolution pairCell otherRead
    subst stored
    simp [tupleFields] at view
    subst values
    cases attempts with
    | headMiss _ _ _ _ miss =>
      have impossible := nullary_constructor_match store root left leftResolved leftResolution leftCell miss
      contradiction
    | tailMiss _ _ _ _ first hit miss =>
      cases miss with
      | headMiss _ _ _ _ miss =>
        have impossible := nullary_constructor_match store root right rightResolved rightResolution rightCell miss
        contradiction
      | tailMiss _ _ _ _ first hit miss => cases miss
    | hit _ _ _ _ first rest head tail =>
      have firstEq := nullary_constructor_match store root left leftResolved leftResolution leftCell head
      cases firstEq
      cases tail with
      | hit _ _ _ _ second rest head tail =>
        have secondEq := nullary_constructor_match store root right rightResolved rightResolution rightCell head
        cases secondEq
        cases tail
        rfl


/-- A populated constructor binds its exact two payload fields. -/
theorem payload_pair_binders_match (store : Store) (tag : Constructor)
    (address resolved payload tuple : Nat) (firstValue tail : Value)
    (entryName tailName : Binder)
    (resolution : Resolve store address resolved)
    (cell : readCell store resolved = some [.tag tag, .location payload])
    (payloadResolution : Resolve store payload tuple)
    (fields : readCell store tuple = some [firstValue, tail])
    (plain : tupleFields [firstValue, tail] = some [firstValue, tail])
    {result : Option Environment}
    (attempt : Attempt store (.constructor tag (some (.tuple [.binder entryName, .binder tailName])))
      (.location address) result) :
    result = some [(entryName, firstValue), (tailName, tail)] := by
  cases attempt with
  | constructorNotLocation _ _ _ notLocation => exact False.elim (notLocation address rfl)
  | constructorWrongKind _ _ _ other stored otherResolution otherRead wrong =>
    have equal := resolved_fields_unique resolution otherResolution cell otherRead
    subst stored
    simp [constructorFields] at wrong
  | constructorWrongTag _ found _ _ other stored actual otherResolution otherRead view different =>
    have equal := resolved_fields_unique resolution otherResolution cell otherRead
    subst stored
    simp [constructorFields] at view
    simp_all
  | constructorPayload _ _ _ other stored value found otherResolution otherRead view inner =>
    have equal := resolved_fields_unique resolution otherResolution cell otherRead
    subst stored
    simp only [constructorFields, Option.some.injEq, Prod.mk.injEq, Option.some.injEq] at view
    rcases view with ⟨_, rfl⟩
    exact pair_binders_match store payload tuple entryName tailName (firstValue) tail
      payloadResolution fields plain inner
  | constructorMissingPayload _ _ _ other stored otherResolution otherRead view =>
    have equal := resolved_fields_unique resolution otherResolution cell otherRead
    subst stored
    simp [constructorFields] at view



/-- A Work pattern binds its two actual integer fields. -/
theorem work_pattern_match (store : Store) (work : Constructor)
    (address resolved payload tuple : Nat) (allocator : Nat) (serial : Int)
    (allocatorName serialName : Binder)
    (resolution : Resolve store address resolved)
    (cell : readCell store resolved = some [.tag work, .location payload])
    (payloadResolution : Resolve store payload tuple)
    (fields : readCell store tuple = some [.integer (Int.ofNat allocator), .integer serial])
    {result : Option Environment}
    (attempt : Attempt store (.constructor work (some (.tuple [.binder allocatorName, .binder serialName])))
      (.location address) result) :
    result = some [(allocatorName, .integer (Int.ofNat allocator)), (serialName, .integer serial)] := by
  exact payload_pair_binders_match store work address resolved payload tuple
    (.integer (Int.ofNat allocator)) (.integer serial) allocatorName serialName resolution cell
    payloadResolution fields rfl attempt

/-- The comparator's Work/Work pattern binds all four actual integers in order. -/
theorem work_pair_pattern_match (store : Store) (work : Constructor)
    (pair pairResolved left leftResolved leftPayload leftTuple right rightResolved rightPayload rightTuple : Nat)
    (leftAllocator rightAllocator : Nat) (leftSerial rightSerial : Int)
    (leftAllocatorName leftSerialName rightAllocatorName rightSerialName : Binder)
    (pairResolution : Resolve store pair pairResolved)
    (pairCell : readCell store pairResolved = some [.location left, .location right])
    (leftResolution : Resolve store left leftResolved)
    (leftCell : readCell store leftResolved = some [.tag work, .location leftPayload])
    (leftPayloadResolution : Resolve store leftPayload leftTuple)
    (leftFields : readCell store leftTuple = some [.integer (Int.ofNat leftAllocator), .integer leftSerial])
    (rightResolution : Resolve store right rightResolved)
    (rightCell : readCell store rightResolved = some [.tag work, .location rightPayload])
    (rightPayloadResolution : Resolve store rightPayload rightTuple)
    (rightFields : readCell store rightTuple = some [.integer (Int.ofNat rightAllocator), .integer rightSerial])
    {result : Option Environment}
    (attempt : Attempt store (.tuple [
      .constructor work (some (.tuple [.binder leftAllocatorName, .binder leftSerialName])),
      .constructor work (some (.tuple [.binder rightAllocatorName, .binder rightSerialName]))])
      (.location pair) result) :
    result = some [(leftAllocatorName, .integer (Int.ofNat leftAllocator)),
      (leftSerialName, .integer leftSerial), (rightAllocatorName, .integer (Int.ofNat rightAllocator)),
      (rightSerialName, .integer rightSerial)] := by
  cases attempt with
  | tupleNotLocation _ _ notLocation => exact False.elim (notLocation pair rfl)
  | tupleWrongKind _ _ other stored otherResolution otherRead wrong =>
    have equal := resolved_fields_unique pairResolution otherResolution pairCell otherRead
    subst stored
    simp [tupleFields] at wrong
  | tupleFields _ _ other stored values found otherResolution otherRead view attempts =>
    have equal := resolved_fields_unique pairResolution otherResolution pairCell otherRead
    subst stored
    simp [tupleFields] at view
    subst values
    cases attempts with
    | headMiss _ _ _ _ miss =>
      have impossible := work_pattern_match store work left leftResolved leftPayload leftTuple
        leftAllocator leftSerial leftAllocatorName leftSerialName leftResolution leftCell
        leftPayloadResolution leftFields miss
      contradiction
    | tailMiss _ _ _ _ first hit miss =>
      cases miss with
      | headMiss _ _ _ _ miss =>
        have impossible := work_pattern_match store work right rightResolved rightPayload rightTuple
          rightAllocator rightSerial rightAllocatorName rightSerialName rightResolution rightCell
          rightPayloadResolution rightFields miss
        contradiction
      | tailMiss _ _ _ _ first hit miss => cases miss
    | hit _ _ _ _ first rest head tail =>
      have firstEq := work_pattern_match store work left leftResolved leftPayload leftTuple
        leftAllocator leftSerial leftAllocatorName leftSerialName leftResolution leftCell
        leftPayloadResolution leftFields head
      cases firstEq
      cases tail with
      | hit _ _ _ _ second rest head tail =>
        have secondEq := work_pattern_match store work right rightResolved rightPayload rightTuple
          rightAllocator rightSerial rightAllocatorName rightSerialName rightResolution rightCell
          rightPayloadResolution rightFields head
        cases secondEq
        cases tail
        rfl


/-- A Root/Root pattern misses when its first operand is a populated Work. -/
theorem root_pair_misses_work (store : Store) (root work : Constructor)
    (pair pairResolved left leftResolved leftPayload right : Nat)
    (pairResolution : Resolve store pair pairResolved)
    (pairCell : readCell store pairResolved = some [.location left, .location right])
    (leftResolution : Resolve store left leftResolved)
    (leftCell : readCell store leftResolved = some [.tag work, .location leftPayload])
    {result : Option Environment}
    (attempt : Attempt store (.tuple [.constructor root none, .constructor root none])
      (.location pair) result) : result = none := by
  cases attempt with
  | tupleNotLocation _ _ notLocation => exact False.elim (notLocation pair rfl)
  | tupleWrongKind => rfl
  | tupleFields _ _ other stored values found otherResolution otherRead view attempts =>
    have equal := resolved_fields_unique pairResolution otherResolution pairCell otherRead
    subst stored
    simp [tupleFields] at view
    subst values
    cases attempts with
    | headMiss => rfl
    | tailMiss _ _ _ _ first hit miss =>
      have impossible := different_payload_constructor_misses store root work left leftResolved leftPayload
        leftResolution leftCell hit
      contradiction
    | hit _ _ _ _ first rest hit tail =>
      have impossible := different_payload_constructor_misses store root work left leftResolved leftPayload
        leftResolution leftCell hit
      contradiction


/-- The checked comparator chooses Work/Work and binds its four real fields. -/
theorem work_pair_selects_second (store : Store) (root work : Constructor)
    (pair pairResolved left leftResolved leftPayload leftTuple right rightResolved rightPayload rightTuple : Nat)
    (leftAllocator rightAllocator : Nat) (leftSerial rightSerial : Int)
    (leftAllocatorName leftSerialName rightAllocatorName rightSerialName : Binder)
    (rootBody workBody defaultBody : NodeId)
    (pairResolution : Resolve store pair pairResolved)
    (pairCell : readCell store pairResolved = some [.location left, .location right])
    (leftResolution : Resolve store left leftResolved)
    (leftCell : readCell store leftResolved = some [.tag work, .location leftPayload])
    (leftPayloadResolution : Resolve store leftPayload leftTuple)
    (leftFields : readCell store leftTuple = some [.integer (Int.ofNat leftAllocator), .integer leftSerial])
    (rightResolution : Resolve store right rightResolved)
    (rightCell : readCell store rightResolved = some [.tag work, .location rightPayload])
    (rightPayloadResolution : Resolve store rightPayload rightTuple)
    (rightFields : readCell store rightTuple = some [.integer (Int.ofNat rightAllocator), .integer rightSerial])
    {chosen : NodeId} {bindings : Environment}
    (selected : Selected store (.location pair) [
      (.tuple [.constructor root none, .constructor root none], rootBody),
      (.tuple [
        .constructor work (some (.tuple [.binder leftAllocatorName, .binder leftSerialName])),
        .constructor work (some (.tuple [.binder rightAllocatorName, .binder rightSerialName]))], workBody),
      (.wildcard, defaultBody)] chosen bindings) :
    chosen = workBody ∧ bindings = [
      (leftAllocatorName, .integer (Int.ofNat leftAllocator)), (leftSerialName, .integer leftSerial),
      (rightAllocatorName, .integer (Int.ofNat rightAllocator)), (rightSerialName, .integer rightSerial)] := by
  cases selected with
  | first _ _ _ _ hit =>
    have impossible := root_pair_misses_work store root work pair pairResolved left leftResolved leftPayload right
      pairResolution pairCell leftResolution leftCell hit
    contradiction
  | later _ _ _ _ _ _ next =>
    cases next with
    | first _ _ _ actual hit =>
      have same := work_pair_pattern_match store work pair pairResolved left leftResolved leftPayload leftTuple
        right rightResolved rightPayload rightTuple leftAllocator rightAllocator leftSerial rightSerial
        leftAllocatorName leftSerialName rightAllocatorName rightSerialName pairResolution pairCell
        leftResolution leftCell leftPayloadResolution leftFields rightResolution rightCell
        rightPayloadResolution rightFields hit
      cases same
      exact ⟨rfl, rfl⟩
    | later _ _ _ _ _ miss _ =>
      have impossible := work_pair_pattern_match store work pair pairResolved left leftResolved leftPayload leftTuple
        right rightResolved rightPayload rightTuple leftAllocator rightAllocator leftSerial rightSerial
        leftAllocatorName leftSerialName rightAllocatorName rightSerialName pairResolution pairCell
        leftResolution leftCell leftPayloadResolution leftFields rightResolution rightCell
        rightPayloadResolution rightFields miss
      contradiction


/-- The checked comparator chooses its Root/Root branch for two Root IDs. -/
theorem root_pair_selects_first (store : Store) (root : Constructor)
    (pair pairResolved left leftResolved right rightResolved : Nat)
    (rootBody workBody defaultBody : NodeId) (workPattern : Pattern)
    (pairResolution : Resolve store pair pairResolved)
    (pairCell : readCell store pairResolved = some [.location left, .location right])
    (leftResolution : Resolve store left leftResolved)
    (leftCell : readCell store leftResolved = some [.tag root])
    (rightResolution : Resolve store right rightResolved)
    (rightCell : readCell store rightResolved = some [.tag root])
    {chosen : NodeId} {bindings : Environment}
    (selected : Selected store (.location pair) [
      (.tuple [.constructor root none, .constructor root none], rootBody),
      (workPattern, workBody), (.wildcard, defaultBody)] chosen bindings) :
    chosen = rootBody ∧ bindings = [] := by
  cases selected with
  | first _ _ _ actual hit =>
    have same := root_pair_pattern_match store root pair pairResolved left leftResolved right rightResolved
      pairResolution pairCell leftResolution leftCell rightResolution rightCell hit
    cases same
    exact ⟨rfl, rfl⟩
  | later _ _ _ _ _ miss _ =>
    have impossible := root_pair_pattern_match store root pair pairResolved left leftResolved right rightResolved
      pairResolution pairCell leftResolution leftCell rightResolution rightCell miss
    contradiction


/-- A populated constructor pattern misses every actual nullary constructor. -/
theorem payload_pattern_misses_nullary (store : Store) (wanted actual : Constructor)
    (payload : Pattern) (address resolved : Nat)
    (resolution : Resolve store address resolved)
    (cell : readCell store resolved = some [.tag actual])
    {result : Option Environment}
    (attempt : Attempt store (.constructor wanted (some payload)) (.location address) result) : result = none := by
  cases attempt with
  | constructorNotLocation _ _ _ notLocation => exact False.elim (notLocation address rfl)
  | constructorWrongKind => rfl
  | constructorWrongTag => rfl
  | constructorPayload _ _ _ other stored value result otherResolution otherRead view inner =>
    have equal := resolved_fields_unique resolution otherResolution cell otherRead
    subst stored
    simp [constructorFields] at view
  | constructorMissingPayload => rfl

/-- A two-field pattern misses when its first field necessarily misses. -/
theorem tuple_pair_head_misses (store : Store) (firstPattern secondPattern : Pattern)
    (pair pairResolved : Nat) (first second : Value)
    (pairResolution : Resolve store pair pairResolved)
    (pairCell : readCell store pairResolved = some [first, second])
    (plain : tupleFields [first, second] = some [first, second])
    (firstMiss : ∀ result, Attempt store firstPattern first result → result = none)
    {result : Option Environment}
    (attempt : Attempt store (.tuple [firstPattern, secondPattern]) (.location pair) result) : result = none := by
  cases attempt with
  | tupleNotLocation _ _ notLocation => exact False.elim (notLocation pair rfl)
  | tupleWrongKind _ _ other stored otherResolution otherRead wrong =>
    have equal := resolved_fields_unique pairResolution otherResolution pairCell otherRead
    subst stored
    simp_all
  | tupleFields _ _ other stored values found otherResolution otherRead view attempts =>
    have equal := resolved_fields_unique pairResolution otherResolution pairCell otherRead
    subst stored
    rw [plain] at view
    have same := Option.some.inj view
    subst values
    cases attempts with
    | headMiss => rfl
    | tailMiss _ _ _ _ first hit miss =>
      have impossible := firstMiss _ hit
      contradiction
    | hit _ _ _ _ first rest hit tail =>
      have impossible := firstMiss _ hit
      contradiction

/-- A two-field pattern misses when its second field necessarily misses. -/
theorem tuple_pair_tail_misses (store : Store) (firstPattern secondPattern : Pattern)
    (pair pairResolved : Nat) (first second : Value)
    (pairResolution : Resolve store pair pairResolved)
    (pairCell : readCell store pairResolved = some [first, second])
    (plain : tupleFields [first, second] = some [first, second])
    (secondMiss : ∀ result, Attempt store secondPattern second result → result = none)
    {result : Option Environment}
    (attempt : Attempt store (.tuple [firstPattern, secondPattern]) (.location pair) result) : result = none := by
  cases attempt with
  | tupleNotLocation _ _ notLocation => exact False.elim (notLocation pair rfl)
  | tupleWrongKind _ _ other stored otherResolution otherRead wrong =>
    have equal := resolved_fields_unique pairResolution otherResolution pairCell otherRead
    subst stored
    simp_all
  | tupleFields _ _ other stored values found otherResolution otherRead view attempts =>
    have equal := resolved_fields_unique pairResolution otherResolution pairCell otherRead
    subst stored
    rw [plain] at view
    have same := Option.some.inj view
    subst values
    cases attempts with
    | headMiss => rfl
    | tailMiss => rfl
    | hit _ _ _ _ first rest hit tail =>
      cases tail with
      | hit _ _ _ _ second rest secondHit remaining =>
        have impossible := secondMiss _ secondHit
        contradiction


/-- The comparator's wildcard arm handles an actual Root/Work pair. -/
theorem root_work_selects_default (store : Store) (root work : Constructor)
    (pair pairResolved left leftResolved right rightResolved rightPayload : Nat)
    (leftPattern rightPattern : Pattern) (rootBody workBody defaultBody : NodeId)
    (pairResolution : Resolve store pair pairResolved)
    (pairCell : readCell store pairResolved = some [.location left, .location right])
    (leftResolution : Resolve store left leftResolved)
    (leftCell : readCell store leftResolved = some [.tag root])
    (rightResolution : Resolve store right rightResolved)
    (rightCell : readCell store rightResolved = some [.tag work, .location rightPayload])
    {chosen : NodeId} {bindings : Environment}
    (selected : Selected store (.location pair) [
      (.tuple [.constructor root none, .constructor root none], rootBody),
      (.tuple [.constructor work (some leftPattern), .constructor work (some rightPattern)], workBody),
      (.wildcard, defaultBody)] chosen bindings) : chosen = defaultBody ∧ bindings = [] := by
  have firstMiss : ∀ result, Attempt store (.tuple [.constructor root none, .constructor root none])
      (.location pair) result → result = none := by
    intro result attempt
    apply tuple_pair_tail_misses store (.constructor root none) (.constructor root none)
      pair pairResolved (.location left) (.location right) pairResolution pairCell rfl
    · intro result inner
      exact different_payload_constructor_misses store root work right rightResolved rightPayload
        rightResolution rightCell inner
    · exact attempt
  have secondMiss : ∀ result, Attempt store
      (.tuple [.constructor work (some leftPattern), .constructor work (some rightPattern)])
      (.location pair) result → result = none := by
    intro result attempt
    apply tuple_pair_head_misses store (.constructor work (some leftPattern))
      (.constructor work (some rightPattern)) pair pairResolved (.location left) (.location right)
      pairResolution pairCell rfl
    · intro result inner
      exact payload_pattern_misses_nullary store work root leftPattern left leftResolved leftResolution leftCell inner
    · exact attempt
  cases selected with
  | first _ _ _ _ hit => have impossible := firstMiss _ hit; contradiction
  | later _ _ _ _ _ _ next =>
    cases next with
    | first _ _ _ _ hit => have impossible := secondMiss _ hit; contradiction
    | later _ _ _ _ _ _ final =>
      cases final with
      | first _ _ _ _ hit => cases hit; exact ⟨rfl, rfl⟩
      | later _ _ _ _ _ miss _ => cases miss


/-- The comparator's wildcard arm handles an actual Work/Root pair. -/
theorem work_root_selects_default (store : Store) (root work : Constructor)
    (pair pairResolved left leftResolved leftPayload right rightResolved : Nat)
    (leftPattern rightPattern : Pattern) (rootBody workBody defaultBody : NodeId)
    (pairResolution : Resolve store pair pairResolved)
    (pairCell : readCell store pairResolved = some [.location left, .location right])
    (leftResolution : Resolve store left leftResolved)
    (leftCell : readCell store leftResolved = some [.tag work, .location leftPayload])
    (rightResolution : Resolve store right rightResolved)
    (rightCell : readCell store rightResolved = some [.tag root])
    {chosen : NodeId} {bindings : Environment}
    (selected : Selected store (.location pair) [
      (.tuple [.constructor root none, .constructor root none], rootBody),
      (.tuple [.constructor work (some leftPattern), .constructor work (some rightPattern)], workBody),
      (.wildcard, defaultBody)] chosen bindings) : chosen = defaultBody ∧ bindings = [] := by
  have firstMiss : ∀ result, Attempt store (.tuple [.constructor root none, .constructor root none])
      (.location pair) result → result = none := by
    intro result attempt
    exact root_pair_misses_work store root work pair pairResolved left leftResolved leftPayload right
      pairResolution pairCell leftResolution leftCell attempt
  have secondMiss : ∀ result, Attempt store
      (.tuple [.constructor work (some leftPattern), .constructor work (some rightPattern)])
      (.location pair) result → result = none := by
    intro result attempt
    apply tuple_pair_tail_misses store (.constructor work (some leftPattern))
      (.constructor work (some rightPattern)) pair pairResolved (.location left) (.location right)
      pairResolution pairCell rfl
    · intro result inner
      exact payload_pattern_misses_nullary store work root rightPattern right rightResolved rightResolution rightCell inner
    · exact attempt
  cases selected with
  | first _ _ _ _ hit => have impossible := firstMiss _ hit; contradiction
  | later _ _ _ _ _ _ next =>
    cases next with
    | first _ _ _ _ hit => have impossible := secondMiss _ hit; contradiction
    | later _ _ _ _ _ _ final =>
      cases final with
      | first _ _ _ _ hit => cases hit; exact ⟨rfl, rfl⟩
      | later _ _ _ _ _ miss _ => cases miss


/-- A checked Root/Root comparator match executes its true literal branch. -/
theorem root_root_comparator_match (c : Constructors) (program : Program)
    (node pair left right rootBody workBody defaultBody : NodeId) (workPattern : Pattern)
    (env : Environment) (start finish : Store) (result leftValue rightValue : Value)
    (checked : CheckedTuple program pair none [left, right]) (leftName rightName : Binder)
    (shape : program node = some (.caseMatch pair [
      (.tuple [.constructor c.root none, .constructor c.root none], rootBody),
      (workPattern, workBody), (.wildcard, defaultBody)]))
    (rootBodyShape : program rootBody = some (.boolean true))
    (leftShape : program left = some (.variable leftName))
    (rightShape : program right = some (.variable rightName))
    (leftFresh : leftName ≠ checked.contextBinder)
    (rightFresh : rightName ≠ checked.contextBinder)
    (leftBinding : CoreEval.lookup env leftName = some leftValue)
    (rightBinding : CoreEval.lookup env rightName = some rightValue)
    (bounded : BoundedLocations start)
    (leftRoot : Ident c start leftValue .root) (rightRoot : Ident c start rightValue .root)
    (evaluation : Eval program env node start result finish) : result = .boolean true := by
  obtain ⟨middle, value, chosen, bindings, pairEval, selected, bodyEval⟩ :=
    case_match_inversion shape evaluation
  obtain ⟨location, pairValue, pairResolution, pairCell, leftAfter, rightAfter, _⟩ :=
    checked_id_pair_tuple c program pair left right env start middle value leftValue rightValue
      .root .root checked leftName rightName leftShape rightShape leftFresh rightFresh
      leftBinding rightBinding bounded leftRoot rightRoot pairEval
  subst value
  cases leftAfter with
  | root leftAddress leftResolved leftResolution leftCell =>
    cases rightAfter with
    | root rightAddress rightResolved rightResolution rightCell =>
      obtain ⟨sameBody, sameBindings⟩ := root_pair_selects_first middle c.root location location
        leftAddress leftResolved rightAddress rightResolved rootBody workBody defaultBody workPattern
        pairResolution pairCell leftResolution leftCell rightResolution rightCell selected
      subst chosen
      subst bindings
      have literal := boolean_inversion rootBodyShape bodyEval
      exact literal.1


/-- A checked Root/Work comparator match executes its false default branch. -/
theorem root_work_comparator_match (c : Constructors) (program : Program)
    (node pair left right rootBody workBody defaultBody : NodeId) (leftPattern rightPattern : Pattern)
    (env : Environment) (start finish : Store) (result leftValue rightValue : Value)
    (rightAllocator : Nat) (rightSerial : Int)
    (checked : CheckedTuple program pair none [left, right]) (leftName rightName : Binder)
    (shape : program node = some (.caseMatch pair [
      (.tuple [.constructor c.root none, .constructor c.root none], rootBody),
      (.tuple [.constructor c.work (some leftPattern), .constructor c.work (some rightPattern)], workBody),
      (.wildcard, defaultBody)]))
    (defaultShape : program defaultBody = some (.boolean false))
    (leftShape : program left = some (.variable leftName))
    (rightShape : program right = some (.variable rightName))
    (leftFresh : leftName ≠ checked.contextBinder) (rightFresh : rightName ≠ checked.contextBinder)
    (leftBinding : CoreEval.lookup env leftName = some leftValue)
    (rightBinding : CoreEval.lookup env rightName = some rightValue)
    (bounded : BoundedLocations start)
    (leftRoot : Ident c start leftValue .root)
    (rightWork : Ident c start rightValue (.work rightAllocator rightSerial))
    (evaluation : Eval program env node start result finish) : result = .boolean false := by
  obtain ⟨middle, value, chosen, bindings, pairEval, selected, bodyEval⟩ := case_match_inversion shape evaluation
  obtain ⟨location, pairValue, pairResolution, pairCell, leftAfter, rightAfter, _⟩ :=
    checked_id_pair_tuple c program pair left right env start middle value leftValue rightValue
      .root (.work rightAllocator rightSerial) checked leftName rightName leftShape rightShape leftFresh rightFresh
      leftBinding rightBinding bounded leftRoot rightWork pairEval
  subst value
  cases leftAfter with
  | root leftAddress leftResolved leftResolution leftCell =>
    cases rightAfter with
    | work rightAddress rightResolved rightPayload rightTuple allocator serial rightResolution rightCell _ _ =>
      obtain ⟨sameBody, sameBindings⟩ := root_work_selects_default middle c.root c.work
        location location leftAddress leftResolved rightAddress rightResolved rightPayload
        leftPattern rightPattern rootBody workBody defaultBody pairResolution pairCell
        leftResolution leftCell rightResolution rightCell selected
      subst chosen
      subst bindings
      exact (boolean_inversion defaultShape bodyEval).1

/-- A checked Work/Root comparator match executes its false default branch. -/
theorem work_root_comparator_match (c : Constructors) (program : Program)
    (node pair left right rootBody workBody defaultBody : NodeId) (leftPattern rightPattern : Pattern)
    (env : Environment) (start finish : Store) (result leftValue rightValue : Value)
    (leftAllocator : Nat) (leftSerial : Int)
    (checked : CheckedTuple program pair none [left, right]) (leftName rightName : Binder)
    (shape : program node = some (.caseMatch pair [
      (.tuple [.constructor c.root none, .constructor c.root none], rootBody),
      (.tuple [.constructor c.work (some leftPattern), .constructor c.work (some rightPattern)], workBody),
      (.wildcard, defaultBody)]))
    (defaultShape : program defaultBody = some (.boolean false))
    (leftShape : program left = some (.variable leftName))
    (rightShape : program right = some (.variable rightName))
    (leftFresh : leftName ≠ checked.contextBinder) (rightFresh : rightName ≠ checked.contextBinder)
    (leftBinding : CoreEval.lookup env leftName = some leftValue)
    (rightBinding : CoreEval.lookup env rightName = some rightValue)
    (bounded : BoundedLocations start)
    (leftWork : Ident c start leftValue (.work leftAllocator leftSerial))
    (rightRoot : Ident c start rightValue .root)
    (evaluation : Eval program env node start result finish) : result = .boolean false := by
  obtain ⟨middle, value, chosen, bindings, pairEval, selected, bodyEval⟩ := case_match_inversion shape evaluation
  obtain ⟨location, pairValue, pairResolution, pairCell, leftAfter, rightAfter, _⟩ :=
    checked_id_pair_tuple c program pair left right env start middle value leftValue rightValue
      (.work leftAllocator leftSerial) .root checked leftName rightName leftShape rightShape leftFresh rightFresh
      leftBinding rightBinding bounded leftWork rightRoot pairEval
  subst value
  cases leftAfter with
  | work leftAddress leftResolved leftPayload leftTuple allocator serial leftResolution leftCell _ _ =>
    cases rightAfter with
    | root rightAddress rightResolved rightResolution rightCell =>
      obtain ⟨sameBody, sameBindings⟩ := work_root_selects_default middle c.root c.work
        location location leftAddress leftResolved leftPayload rightAddress rightResolved
        leftPattern rightPattern rootBody workBody defaultBody pairResolution pairCell
        leftResolution leftCell rightResolution rightCell selected
      subst chosen
      subst bindings
      exact (boolean_inversion defaultShape bodyEval).1


/-- The Work branch evaluates both real integer fields with the checked short circuit. -/
theorem work_comparison_body (program : Program) (store finish : Store) (env : Environment)
    (node allocatorCompare allocatorLeft allocatorRight serialCompare serialLeft serialRight falseBody : NodeId)
    (leftAllocatorName rightAllocatorName leftSerialName rightSerialName : Binder)
    (leftAllocator rightAllocator : Nat) (leftSerial rightSerial : Int) (result : Value)
    (shape : program node = some (.caseMatch allocatorCompare
      [(.boolean true, serialCompare), (.boolean false, falseBody)]))
    (allocatorShape : program allocatorCompare = some (.integerEqual allocatorLeft allocatorRight))
    (allocatorLeftShape : program allocatorLeft = some (.variable leftAllocatorName))
    (allocatorRightShape : program allocatorRight = some (.variable rightAllocatorName))
    (serialShape : program serialCompare = some (.integerEqual serialLeft serialRight))
    (serialLeftShape : program serialLeft = some (.variable leftSerialName))
    (serialRightShape : program serialRight = some (.variable rightSerialName))
    (falseShape : program falseBody = some (.boolean false))
    (leftAllocatorBinding : CoreEval.lookup env leftAllocatorName = some (.integer (Int.ofNat leftAllocator)))
    (rightAllocatorBinding : CoreEval.lookup env rightAllocatorName = some (.integer (Int.ofNat rightAllocator)))
    (leftSerialBinding : CoreEval.lookup env leftSerialName = some (.integer leftSerial))
    (rightSerialBinding : CoreEval.lookup env rightSerialName = some (.integer rightSerial))
    (evaluation : Eval program env node store result finish) :
    result = .boolean (Ash.NetworkLedger.CoreRemoval.compareId
      (.work leftAllocator leftSerial) (.work rightAllocator rightSerial)) ∧ finish = store := by
  have selected := integer_equal_match_executes program store finish env node allocatorCompare
    allocatorLeft allocatorRight serialCompare falseBody leftAllocatorName rightAllocatorName
    (Int.ofNat leftAllocator) (Int.ofNat rightAllocator) result shape allocatorShape
    allocatorLeftShape allocatorRightShape leftAllocatorBinding rightAllocatorBinding evaluation
  by_cases equal : leftAllocator = rightAllocator
  · subst rightAllocator
    simp at selected
    obtain ⟨resultEq, stateEq⟩ := integer_equal_variables program store finish env serialCompare
      serialLeft serialRight leftSerialName rightSerialName leftSerial rightSerial result serialShape
      serialLeftShape serialRightShape leftSerialBinding rightSerialBinding selected
    simpa [Ash.NetworkLedger.CoreRemoval.compareId] using And.intro resultEq stateEq
  · have integerUnequal : Int.ofNat leftAllocator ≠ Int.ofNat rightAllocator := by
      intro same
      exact equal (Int.ofNat_inj.mp same)
    rw [if_neg integerUnequal] at selected
    obtain ⟨resultEq, stateEq⟩ := boolean_inversion falseShape selected
    simpa [Ash.NetworkLedger.CoreRemoval.compareId, equal] using And.intro resultEq stateEq


/-- Distinct pattern binders recover all four Work integers after extension. -/
theorem work_bindings_lookup (env : Environment)
    (a b c d : Binder) (av bv cv dv : Int) (unique : [a, b, c, d].Nodup) :
    CoreEval.lookup ([(a, .integer av), (b, .integer bv), (c, .integer cv), (d, .integer dv)].reverse ++ env) a = some (.integer av) ∧
    CoreEval.lookup ([(a, .integer av), (b, .integer bv), (c, .integer cv), (d, .integer dv)].reverse ++ env) b = some (.integer bv) ∧
    CoreEval.lookup ([(a, .integer av), (b, .integer bv), (c, .integer cv), (d, .integer dv)].reverse ++ env) c = some (.integer cv) ∧
    CoreEval.lookup ([(a, .integer av), (b, .integer bv), (c, .integer cv), (d, .integer dv)].reverse ++ env) d = some (.integer dv) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true, or_false, not_or] at unique
  simp_all [CoreEval.lookup, ne_comm]


/-- Checked Work/Work comparator evaluation uses the real four captured integers. -/
theorem work_work_comparator_match (c : Constructors) (program : Program)
    (node pair left right rootBody workBody defaultBody : NodeId)
    (allocatorCompare allocatorLeft allocatorRight serialCompare serialLeft serialRight falseBody : NodeId)
    (leftAllocatorName leftSerialName rightAllocatorName rightSerialName : Binder)
    (env : Environment) (start finish : Store) (result leftValue rightValue : Value)
    (leftAllocator rightAllocator : Nat) (leftSerial rightSerial : Int)
    (checked : CheckedTuple program pair none [left, right]) (leftName rightName : Binder)
    (uniqueNames : [leftAllocatorName, leftSerialName, rightAllocatorName, rightSerialName].Nodup)
    (shape : program node = some (.caseMatch pair [
      (.tuple [.constructor c.root none, .constructor c.root none], rootBody),
      (.tuple [
        .constructor c.work (some (.tuple [.binder leftAllocatorName, .binder leftSerialName])),
        .constructor c.work (some (.tuple [.binder rightAllocatorName, .binder rightSerialName]))], workBody),
      (.wildcard, defaultBody)]))
    (workShape : program workBody = some (.caseMatch allocatorCompare
      [(.boolean true, serialCompare), (.boolean false, falseBody)]))
    (allocatorShape : program allocatorCompare = some (.integerEqual allocatorLeft allocatorRight))
    (allocatorLeftShape : program allocatorLeft = some (.variable leftAllocatorName))
    (allocatorRightShape : program allocatorRight = some (.variable rightAllocatorName))
    (serialShape : program serialCompare = some (.integerEqual serialLeft serialRight))
    (serialLeftShape : program serialLeft = some (.variable leftSerialName))
    (serialRightShape : program serialRight = some (.variable rightSerialName))
    (falseShape : program falseBody = some (.boolean false))
    (leftShape : program left = some (.variable leftName))
    (rightShape : program right = some (.variable rightName))
    (leftFresh : leftName ≠ checked.contextBinder) (rightFresh : rightName ≠ checked.contextBinder)
    (leftBinding : CoreEval.lookup env leftName = some leftValue)
    (rightBinding : CoreEval.lookup env rightName = some rightValue)
    (bounded : BoundedLocations start)
    (leftWork : Ident c start leftValue (.work leftAllocator leftSerial))
    (rightWork : Ident c start rightValue (.work rightAllocator rightSerial))
    (evaluation : Eval program env node start result finish) :
    result = .boolean (Ash.NetworkLedger.CoreRemoval.compareId
      (.work leftAllocator leftSerial) (.work rightAllocator rightSerial)) := by
  obtain ⟨middle, value, chosen, bindings, pairEval, selected, bodyEval⟩ := case_match_inversion shape evaluation
  obtain ⟨location, pairValue, pairResolution, pairCell, leftAfter, rightAfter, _⟩ :=
    checked_id_pair_tuple c program pair left right env start middle value leftValue rightValue
      (.work leftAllocator leftSerial) (.work rightAllocator rightSerial) checked leftName rightName
      leftShape rightShape leftFresh rightFresh leftBinding rightBinding bounded leftWork rightWork pairEval
  subst value
  cases leftAfter with
  | work leftAddress leftResolved leftPayload leftTuple allocator serial leftResolution leftCell leftPayloadResolution leftFields =>
    cases rightAfter with
    | work rightAddress rightResolved rightPayload rightTuple allocator serial rightResolution rightCell rightPayloadResolution rightFields =>
      obtain ⟨sameBody, sameBindings⟩ := work_pair_selects_second middle c.root c.work
        location location leftAddress leftResolved leftPayload leftTuple rightAddress rightResolved rightPayload rightTuple
        leftAllocator rightAllocator leftSerial rightSerial leftAllocatorName leftSerialName rightAllocatorName rightSerialName
        rootBody workBody defaultBody pairResolution pairCell leftResolution leftCell leftPayloadResolution leftFields
        rightResolution rightCell rightPayloadResolution rightFields selected
      subst chosen
      subst bindings
      have nameValues := work_bindings_lookup env leftAllocatorName leftSerialName rightAllocatorName rightSerialName
        (Int.ofNat leftAllocator) leftSerial (Int.ofNat rightAllocator) rightSerial uniqueNames
      exact (work_comparison_body program middle finish _ workBody allocatorCompare allocatorLeft allocatorRight
        serialCompare serialLeft serialRight falseBody leftAllocatorName rightAllocatorName leftSerialName rightSerialName
        leftAllocator rightAllocator leftSerial rightSerial result workShape allocatorShape allocatorLeftShape allocatorRightShape
        serialShape serialLeftShape serialRightShape falseShape nameValues.1 nameValues.2.2.1 nameValues.2.1 nameValues.2.2.2 bodyEval).1


/-- Reopening the checked capture-free helper uses its exact code and parameter. -/
theorem capture_free_target (program : Program) (store : Store)
    (address resolved code context storage parameter body : Nat)
    (resolution : Resolve store address resolved)
    (fields : readCell store resolved = some [.closureCode code])
    (shape : program code = some (.closure context [] storage parameter body))
    {actualParameter : Binder} {actualBody : NodeId} {captured : Environment}
    (target : CallTarget program store (.location address) actualParameter actualBody captured) :
    actualParameter = parameter ∧ actualBody = body ∧ captured = [] := by
  cases target with
  | stored actualAddress other actualCode actualContext actualStorage captures
      actualParameter actualBody values bindings callableAddress otherResolution otherFields actualShape captureBindings =>
    simp at callableAddress
    subst actualAddress
    have equalFields := resolved_fields_unique resolution otherResolution fields otherFields
    simp only [List.cons.injEq, Value.closureCode.injEq] at equalFields
    rcases equalFields with ⟨sameCode, sameValues⟩
    subst actualCode
    subst values
    have sameShape := Option.some.inj (shape.symm.trans actualShape)
    simp only [Node.closure.injEq] at sameShape
    rcases sameShape with ⟨_, sameCaptures, _, sameParameter, sameBody⟩
    subst captures
    cases captureBindings
    simp_all


/-- The graph coordinates checked for the ordinary identity comparator match. -/
structure ComparatorMatch (c : Constructors) (program : Program) where
  node : NodeId
  pair : NodeId
  left : NodeId
  right : NodeId
  rootBody : NodeId
  workBody : NodeId
  defaultBody : NodeId
  allocatorCompare : NodeId
  allocatorLeft : NodeId
  allocatorRight : NodeId
  serialCompare : NodeId
  serialLeft : NodeId
  serialRight : NodeId
  falseBody : NodeId
  leftName : Binder
  rightName : Binder
  leftAllocatorName : Binder
  leftSerialName : Binder
  rightAllocatorName : Binder
  rightSerialName : Binder
  tuple : CheckedTuple program pair none [left, right]
  distinct : [leftAllocatorName, leftSerialName, rightAllocatorName, rightSerialName].Nodup
  matchShape : program node = some (.caseMatch pair [
    (.tuple [.constructor c.root none, .constructor c.root none], rootBody),
    (.tuple [
      .constructor c.work (some (.tuple [.binder leftAllocatorName, .binder leftSerialName])),
      .constructor c.work (some (.tuple [.binder rightAllocatorName, .binder rightSerialName]))], workBody),
    (.wildcard, defaultBody)])
  rootShape : program rootBody = some (.boolean true)
  defaultShape : program defaultBody = some (.boolean false)
  workShape : program workBody = some (.caseMatch allocatorCompare
    [(.boolean true, serialCompare), (.boolean false, falseBody)])
  allocatorShape : program allocatorCompare = some (.integerEqual allocatorLeft allocatorRight)
  allocatorLeftShape : program allocatorLeft = some (.variable leftAllocatorName)
  allocatorRightShape : program allocatorRight = some (.variable rightAllocatorName)
  serialShape : program serialCompare = some (.integerEqual serialLeft serialRight)
  serialLeftShape : program serialLeft = some (.variable leftSerialName)
  serialRightShape : program serialRight = some (.variable rightSerialName)
  falseShape : program falseBody = some (.boolean false)
  leftShape : program left = some (.variable leftName)
  rightShape : program right = some (.variable rightName)
  leftFresh : leftName ≠ tuple.contextBinder
  rightFresh : rightName ≠ tuple.contextBinder

/-- Every normal evaluation of the checked comparator match returns correct ID equality. -/
theorem comparator_match_correct (c : Constructors) (program : Program) (checked : ComparatorMatch c program)
    (env : Environment) (start finish : Store) (result leftValue rightValue : Value) (leftId rightId : Id)
    (leftBinding : CoreEval.lookup env checked.leftName = some leftValue)
    (rightBinding : CoreEval.lookup env checked.rightName = some rightValue)
    (bounded : BoundedLocations start) (leftRep : Ident c start leftValue leftId)
    (rightRep : Ident c start rightValue rightId)
    (evaluation : Eval program env checked.node start result finish) :
    result = .boolean (Ash.NetworkLedger.CoreRemoval.compareId leftId rightId) := by
  cases leftId with
  | root =>
    cases rightId with
    | root =>
      simpa [Ash.NetworkLedger.CoreRemoval.compareId] using
        root_root_comparator_match c program checked.node checked.pair checked.left checked.right checked.rootBody
          checked.workBody checked.defaultBody _ env start finish result leftValue rightValue checked.tuple
          checked.leftName checked.rightName checked.matchShape checked.rootShape checked.leftShape checked.rightShape
          checked.leftFresh checked.rightFresh leftBinding rightBinding bounded leftRep rightRep evaluation
    | work rightAllocator rightSerial =>
      simpa [Ash.NetworkLedger.CoreRemoval.compareId] using
        root_work_comparator_match c program checked.node checked.pair checked.left checked.right checked.rootBody
          checked.workBody checked.defaultBody _ _ env start finish result leftValue rightValue rightAllocator rightSerial
          checked.tuple checked.leftName checked.rightName checked.matchShape checked.defaultShape checked.leftShape
          checked.rightShape checked.leftFresh checked.rightFresh leftBinding rightBinding bounded leftRep rightRep evaluation
  | work leftAllocator leftSerial =>
    cases rightId with
    | root =>
      simpa [Ash.NetworkLedger.CoreRemoval.compareId] using
        work_root_comparator_match c program checked.node checked.pair checked.left checked.right checked.rootBody
          checked.workBody checked.defaultBody _ _ env start finish result leftValue rightValue leftAllocator leftSerial
          checked.tuple checked.leftName checked.rightName checked.matchShape checked.defaultShape checked.leftShape
          checked.rightShape checked.leftFresh checked.rightFresh leftBinding rightBinding bounded leftRep rightRep evaluation
    | work rightAllocator rightSerial =>
      exact work_work_comparator_match c program checked.node checked.pair checked.left checked.right checked.rootBody
        checked.workBody checked.defaultBody checked.allocatorCompare checked.allocatorLeft checked.allocatorRight
        checked.serialCompare checked.serialLeft checked.serialRight checked.falseBody checked.leftAllocatorName
        checked.leftSerialName checked.rightAllocatorName checked.rightSerialName env start finish result leftValue rightValue
        leftAllocator rightAllocator leftSerial rightSerial checked.tuple checked.leftName checked.rightName checked.distinct
        checked.matchShape checked.workShape checked.allocatorShape checked.allocatorLeftShape checked.allocatorRightShape
        checked.serialShape checked.serialLeftShape checked.serialRightShape checked.falseShape checked.leftShape
        checked.rightShape checked.leftFresh checked.rightFresh leftBinding rightBinding bounded leftRep rightRep evaluation


/-- Every supported source identity is represented by a location. -/
theorem ident_is_location (c : Constructors) (store : Store) (value : Value) (id : Id)
    (representation : Ident c store value id) : ∃ address, value = .location address := by
  cases representation <;> exact ⟨_, rfl⟩

/-- A single tuple-pattern arm binds the actual two argument values. -/
theorem pair_selects_single (store : Store) (pair resolved : Nat) (left right : Value)
    (leftName rightName : Binder) (body : NodeId)
    (resolution : Resolve store pair resolved)
    (cell : readCell store resolved = some [left, right])
    (plain : tupleFields [left, right] = some [left, right])
    {chosen : NodeId} {bindings : Environment}
    (selected : Selected store (.location pair)
      [(.tuple [.binder leftName, .binder rightName], body)] chosen bindings) :
    chosen = body ∧ bindings = [(leftName, left), (rightName, right)] := by
  cases selected with
  | first _ _ _ actual hit =>
    have same := pair_binders_match store pair resolved leftName rightName left right
      resolution cell plain hit
    cases same
    exact ⟨rfl, rfl⟩
  | later _ _ _ _ _ _ next => cases next


/-- The ordinary comparator's argument destructure feeds the checked match. -/
theorem comparator_function_body (c : Constructors) (program : Program) (checked : ComparatorMatch c program)
    (body argScrutinee : NodeId) (parameter : Binder) (pair pairResolved : Nat)
    (leftValue rightValue result : Value) (leftId rightId : Id) (start finish : Store)
    (distinct : checked.leftName ≠ checked.rightName)
    (bodyShape : program body = some (.caseMatch argScrutinee
      [(.tuple [.binder checked.leftName, .binder checked.rightName], checked.node)]))
    (argShape : program argScrutinee = some (.variable parameter))
    (pairResolution : Resolve start pair pairResolved)
    (pairCell : readCell start pairResolved = some [leftValue, rightValue])
    (bounded : BoundedLocations start)
    (leftRep : Ident c start leftValue leftId) (rightRep : Ident c start rightValue rightId)
    (evaluation : Eval program (extend [] parameter (.location pair)) body start result finish) :
    result = .boolean (Ash.NetworkLedger.CoreRemoval.compareId leftId rightId) := by
  obtain ⟨middle, value, chosen, bindings, argEval, selected, bodyEval⟩ :=
    case_match_inversion bodyShape evaluation
  obtain ⟨actualBinding, sameStore⟩ := variable_inversion argShape argEval
  have sameValue : value = .location pair := by
    simpa [CoreEval.lookup, extend] using actualBinding.symm
  subst value
  subst middle
  obtain ⟨leftAddress, leftEq⟩ := ident_is_location c start leftValue leftId leftRep
  have plain : tupleFields [leftValue, rightValue] = some [leftValue, rightValue] := by
    rw [leftEq]
    rfl
  obtain ⟨sameBody, sameBindings⟩ := pair_selects_single start pair pairResolved leftValue rightValue
    checked.leftName checked.rightName checked.node pairResolution pairCell plain selected
  subst chosen
  subst bindings
  have innerLeft : CoreEval.lookup
      ([(checked.leftName, leftValue), (checked.rightName, rightValue)].reverse ++ extend [] parameter (.location pair))
      checked.leftName = some leftValue := by
    simp [CoreEval.lookup, Ne.symm distinct]
  have innerRight : CoreEval.lookup
      ([(checked.leftName, leftValue), (checked.rightName, rightValue)].reverse ++ extend [] parameter (.location pair))
      checked.rightName = some rightValue := by simp [CoreEval.lookup]
  exact comparator_match_correct c program checked _ start finish result leftValue rightValue leftId rightId
    innerLeft innerRight bounded leftRep rightRep bodyEval


/-- Exact normalized Core graph for the checked capture-free key projection. -/
structure ProjectionCallShape (program : Program) (call : NodeId) where
  function : NodeId
  argument : NodeId
  code : NodeId
  context : NodeId
  storage : NodeId
  parameter : Binder
  body : NodeId
  scrutinee : NodeId
  returnKey : NodeId
  functionName : Binder
  entryName : Binder
  keyName : Binder
  destinationName : Binder
  child : Constructor
  distinct : keyName ≠ destinationName
  callShape : program call = some (.apply function argument)
  functionShape : program function = some (.variable functionName)
  argumentShape : program argument = some (.variable entryName)
  closureShape : program code = some (.closure context [] storage parameter body)
  bodyShape : program body = some (.caseMatch scrutinee
    [(.constructor child (some (.tuple [.binder keyName, .binder destinationName])), returnKey)])
  scrutineeShape : program scrutinee = some (.variable parameter)
  returnShape : program returnKey = some (.variable keyName)

/-- The actual capture-free projection call returns the original child key. -/
theorem child_projection_call (program : Program) (store finish : Store) (env : Environment)
    (call function argument code context storage parameter body scrutinee returnKey : NodeId)
    (functionName entryName keyName destinationName : Binder) (child : Constructor)
    (functionAddress functionResolved entryAddress entryResolved payload tuple keyAddress : Nat)
    (destination result : Value)
    (shape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable functionName))
    (argumentShape : program argument = some (.variable entryName))
    (functionBinding : CoreEval.lookup env functionName = some (.location functionAddress))
    (entryBinding : CoreEval.lookup env entryName = some (.location entryAddress))
    (functionResolution : Resolve store functionAddress functionResolved)
    (functionCell : readCell store functionResolved = some [.closureCode code])
    (closureShape : program code = some (.closure context [] storage parameter body))
    (distinct : keyName ≠ destinationName)
    (bodyShape : program body = some (.caseMatch scrutinee
      [(.constructor child (some (.tuple [.binder keyName, .binder destinationName])), returnKey)]))
    (scrutineeShape : program scrutinee = some (.variable parameter))
    (returnShape : program returnKey = some (.variable keyName))
    (entryResolution : Resolve store entryAddress entryResolved)
    (entryCell : readCell store entryResolved = some [.tag child, .location payload])
    (payloadResolution : Resolve store payload tuple)
    (fields : readCell store tuple = some [.location keyAddress, destination])
    (evaluation : Eval program env call store result finish) :
    result = .location keyAddress ∧ finish = store := by
  obtain ⟨afterFunction, afterArgument, callable, argumentValue, actualParameter, actualBody, captured,
    functionEval, target, argumentEval, bodyEval⟩ := apply_inversion shape evaluation
  obtain ⟨actualFunction, functionState⟩ := variable_inversion functionShape functionEval
  have sameFunction : callable = .location functionAddress := by simpa [functionBinding] using actualFunction.symm
  subst callable
  subst afterFunction
  obtain ⟨sameParameter, sameBody, sameCapture⟩ :=
    capture_free_target program store functionAddress functionResolved code context storage parameter body
      functionResolution functionCell closureShape target
  subst actualParameter
  subst actualBody
  subst captured
  obtain ⟨actualArgument, argumentState⟩ := variable_inversion argumentShape argumentEval
  have sameArgument : argumentValue = .location entryAddress := by simpa [entryBinding] using actualArgument.symm
  subst argumentValue
  subst afterArgument
  exact child_projection_returns_key program store finish (extend [] parameter (.location entryAddress))
    body scrutinee returnKey parameter keyName destinationName child entryAddress entryResolved payload tuple keyAddress
    destination result distinct bodyShape scrutineeShape returnShape (by simp [CoreEval.lookup, extend])
    entryResolution entryCell payloadResolution fields bodyEval


/-- A concrete projection call returns its represented key after the checked query. -/
def ProjectionAfterQuery (program : Program) (projection : NodeId) (env : Environment)
    (contextBinder : Binder) (start : Store) (keyAddress : Nat) : Prop :=
  ∀ queried middle actual,
    query .hostDefault start = some (.hostDefault, queried) →
    Eval program (extend env contextBinder .context) projection queried actual middle →
    actual = .location keyAddress ∧ middle = queried

/-- Strict projection and wanted evaluation build the pair from the actual key. -/
theorem projection_first_argument_with (program : Program) (root projection wantedNode : NodeId)
    (env : Environment) (start finish : Store) (result wanted : Value)
    (checked : CheckedTuple program root none [projection, wantedNode]) (wantedName : Binder)
    (keyAddress : Nat) (wantedFresh : wantedName ≠ checked.contextBinder)
    (wantedShape : program wantedNode = some (.variable wantedName))
    (wantedBinding : CoreEval.lookup env wantedName = some wanted)
    (projectionLaw : ProjectionAfterQuery program projection env checked.contextBinder start keyAddress)
    (bounded : BoundedLocations start)
    (evaluation : Eval program env root start result finish) :
    ∃ location, location = start.nextLocation ∧ result = .location location ∧
      readCell finish location = some [.location keyAddress, wanted] ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ address values, readCell start address = some values → readCell finish address = some values) := by
  obtain ⟨queried, afterFields, afterAlloc, location, values, queryStep, fieldEvals,
    allocated, initialized, resultEq⟩ := checked_tuple_inversion checked evaluation
  obtain ⟨middle, actualKey, actualWanted, projectionEval, wantedEval, sameValues⟩ :=
    pair_fields_inversion fieldEvals
  have wantedBound : CoreEval.lookup (extend env checked.contextBinder .context) wantedName = some wanted := by
    rw [lookup_extended_other env checked.contextBinder wantedName wantedFresh]
    exact wantedBinding
  obtain ⟨sameKey, sameMiddle⟩ := projectionLaw queried middle actualKey queryStep projectionEval
  subst actualKey
  subst middle
  obtain ⟨actualWantedBinding, wantedStore⟩ := variable_inversion wantedShape wantedEval
  have sameWanted : actualWanted = wanted := by simpa [wantedBound] using actualWantedBinding.symm
  subst actualWanted
  subst afterFields
  subst values
  have allocationStep : allocate .hostDefault 2 true queried = some (location, afterAlloc) := by
    simpa using allocated
  have initializeStep : initializeStorage location 2 [.location keyAddress, wanted] afterAlloc =
      some ([.location keyAddress, wanted], finish) := by simpa [storedFields] using initialized
  obtain ⟨fresh, pairCell, aliasesSame, finishBound, retained⟩ :=
    host_pair_retains bounded queryStep allocationStep initializeStep
  exact ⟨location, fresh, resultEq, pairCell, aliasesSame, finishBound, retained⟩

/-- The actual projection-first comparator argument stores the original key and query. -/
theorem projection_first_argument (program : Program) (root projection wantedNode : NodeId)
    (shape : ProjectionCallShape program projection)
    (env : Environment) (start finish : Store) (result wanted : Value)
    (checked : CheckedTuple program root none [projection, wantedNode]) (wantedName : Binder)
    (functionAddress functionResolved entryAddress entryResolved payload tuple keyAddress : Nat) (destination : Value)
    (functionFresh : shape.functionName ≠ checked.contextBinder)
    (entryFresh : shape.entryName ≠ checked.contextBinder)
    (wantedFresh : wantedName ≠ checked.contextBinder)
    (wantedShape : program wantedNode = some (.variable wantedName))
    (functionBinding : CoreEval.lookup env shape.functionName = some (.location functionAddress))
    (entryBinding : CoreEval.lookup env shape.entryName = some (.location entryAddress))
    (wantedBinding : CoreEval.lookup env wantedName = some wanted)
    (functionResolution : Resolve start functionAddress functionResolved)
    (functionCell : readCell start functionResolved = some [.closureCode shape.code])
    (entryResolution : Resolve start entryAddress entryResolved)
    (entryCell : readCell start entryResolved = some [.tag shape.child, .location payload])
    (payloadResolution : Resolve start payload tuple)
    (fields : readCell start tuple = some [.location keyAddress, destination])
    (bounded : BoundedLocations start)
    (evaluation : Eval program env root start result finish) :
    ∃ location, location = start.nextLocation ∧ result = .location location ∧
      readCell finish location = some [.location keyAddress, wanted] ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ address values, readCell start address = some values → readCell finish address = some values) := by
  apply projection_first_argument_with program root projection wantedNode env start finish result wanted
    checked wantedName keyAddress wantedFresh wantedShape wantedBinding ?_ bounded evaluation
  intro queried middle actualKey queryStep projectionEval
  have functionBound : CoreEval.lookup (extend env checked.contextBinder .context) shape.functionName =
      some (.location functionAddress) := by
    rw [lookup_extended_other env checked.contextBinder shape.functionName functionFresh]
    exact functionBinding
  have entryBound : CoreEval.lookup (extend env checked.contextBinder .context) shape.entryName =
      some (.location entryAddress) := by
    rw [lookup_extended_other env checked.contextBinder shape.entryName entryFresh]
    exact entryBinding
  exact child_projection_call program queried middle (extend env checked.contextBinder .context)
    projection shape.function shape.argument shape.code shape.context shape.storage shape.parameter shape.body
    shape.scrutinee shape.returnKey shape.functionName shape.entryName shape.keyName shape.destinationName shape.child
    functionAddress functionResolved entryAddress entryResolved payload tuple keyAddress destination actualKey
    shape.callShape shape.functionShape shape.argumentShape functionBound entryBound
    (query_preserves_resolution queryStep functionResolution) (query_preserves_cell queryStep functionCell)
    shape.closureShape shape.distinct shape.bodyShape shape.scrutineeShape shape.returnShape
    (query_preserves_resolution queryStep entryResolution) (query_preserves_cell queryStep entryCell)
    (query_preserves_resolution queryStep payloadResolution) (query_preserves_cell queryStep fields) projectionEval


/-- Exact normalized graph of a capture-free ordinary comparator function. -/
structure ComparatorFunction (c : Constructors) (program : Program) where
  inner : ComparatorMatch c program
  code : NodeId
  context : NodeId
  storage : NodeId
  parameter : Binder
  body : NodeId
  argScrutinee : NodeId
  argDistinct : inner.leftName ≠ inner.rightName
  closureShape : program code = some (.closure context [] storage parameter body)
  bodyShape : program body = some (.caseMatch argScrutinee
    [(.tuple [.binder inner.leftName, .binder inner.rightName], inner.node)])
  argShape : program argScrutinee = some (.variable parameter)

/-- The linked Remove comparator call uses its projection and current query ID. -/
theorem projection_comparator_call (c : Constructors) (program : Program)
    (call function argument projection wantedNode : NodeId)
    (comparator : ComparatorFunction c program) (projectionShape : ProjectionCallShape program projection)
    (callerEnv : Environment) (start finish : Store) (result wanted : Value)
    (wantedId keyId : Id) (functionName wantedName : Binder)
    (checkedArgument : CheckedTuple program argument none [projection, wantedNode])
    (comparatorAddress comparatorResolved projectionAddress projectionResolved : Nat)
    (entryAddress entryResolved payload tuple keyAddress : Nat) (destination : Value)
    (callShape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable functionName))
    (functionBinding : CoreEval.lookup callerEnv functionName = some (.location comparatorAddress))
    (comparatorResolution : Resolve start comparatorAddress comparatorResolved)
    (comparatorCell : readCell start comparatorResolved = some [.closureCode comparator.code])
    (projectionFresh : projectionShape.functionName ≠ checkedArgument.contextBinder)
    (entryFresh : projectionShape.entryName ≠ checkedArgument.contextBinder)
    (wantedFresh : wantedName ≠ checkedArgument.contextBinder)
    (wantedShape : program wantedNode = some (.variable wantedName))
    (projectionBinding : CoreEval.lookup callerEnv projectionShape.functionName = some (.location projectionAddress))
    (entryBinding : CoreEval.lookup callerEnv projectionShape.entryName = some (.location entryAddress))
    (wantedBinding : CoreEval.lookup callerEnv wantedName = some wanted)
    (projectionResolution : Resolve start projectionAddress projectionResolved)
    (projectionCell : readCell start projectionResolved = some [.closureCode projectionShape.code])
    (entryResolution : Resolve start entryAddress entryResolved)
    (entryCell : readCell start entryResolved = some [.tag projectionShape.child, .location payload])
    (payloadResolution : Resolve start payload tuple)
    (entryFields : readCell start tuple = some [.location keyAddress, destination])
    (bounded : BoundedLocations start)
    (keyRepresentation : Ident c start (.location keyAddress) keyId)
    (wantedRepresentation : Ident c start wanted wantedId)
    (evaluation : Eval program callerEnv call start result finish) :
    result = .boolean (Ash.NetworkLedger.CoreRemoval.compareId keyId wantedId) := by
  obtain ⟨afterFunction, afterArgument, callable, argumentValue, parameter, body, captured,
    functionEval, target, argumentEval, bodyEval⟩ := apply_inversion callShape evaluation
  obtain ⟨actualFunction, functionState⟩ := variable_inversion functionShape functionEval
  have sameFunction : callable = .location comparatorAddress := by simpa [functionBinding] using actualFunction.symm
  subst callable
  subst afterFunction
  obtain ⟨sameParameter, sameBody, sameCapture⟩ := capture_free_target program start comparatorAddress comparatorResolved
    comparator.code comparator.context comparator.storage comparator.parameter comparator.body
    comparatorResolution comparatorCell comparator.closureShape target
  subst parameter
  subst body
  subst captured
  obtain ⟨location, fresh, sameArgument, pairCell, aliasesSame, afterBound, retained⟩ :=
    projection_first_argument program argument projection wantedNode projectionShape callerEnv start afterArgument
      argumentValue wanted checkedArgument wantedName projectionAddress projectionResolved entryAddress entryResolved
      payload tuple keyAddress destination projectionFresh entryFresh wantedFresh wantedShape projectionBinding
      entryBinding wantedBinding projectionResolution projectionCell entryResolution entryCell payloadResolution entryFields
      bounded argumentEval
  subst argumentValue
  have noAlias : readAlias afterArgument location = none := by
    rw [fresh]
    simpa [readAlias, aliasesSame] using bounded_fresh_no_alias start bounded
  have pairResolution : Resolve afterArgument location location :=
    Resolve.cell location [.location keyAddress, wanted] noAlias pairCell
  have keyAfter := ident_retained c start afterArgument (.location keyAddress) keyId aliasesSame retained keyRepresentation
  have wantedAfter := ident_retained c start afterArgument wanted wantedId aliasesSame retained wantedRepresentation
  exact comparator_function_body c program comparator.inner comparator.body comparator.argScrutinee comparator.parameter
    location location (.location keyAddress) wanted result keyId wantedId afterArgument finish comparator.argDistinct
    comparator.bodyShape comparator.argShape pairResolution pairCell afterBound keyAfter wantedAfter bodyEval


/-- Integer equality of checked variables has no heap effects. -/
theorem integer_variables_preserve (program : Program) (env : Environment)
    (node left right : NodeId) (leftName rightName : Binder)
    (start finish : Store) (result : Value)
    (shape : program node = some (.integerEqual left right))
    (leftShape : program left = some (.variable leftName))
    (rightShape : program right = some (.variable rightName))
    (evaluation : Eval program env node start result finish) : finish = start := by
  obtain ⟨middle, first, second, leftEval, rightEval, _⟩ := integer_equal_inversion shape evaluation
  obtain ⟨_, leftStore⟩ := variable_inversion leftShape leftEval
  obtain ⟨_, rightStore⟩ := variable_inversion rightShape rightEval
  exact rightStore.trans leftStore

/-- Every branch of the checked Work comparison retains its input store. -/
theorem comparator_work_preserves (c : Constructors) (program : Program)
    (checked : ComparatorMatch c program) (env : Environment) (start finish : Store)
    (result : Value) (evaluation : Eval program env checked.workBody start result finish) : finish = start := by
  obtain ⟨middle, value, chosen, bindings, allocatorEval, selected, bodyEval⟩ :=
    case_match_inversion checked.workShape evaluation
  have sameMiddle := integer_variables_preserve program env checked.allocatorCompare checked.allocatorLeft
    checked.allocatorRight checked.leftAllocatorName checked.rightAllocatorName start middle value
    checked.allocatorShape checked.allocatorLeftShape checked.allocatorRightShape allocatorEval
  subst middle
  cases selected with
  | first _ _ _ _ _ =>
    exact integer_variables_preserve program _ checked.serialCompare checked.serialLeft checked.serialRight
      checked.leftSerialName checked.rightSerialName start finish result checked.serialShape checked.serialLeftShape
      checked.serialRightShape bodyEval
  | later _ _ _ _ _ _ next =>
    cases next with
    | first _ _ _ _ _ => exact (boolean_inversion checked.falseShape bodyEval).2
    | later _ _ _ _ _ _ impossible => cases impossible

/-- A variable pair allocates exactly one new host location. -/
theorem checked_variable_pair_advances {program : Program} {root left right : NodeId}
    {env : Environment} {start finish : Store} {result leftValue rightValue : Value}
    (checked : CheckedTuple program root none [left, right])
    (leftName rightName : Binder)
    (leftShape : program left = some (.variable leftName))
    (rightShape : program right = some (.variable rightName))
    (leftFresh : leftName ≠ checked.contextBinder)
    (rightFresh : rightName ≠ checked.contextBinder)
    (leftBinding : CoreEval.lookup env leftName = some leftValue)
    (rightBinding : CoreEval.lookup env rightName = some rightValue)
    (evaluation : Eval program env root start result finish) : finish.nextLocation = start.nextLocation + 1 := by
  obtain ⟨queried, afterAlloc, location, queryStep, allocated, initialized, _⟩ :=
    checked_variable_pair_tuple checked leftName rightName leftShape rightShape leftFresh rightFresh
      leftBinding rightBinding evaluation
  simp only [query, Option.some.injEq, Prod.mk.injEq] at queryStep
  rcases queryStep with ⟨_, rfl⟩
  simp only [allocate, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Option.some.injEq, Prod.mk.injEq] at allocated
  rcases allocated with ⟨rfl, rfl⟩
  simp only [initializeStorage] at initialized
  split at initialized
  · simp only [Option.some.injEq, Prod.mk.injEq] at initialized
    rcases initialized with ⟨_, rfl⟩
    rfl
  · simp_all

/-- The checked comparator's allocated pair is its only change to live storage. -/
theorem comparator_match_preserves (c : Constructors) (program : Program)
    (checked : ComparatorMatch c program) (env : Environment) (start finish : Store)
    (result leftValue rightValue : Value)
    (leftBinding : CoreEval.lookup env checked.leftName = some leftValue)
    (rightBinding : CoreEval.lookup env checked.rightName = some rightValue)
    (bounded : BoundedLocations start)
    (evaluation : Eval program env checked.node start result finish) :
    finish.nextLocation = start.nextLocation + 1 ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ address values, readCell start address = some values → readCell finish address = some values) := by
  obtain ⟨middle, value, chosen, bindings, pairEval, selected, bodyEval⟩ :=
    case_match_inversion checked.matchShape evaluation
  obtain ⟨_, _, _, _, aliasesSame, afterBound, retained⟩ :=
    checked_variable_pair_retains checked.tuple checked.leftName checked.rightName checked.leftShape
      checked.rightShape checked.leftFresh checked.rightFresh leftBinding rightBinding bounded pairEval
  have sameFinish : finish = middle := by
    cases selected with
    | first _ _ _ _ _ => exact (boolean_inversion checked.rootShape bodyEval).2
    | later _ _ _ _ _ _ next =>
      cases next with
      | first _ _ _ _ _ => exact comparator_work_preserves c program checked _ middle finish result bodyEval
      | later _ _ _ _ _ _ last =>
        cases last with
        | first _ _ _ _ _ => exact (boolean_inversion checked.defaultShape bodyEval).2
        | later _ _ _ _ _ _ impossible => cases impossible
  subst finish
  have advances := checked_variable_pair_advances checked.tuple checked.leftName checked.rightName checked.leftShape
    checked.rightShape checked.leftFresh checked.rightFresh leftBinding rightBinding pairEval
  exact ⟨advances, aliasesSame, afterBound, retained⟩

/-- Opening and destructuring the actual comparator argument preserves the pair's caller state. -/
theorem comparator_function_preserves (c : Constructors) (program : Program) (checked : ComparatorFunction c program)
    (pair pairResolved : Nat) (leftValue rightValue result : Value) (leftId : Id) (start finish : Store)
    (pairResolution : Resolve start pair pairResolved)
    (pairCell : readCell start pairResolved = some [leftValue, rightValue])
    (bounded : BoundedLocations start) (leftRep : Ident c start leftValue leftId)
    (evaluation : Eval program (extend [] checked.parameter (.location pair)) checked.body start result finish) :
    finish.nextLocation = start.nextLocation + 1 ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ address values, readCell start address = some values → readCell finish address = some values) := by
  obtain ⟨middle, value, chosen, bindings, argEval, selected, bodyEval⟩ :=
    case_match_inversion checked.bodyShape evaluation
  obtain ⟨actualBinding, sameStore⟩ := variable_inversion checked.argShape argEval
  have sameValue : value = .location pair := by
    simpa [CoreEval.lookup, extend] using actualBinding.symm
  subst value
  subst middle
  obtain ⟨leftAddress, leftEq⟩ := ident_is_location c start leftValue leftId leftRep
  have plain : tupleFields [leftValue, rightValue] = some [leftValue, rightValue] := by
    rw [leftEq]
    rfl
  obtain ⟨sameBody, sameBindings⟩ := pair_selects_single start pair pairResolved leftValue rightValue
    checked.inner.leftName checked.inner.rightName checked.inner.node pairResolution pairCell plain selected
  subst chosen
  subst bindings
  have innerLeft : CoreEval.lookup
      ([(checked.inner.leftName, leftValue), (checked.inner.rightName, rightValue)].reverse ++ extend [] checked.parameter (.location pair))
      checked.inner.leftName = some leftValue := by
    simp [CoreEval.lookup, Ne.symm checked.argDistinct]
  have innerRight : CoreEval.lookup
      ([(checked.inner.leftName, leftValue), (checked.inner.rightName, rightValue)].reverse ++ extend [] checked.parameter (.location pair))
      checked.inner.rightName = some rightValue := by simp [CoreEval.lookup]
  exact comparator_match_preserves c program checked.inner _ start finish result leftValue rightValue
    innerLeft innerRight bounded bodyEval

/-- Preserving actual heap reads retains each complete original child entry. -/
theorem entry_retained (c : Constructors) (before after : Store) (entry key destination : Value)
    (aliasesSame : after.aliases = before.aliases)
    (cellsRetained : ∀ location values, readCell before location = some values →
      readCell after location = some values)
    (representation : Entry c before entry key destination) : Entry c after entry key destination := by
  cases representation with
  | child address resolved payload tuple key destination resolution cell payloadResolution fields =>
    exact Entry.child address resolved payload tuple key destination
      (resolve_preserved aliasesSame cellsRetained resolution) (cellsRetained resolved _ cell)
      (resolve_preserved aliasesSame cellsRetained payloadResolution) (cellsRetained tuple _ fields)

/-- The same preservation retains the finite list's exact ordered entry values. -/
theorem children_retained (c : Constructors) (before after : Store) (value : Value) (entries : List Value)
    (aliasesSame : after.aliases = before.aliases)
    (cellsRetained : ∀ location values, readCell before location = some values →
      readCell after location = some values)
    (representation : Children c before value entries) : Children c after value entries := by
  induction representation with
  | empty address resolved resolution cell =>
    exact Children.empty address resolved (resolve_preserved aliasesSame cellsRetained resolution)
      (cellsRetained resolved _ cell)
  | more address resolved payload tuple head tail entries resolution cell payloadResolution fields remaining ih =>
    exact Children.more address resolved payload tuple head tail entries
      (resolve_preserved aliasesSame cellsRetained resolution) (cellsRetained resolved _ cell)
      (resolve_preserved aliasesSame cellsRetained payloadResolution) (cellsRetained tuple _ fields) ih

/-- The full checked projection and comparator preserve the caller’s live heap. -/
theorem projection_comparator_retains (c : Constructors) (program : Program)
    (call function argument projection wantedNode : NodeId)
    (comparator : ComparatorFunction c program) (projectionShape : ProjectionCallShape program projection)
    (callerEnv : Environment) (start finish : Store) (result wanted : Value)
    (wantedId keyId : Id) (functionName wantedName : Binder)
    (checkedArgument : CheckedTuple program argument none [projection, wantedNode])
    (comparatorAddress comparatorResolved projectionAddress projectionResolved : Nat)
    (entryAddress entryResolved payload tuple keyAddress : Nat) (destination : Value)
    (callShape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable functionName))
    (functionBinding : CoreEval.lookup callerEnv functionName = some (.location comparatorAddress))
    (comparatorResolution : Resolve start comparatorAddress comparatorResolved)
    (comparatorCell : readCell start comparatorResolved = some [.closureCode comparator.code])
    (projectionFresh : projectionShape.functionName ≠ checkedArgument.contextBinder)
    (entryFresh : projectionShape.entryName ≠ checkedArgument.contextBinder)
    (wantedFresh : wantedName ≠ checkedArgument.contextBinder)
    (wantedShape : program wantedNode = some (.variable wantedName))
    (projectionBinding : CoreEval.lookup callerEnv projectionShape.functionName = some (.location projectionAddress))
    (entryBinding : CoreEval.lookup callerEnv projectionShape.entryName = some (.location entryAddress))
    (wantedBinding : CoreEval.lookup callerEnv wantedName = some wanted)
    (projectionResolution : Resolve start projectionAddress projectionResolved)
    (projectionCell : readCell start projectionResolved = some [.closureCode projectionShape.code])
    (entryResolution : Resolve start entryAddress entryResolved)
    (entryCell : readCell start entryResolved = some [.tag projectionShape.child, .location payload])
    (payloadResolution : Resolve start payload tuple)
    (entryFields : readCell start tuple = some [.location keyAddress, destination])
    (bounded : BoundedLocations start)
    (keyRepresentation : Ident c start (.location keyAddress) keyId)
    (wantedRepresentation : Ident c start wanted wantedId)
    (evaluation : Eval program callerEnv call start result finish) :
    result = .boolean (Ash.NetworkLedger.CoreRemoval.compareId keyId wantedId) ∧
      start.nextLocation < finish.nextLocation ∧ finish.aliases = start.aliases ∧
      BoundedLocations finish ∧
      (∀ address values, readCell start address = some values → readCell finish address = some values) := by
  obtain ⟨afterFunction, afterArgument, callable, argumentValue, parameter, body, captured,
    functionEval, target, argumentEval, bodyEval⟩ := apply_inversion callShape evaluation
  obtain ⟨actualFunction, functionState⟩ := variable_inversion functionShape functionEval
  have sameFunction : callable = .location comparatorAddress := by simpa [functionBinding] using actualFunction.symm
  subst callable
  subst afterFunction
  obtain ⟨sameParameter, sameBody, sameCapture⟩ := capture_free_target program start comparatorAddress comparatorResolved
    comparator.code comparator.context comparator.storage comparator.parameter comparator.body
    comparatorResolution comparatorCell comparator.closureShape target
  subst parameter
  subst body
  subst captured
  obtain ⟨location, fresh, sameArgument, pairCell, aliasesSame, afterBound, retained⟩ :=
    projection_first_argument program argument projection wantedNode projectionShape callerEnv start afterArgument
      argumentValue wanted checkedArgument wantedName projectionAddress projectionResolved entryAddress entryResolved
      payload tuple keyAddress destination projectionFresh entryFresh wantedFresh wantedShape projectionBinding
      entryBinding wantedBinding projectionResolution projectionCell entryResolution entryCell payloadResolution entryFields
      bounded argumentEval
  subst argumentValue
  have noAlias : readAlias afterArgument location = none := by
    rw [fresh]
    simpa [readAlias, aliasesSame] using bounded_fresh_no_alias start bounded
  have pairResolution : Resolve afterArgument location location :=
    Resolve.cell location [.location keyAddress, wanted] noAlias pairCell
  have keyAfter := ident_retained c start afterArgument (.location keyAddress) keyId aliasesSame retained keyRepresentation
  have wantedAfter := ident_retained c start afterArgument wanted wantedId aliasesSame retained wantedRepresentation
  have correct := comparator_function_body c program comparator.inner comparator.body comparator.argScrutinee comparator.parameter
    location location (.location keyAddress) wanted result keyId wantedId afterArgument finish comparator.argDistinct
    comparator.bodyShape comparator.argShape pairResolution pairCell afterBound keyAfter wantedAfter bodyEval
  obtain ⟨_, aliasesFinal, boundedFinal, retainedFinal⟩ :=
    comparator_function_preserves c program comparator location location (.location keyAddress) wanted result keyId
      afterArgument finish pairResolution pairCell afterBound keyAfter bodyEval
  have finalPair := retainedFinal location _ pairCell
  have freshBound := boundedFinal.2.1 location _ (readCell_member finish location _ finalPair)
  rw [fresh] at freshBound
  refine ⟨correct, freshBound, aliasesFinal.trans aliasesSame, boundedFinal, ?_⟩
  intro address values read
  exact retainedFinal address values (retained address values read)


/-- Comparator execution from an exact, store-preserving projection evaluation. -/
theorem projection_comparator_retains_with (c : Constructors) (program : Program)
    (call function argument projection wantedNode : NodeId)
    (comparator : ComparatorFunction c program)
    (callerEnv : Environment) (start finish : Store) (result wanted : Value)
    (wantedId keyId : Id) (functionName wantedName : Binder)
    (checkedArgument : CheckedTuple program argument none [projection, wantedNode])
    (comparatorAddress comparatorResolved keyAddress : Nat)
    (callShape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable functionName))
    (functionBinding : CoreEval.lookup callerEnv functionName = some (.location comparatorAddress))
    (comparatorResolution : Resolve start comparatorAddress comparatorResolved)
    (comparatorCell : readCell start comparatorResolved = some [.closureCode comparator.code])
    (wantedFresh : wantedName ≠ checkedArgument.contextBinder)
    (wantedShape : program wantedNode = some (.variable wantedName))
    (wantedBinding : CoreEval.lookup callerEnv wantedName = some wanted)
    (projectionLaw : ProjectionAfterQuery program projection callerEnv checkedArgument.contextBinder start keyAddress)
    (bounded : BoundedLocations start)
    (keyRepresentation : Ident c start (.location keyAddress) keyId)
    (wantedRepresentation : Ident c start wanted wantedId)
    (evaluation : Eval program callerEnv call start result finish) :
    result = .boolean (Ash.NetworkLedger.CoreRemoval.compareId keyId wantedId) ∧
      start.nextLocation < finish.nextLocation ∧ finish.aliases = start.aliases ∧
      BoundedLocations finish ∧
      (∀ address values, readCell start address = some values → readCell finish address = some values) := by
  obtain ⟨afterFunction, afterArgument, callable, argumentValue, parameter, body, captured,
    functionEval, target, argumentEval, bodyEval⟩ := apply_inversion callShape evaluation
  obtain ⟨actualFunction, functionState⟩ := variable_inversion functionShape functionEval
  have sameFunction : callable = .location comparatorAddress := by
    simpa [functionBinding] using actualFunction.symm
  subst callable
  subst afterFunction
  obtain ⟨sameParameter, sameBody, sameCapture⟩ := capture_free_target program start comparatorAddress comparatorResolved
    comparator.code comparator.context comparator.storage comparator.parameter comparator.body
    comparatorResolution comparatorCell comparator.closureShape target
  subst parameter
  subst body
  subst captured
  obtain ⟨location, fresh, sameArgument, pairCell, aliasesSame, afterBound, retained⟩ :=
    projection_first_argument_with program argument projection wantedNode callerEnv start afterArgument
      argumentValue wanted checkedArgument wantedName keyAddress wantedFresh wantedShape wantedBinding
      projectionLaw bounded argumentEval
  subst argumentValue
  have noAlias : readAlias afterArgument location = none := by
    rw [fresh]
    simpa [readAlias, aliasesSame] using bounded_fresh_no_alias start bounded
  have pairResolution : Resolve afterArgument location location :=
    Resolve.cell location [.location keyAddress, wanted] noAlias pairCell
  have keyAfter := ident_retained c start afterArgument (.location keyAddress) keyId aliasesSame retained keyRepresentation
  have wantedAfter := ident_retained c start afterArgument wanted wantedId aliasesSame retained wantedRepresentation
  have correct := comparator_function_body c program comparator.inner comparator.body comparator.argScrutinee comparator.parameter
    location location (.location keyAddress) wanted result keyId wantedId afterArgument finish comparator.argDistinct
    comparator.bodyShape comparator.argShape pairResolution pairCell afterBound keyAfter wantedAfter bodyEval
  obtain ⟨_, aliasesFinal, boundedFinal, retainedFinal⟩ :=
    comparator_function_preserves c program comparator location location (.location keyAddress) wanted result keyId
      afterArgument finish pairResolution pairCell afterBound keyAfter bodyEval
  have finalPair := retainedFinal location _ pairCell
  have freshBound := boundedFinal.2.1 location _ (readCell_member finish location _ finalPair)
  rw [fresh] at freshBound
  refine ⟨correct, freshBound, aliasesFinal.trans aliasesSame, boundedFinal, ?_⟩
  intro address values read
  exact retainedFinal address values (retained address values read)

/-- The actual comparator selects a branch using the represented key. -/
theorem comparison_selects_with (c : Constructors) (program : Program)
    (branch trueBody falseBody call function argument projection wantedNode : NodeId)
    (comparator : ComparatorFunction c program) (callerEnv : Environment) (start finish : Store)
    (result wanted : Value) (wantedId keyId : Id) (functionName wantedName : Binder)
    (checkedArgument : CheckedTuple program argument none [projection, wantedNode])
    (comparatorAddress comparatorResolved keyAddress : Nat)
    (callShape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable functionName))
    (functionBinding : CoreEval.lookup callerEnv functionName = some (.location comparatorAddress))
    (comparatorResolution : Resolve start comparatorAddress comparatorResolved)
    (comparatorCell : readCell start comparatorResolved = some [.closureCode comparator.code])
    (wantedFresh : wantedName ≠ checkedArgument.contextBinder)
    (wantedShape : program wantedNode = some (.variable wantedName))
    (wantedBinding : CoreEval.lookup callerEnv wantedName = some wanted)
    (projectionLaw : ProjectionAfterQuery program projection callerEnv checkedArgument.contextBinder start keyAddress)
    (bounded : BoundedLocations start)
    (keyRepresentation : Ident c start (.location keyAddress) keyId)
    (wantedRepresentation : Ident c start wanted wantedId)
    (branchShape : program branch = some (.caseMatch call
      [(.boolean true, trueBody), (.boolean false, falseBody)]))
    (evaluation : Eval program callerEnv branch start result finish) :
    ∃ middle, Eval program callerEnv
        (if Ash.NetworkLedger.CoreRemoval.compareId keyId wantedId then trueBody else falseBody)
        middle result finish ∧
      start.nextLocation < middle.nextLocation ∧ middle.aliases = start.aliases ∧
      BoundedLocations middle ∧
      (∀ address values, readCell start address = some values → readCell middle address = some values) := by
  obtain ⟨middle, value, chosen, bindings, comparisonEval, selected, bodyEval⟩ :=
    case_match_inversion branchShape evaluation
  obtain ⟨sameValue, advances, aliasesSame, middleBounded, retained⟩ :=
    projection_comparator_retains_with c program call function argument projection wantedNode comparator
      callerEnv start middle value wanted wantedId keyId functionName wantedName checkedArgument
      comparatorAddress comparatorResolved keyAddress callShape functionShape functionBinding comparatorResolution
      comparatorCell wantedFresh wantedShape wantedBinding projectionLaw bounded keyRepresentation wantedRepresentation
      comparisonEval
  subst value
  obtain ⟨sameBody, sameBindings⟩ := boolean_selects middle
    (Ash.NetworkLedger.CoreRemoval.compareId keyId wantedId) trueBody falseBody selected
  subst chosen
  subst bindings
  exact ⟨middle, by simpa using bodyEval, advances, aliasesSame, middleBounded, retained⟩

/-- The checked removal test selects the branch for the original child key. -/
theorem removal_comparison_selects (c : Constructors) (program : Program)
    (branch trueBody falseBody call function argument projection wantedNode : NodeId)
    (comparator : ComparatorFunction c program) (projectionShape : ProjectionCallShape program projection)
    (callerEnv : Environment) (start finish : Store) (result wanted : Value)
    (wantedId keyId : Id) (functionName wantedName : Binder)
    (checkedArgument : CheckedTuple program argument none [projection, wantedNode])
    (comparatorAddress comparatorResolved projectionAddress projectionResolved : Nat)
    (entryAddress entryResolved payload tuple keyAddress : Nat) (destination : Value)
    (callShape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable functionName))
    (functionBinding : CoreEval.lookup callerEnv functionName = some (.location comparatorAddress))
    (comparatorResolution : Resolve start comparatorAddress comparatorResolved)
    (comparatorCell : readCell start comparatorResolved = some [.closureCode comparator.code])
    (projectionFresh : projectionShape.functionName ≠ checkedArgument.contextBinder)
    (entryFresh : projectionShape.entryName ≠ checkedArgument.contextBinder)
    (wantedFresh : wantedName ≠ checkedArgument.contextBinder)
    (wantedShape : program wantedNode = some (.variable wantedName))
    (projectionBinding : CoreEval.lookup callerEnv projectionShape.functionName = some (.location projectionAddress))
    (entryBinding : CoreEval.lookup callerEnv projectionShape.entryName = some (.location entryAddress))
    (wantedBinding : CoreEval.lookup callerEnv wantedName = some wanted)
    (projectionResolution : Resolve start projectionAddress projectionResolved)
    (projectionCell : readCell start projectionResolved = some [.closureCode projectionShape.code])
    (entryResolution : Resolve start entryAddress entryResolved)
    (entryCell : readCell start entryResolved = some [.tag projectionShape.child, .location payload])
    (payloadResolution : Resolve start payload tuple)
    (entryFields : readCell start tuple = some [.location keyAddress, destination])
    (bounded : BoundedLocations start)
    (keyRepresentation : Ident c start (.location keyAddress) keyId)
    (wantedRepresentation : Ident c start wanted wantedId)
    (branchShape : program branch = some (.caseMatch call
      [(.boolean true, trueBody), (.boolean false, falseBody)]))
    (evaluation : Eval program callerEnv branch start result finish) :
    ∃ middle, Eval program callerEnv
        (if Ash.NetworkLedger.CoreRemoval.compareId keyId wantedId then trueBody else falseBody)
        middle result finish ∧
      start.nextLocation < middle.nextLocation ∧ middle.aliases = start.aliases ∧
      BoundedLocations middle ∧
      (∀ address values, readCell start address = some values → readCell middle address = some values) := by
  obtain ⟨middle, value, chosen, bindings, comparisonEval, selected, bodyEval⟩ :=
    case_match_inversion branchShape evaluation
  obtain ⟨sameValue, advances, aliasesSame, middleBounded, retained⟩ :=
    projection_comparator_retains c program call function argument projection wantedNode comparator projectionShape
      callerEnv start middle value wanted wantedId keyId functionName wantedName checkedArgument
      comparatorAddress comparatorResolved projectionAddress projectionResolved entryAddress entryResolved payload tuple
      keyAddress destination callShape functionShape functionBinding comparatorResolution comparatorCell projectionFresh
      entryFresh wantedFresh wantedShape projectionBinding entryBinding wantedBinding projectionResolution projectionCell
      entryResolution entryCell payloadResolution entryFields bounded keyRepresentation wantedRepresentation comparisonEval
  subst value
  obtain ⟨sameBody, sameBindings⟩ := boolean_selects middle
    (Ash.NetworkLedger.CoreRemoval.compareId keyId wantedId) trueBody falseBody selected
  subst chosen
  subst bindings
  exact ⟨middle, by simpa using bodyEval, advances, aliasesSame, middleBounded, retained⟩

/-- A selected host construction retains old cells for any exact field array. -/
theorem host_construct_retains {start queried afterAlloc finish : Store} {location : Nat}
    {values : List Value} (bounded : BoundedLocations start)
    (queryStep : query .hostDefault start = some (.hostDefault, queried))
    (allocated : allocate .hostDefault values.length true queried = some (location, afterAlloc))
    (initialized : initializeStorage location values.length values afterAlloc = some (values, finish)) :
    location = start.nextLocation ∧ finish.nextLocation = start.nextLocation + 1 ∧
      readCell finish location = some values ∧ finish.aliases = start.aliases ∧
      BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  have queryBound := query_preserves_bounded start queried .hostDefault .hostDefault bounded queryStep
  have allocationBound := allocation_preserves_bounded queried afterAlloc .hostDefault values.length true location
    queryBound allocated
  have finishBound := initialization_preserves_bounded afterAlloc finish location values.length
    values values allocationBound initialized
  simp only [query, Option.some.injEq, Prod.mk.injEq] at queryStep
  rcases queryStep with ⟨_, rfl⟩
  simp only [allocate, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Option.some.injEq, Prod.mk.injEq] at allocated
  rcases allocated with ⟨rfl, rfl⟩
  simp only [initializeStorage] at initialized
  split at initialized
  · simp only [Option.some.injEq, Prod.mk.injEq] at initialized
    rcases initialized with ⟨_, rfl⟩
    refine ⟨rfl, rfl, ?_, rfl, finishBound, ?_⟩
    · simp [readCell]
    · intro address old read
      have member := readCell_member start address old read
      have less := bounded.2.1 address old member
      have different : start.nextLocation ≠ address := by omega
      simpa [readCell, different] using read
  · simp_all

/-- The actual checked nullary constructor creates its nominal tag and retains the caller. -/
theorem checked_nullary_retains {program : Program} {node : NodeId} {tag : Constructor}
    {env : Environment} {start finish : Store} {result : Value}
    (checked : CheckedTuple program node (some tag) [])
    (bounded : BoundedLocations start) (evaluation : Eval program env node start result finish) :
    ∃ location, result = .location location ∧ location = start.nextLocation ∧
      finish.nextLocation = start.nextLocation + 1 ∧ readCell finish location = some [.tag tag] ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  obtain ⟨queried, afterFields, afterAlloc, location, values, queryStep, fieldEvals,
    allocated, initialized, resultEq⟩ := checked_tuple_inversion checked evaluation
  cases fieldEvals
  have allocated' : allocate .hostDefault ([.tag tag] : List Value).length true queried =
      some (location, afterAlloc) := by simpa using allocated
  have initialized' : initializeStorage location ([.tag tag] : List Value).length [.tag tag] afterAlloc =
      some ([.tag tag], finish) := by simpa [storedFields] using initialized
  obtain ⟨fresh, advances, cell, aliasesSame, finalBounded, retained⟩ :=
    host_construct_retains bounded queryStep allocated' initialized'
  exact ⟨location, resultEq, fresh, advances, cell, aliasesSame, finalBounded, retained⟩

/-- The actual allocation and initialization retain all prior live storage. -/
theorem host_allocation_retains {start afterAlloc finish : Store} {location : Nat}
    {values : List Value} (bounded : BoundedLocations start)
    (allocated : allocate .hostDefault values.length true start = some (location, afterAlloc))
    (initialized : initializeStorage location values.length values afterAlloc = some (values, finish)) :
    location = start.nextLocation ∧ finish.nextLocation = start.nextLocation + 1 ∧
      readCell finish location = some values ∧ finish.aliases = start.aliases ∧
      BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  have allocationBound := allocation_preserves_bounded start afterAlloc .hostDefault values.length true location
    bounded allocated
  have finishBound := initialization_preserves_bounded afterAlloc finish location values.length
    values values allocationBound initialized
  simp only [allocate, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    Option.some.injEq, Prod.mk.injEq] at allocated
  rcases allocated with ⟨rfl, rfl⟩
  simp only [initializeStorage] at initialized
  split at initialized
  · simp only [Option.some.injEq, Prod.mk.injEq] at initialized
    rcases initialized with ⟨_, rfl⟩
    refine ⟨rfl, rfl, ?_, rfl, finishBound, ?_⟩
    · simp [readCell]
    · intro address old read
      have member := readCell_member start address old read
      have less := bounded.2.1 address old member
      have different : start.nextLocation ≠ address := by omega
      simpa [readCell, different] using read
  · simp_all

/-- A checked result pair evaluates its list field, then its nullary status. -/
theorem checked_tail_status_result {program : Program} {root tailNode statusNode : NodeId}
    {tag : Constructor} {env : Environment} {start finish : Store} {result tail : Value}
    (pair : CheckedTuple program root none [tailNode, statusNode])
    (status : CheckedTuple program statusNode (some tag) []) (tailName : Binder)
    (tailShape : program tailNode = some (.variable tailName))
    (tailFresh : tailName ≠ pair.contextBinder)
    (tailBinding : CoreEval.lookup env tailName = some tail)
    (bounded : BoundedLocations start) (evaluation : Eval program env root start result finish) :
    ∃ pairAddress statusAddress,
      result = .location pairAddress ∧
      Result finish result tail (.location statusAddress) ∧
      Resolve finish statusAddress statusAddress ∧ readCell finish statusAddress = some [.tag tag] ∧
      start.nextLocation < finish.nextLocation ∧ finish.aliases = start.aliases ∧
      BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  obtain ⟨queried, afterFields, afterAlloc, pairAddress, values, queryStep, fieldEvals,
    allocated, initialized, resultEq⟩ := checked_tuple_inversion pair evaluation
  obtain ⟨middle, actualTail, actualStatus, tailEval, statusEval, sameValues⟩ :=
    pair_fields_inversion fieldEvals
  have tailBound : CoreEval.lookup (extend env pair.contextBinder .context) tailName = some tail := by
    rw [lookup_extended_other env pair.contextBinder tailName tailFresh]
    exact tailBinding
  obtain ⟨actualBinding, tailState⟩ := variable_inversion tailShape tailEval
  have sameTail : actualTail = tail := by simpa [tailBound] using actualBinding.symm
  subst actualTail
  subst middle
  have queryBound := query_preserves_bounded start queried .hostDefault .hostDefault bounded queryStep
  obtain ⟨statusAddress, statusEq, statusFresh, statusNext, statusCell, statusAliases,
    statusBound, statusRetained⟩ := checked_nullary_retains status queryBound statusEval
  subst actualStatus
  subst values
  have allocatePair : allocate .hostDefault ([tail, .location statusAddress] : List Value).length true afterFields =
      some (pairAddress, afterAlloc) := by simpa using allocated
  have initializePair : initializeStorage pairAddress ([tail, .location statusAddress] : List Value).length
      [tail, .location statusAddress] afterAlloc = some ([tail, .location statusAddress], finish) := by
    simpa [storedFields] using initialized
  obtain ⟨pairFresh, pairNext, pairCell, pairAliases, finalBound, pairRetained⟩ :=
    host_allocation_retains statusBound allocatePair initializePair
  have queryAliases : queried.aliases = start.aliases := by
    simp only [query, Option.some.injEq, Prod.mk.injEq] at queryStep
    rcases queryStep with ⟨_, rfl⟩
    rfl
  have allAliases : finish.aliases = start.aliases := pairAliases.trans (statusAliases.trans queryAliases)
  have finalStatus := pairRetained statusAddress _ statusCell
  have statusNoAlias : readAlias finish statusAddress = none := by
    simpa [readAlias, pairAliases, statusAliases, statusFresh] using bounded_fresh_no_alias queried queryBound
  have pairNoAlias : readAlias finish pairAddress = none := by
    simpa [readAlias, pairAliases, pairFresh] using bounded_fresh_no_alias afterFields statusBound
  have resultRep : Result finish result tail (.location statusAddress) := by
    rw [resultEq]
    exact Result.pair pairAddress pairAddress tail (.location statusAddress)
      (Resolve.cell pairAddress [tail, .location statusAddress] pairNoAlias pairCell) pairCell
  have progress : start.nextLocation < finish.nextLocation := by
    have statusBoundFinal := finalBound.2.1 statusAddress _ (readCell_member finish statusAddress _ finalStatus)
    have queryNext : queried.nextLocation = start.nextLocation := by
      simp only [query, Option.some.injEq, Prod.mk.injEq] at queryStep
      rcases queryStep with ⟨_, rfl⟩
      rfl
    rw [statusFresh, queryNext] at statusBoundFinal
    exact statusBoundFinal
  refine ⟨pairAddress, statusAddress, resultEq, resultRep,
    Resolve.cell statusAddress [.tag tag] statusNoAlias finalStatus, finalStatus,
    progress, allAliases, finalBound, ?_⟩
  intro address old read
  exact pairRetained address old (statusRetained address old (query_preserves_cell queryStep read))

/-- The same linked capture nodes and stored values determine one environment. -/
theorem capture_bindings_unique (program : Program) (nodes : List NodeId) (values : List Value)
    (left right : Environment) (first : CaptureBindings program nodes values left)
    (second : CaptureBindings program nodes values right) : left = right := by
  induction first generalizing right with
  | empty => cases second; rfl
  | cons node nodes name value values rest shape tail ih =>
    cases second with
    | cons _ _ other _ _ otherRest otherShape otherTail =>
      have same := Option.some.inj (shape.symm.trans otherShape)
      cases same
      have sameRest := ih otherRest otherTail
      cases sameRest
      rfl

/-- An ordinary recursive closure reopens its exact stored code and captures. -/
theorem captured_target (program : Program) (store : Store)
    (address resolved code context storage parameter body : Nat) (nodes : List NodeId)
    (values : List Value) (expected : Environment)
    (resolution : Resolve store address resolved)
    (fields : readCell store resolved = some (.closureCode code :: values))
    (shape : program code = some (.closure context nodes storage parameter body))
    (captureBindings : CaptureBindings program nodes values expected)
    {actualParameter : Binder} {actualBody : NodeId} {captured : Environment}
    (target : CallTarget program store (.location address) actualParameter actualBody captured) :
    actualParameter = parameter ∧ actualBody = body ∧ captured = expected.reverse := by
  cases target with
  | stored actualAddress other actualCode actualContext actualStorage captures
      actualParameter actualBody storedValues bindings callableAddress otherResolution otherFields actualShape actualBindings =>
    simp at callableAddress
    subst actualAddress
    have equalFields := resolved_fields_unique resolution otherResolution fields otherFields
    simp only [List.cons.injEq, Value.closureCode.injEq] at equalFields
    rcases equalFields with ⟨sameCode, sameValues⟩
    subst actualCode
    subst storedValues
    have sameShape := Option.some.inj (shape.symm.trans actualShape)
    simp only [Node.closure.injEq] at sameShape
    rcases sameShape with ⟨_, sameCaptures, _, sameParameter, sameBody⟩
    subst captures
    have sameBindings := capture_bindings_unique program nodes values expected bindings captureBindings actualBindings
    subst bindings
    simp_all

/-- A matching child returns its actual tail and Found status. -/
theorem removal_hit_returns_tail (c : Constructors) (program : Program)
    (branch trueBody falseBody call function argument projection wantedNode : NodeId)
    (comparator : ComparatorFunction c program) (projectionShape : ProjectionCallShape program projection)
    (callerEnv : Environment) (start finish : Store) (result wanted : Value)
    (wantedId keyId : Id) (functionName wantedName : Binder)
    (checkedArgument : CheckedTuple program argument none [projection, wantedNode])
    (comparatorAddress comparatorResolved projectionAddress projectionResolved : Nat)
    (entryAddress entryResolved payload tuple keyAddress : Nat) (destination : Value)
    (callShape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable functionName))
    (functionBinding : CoreEval.lookup callerEnv functionName = some (.location comparatorAddress))
    (comparatorResolution : Resolve start comparatorAddress comparatorResolved)
    (comparatorCell : readCell start comparatorResolved = some [.closureCode comparator.code])
    (projectionFresh : projectionShape.functionName ≠ checkedArgument.contextBinder)
    (entryFresh : projectionShape.entryName ≠ checkedArgument.contextBinder)
    (wantedFresh : wantedName ≠ checkedArgument.contextBinder)
    (wantedShape : program wantedNode = some (.variable wantedName))
    (projectionBinding : CoreEval.lookup callerEnv projectionShape.functionName = some (.location projectionAddress))
    (entryBinding : CoreEval.lookup callerEnv projectionShape.entryName = some (.location entryAddress))
    (wantedBinding : CoreEval.lookup callerEnv wantedName = some wanted)
    (projectionResolution : Resolve start projectionAddress projectionResolved)
    (projectionCell : readCell start projectionResolved = some [.closureCode projectionShape.code])
    (entryResolution : Resolve start entryAddress entryResolved)
    (entryCell : readCell start entryResolved = some [.tag projectionShape.child, .location payload])
    (payloadResolution : Resolve start payload tuple)
    (entryFields : readCell start tuple = some [.location keyAddress, destination])
    (bounded : BoundedLocations start)
    (keyRepresentation : Ident c start (.location keyAddress) keyId)
    (wantedRepresentation : Ident c start wanted wantedId)
    (branchShape : program branch = some (.caseMatch call
      [(.boolean true, trueBody), (.boolean false, falseBody)]))
    (tailNode foundNode : NodeId) (tailName : Binder) (tail : Value) (entries : List Value)
    (hitPair : CheckedTuple program trueBody none [tailNode, foundNode])
    (found : CheckedTuple program foundNode (some c.found) [])
    (tailShape : program tailNode = some (.variable tailName))
    (tailFresh : tailName ≠ hitPair.contextBinder)
    (tailBinding : CoreEval.lookup callerEnv tailName = some tail)
    (tailRepresentation : Children c start tail entries)
    (sameKey : keyId = wantedId)
    (evaluation : Eval program callerEnv branch start result finish) :
    ∃ statusAddress, Result finish result tail (.location statusAddress) ∧
      Resolve finish statusAddress statusAddress ∧ readCell finish statusAddress = some [.tag c.found] ∧
      Children c finish tail entries ∧ start.nextLocation < finish.nextLocation ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  obtain ⟨middle, selectedEval, advances, aliasesSame, middleBounded, retained⟩ :=
    removal_comparison_selects c program branch trueBody falseBody call function argument projection wantedNode
      comparator projectionShape callerEnv start finish result wanted wantedId keyId functionName wantedName checkedArgument
      comparatorAddress comparatorResolved projectionAddress projectionResolved entryAddress entryResolved payload tuple
      keyAddress destination callShape functionShape functionBinding comparatorResolution comparatorCell projectionFresh
      entryFresh wantedFresh wantedShape projectionBinding entryBinding wantedBinding projectionResolution projectionCell
      entryResolution entryCell payloadResolution entryFields bounded keyRepresentation wantedRepresentation branchShape evaluation
  have equalComparison : Ash.NetworkLedger.CoreRemoval.compareId keyId wantedId = true :=
    (Ash.NetworkLedger.CoreRemoval.compareId_correct keyId wantedId).mpr sameKey
  simp only [equalComparison, if_true] at selectedEval
  obtain ⟨_, statusAddress, _, resultRep, statusResolved, statusCell, hitAdvances, hitAliases,
    finishBounded, hitRetained⟩ :=
    checked_tail_status_result hitPair found tailName tailShape tailFresh tailBinding middleBounded selectedEval
  have aliasesFinal : finish.aliases = start.aliases := hitAliases.trans aliasesSame
  have allRetained : ∀ address old, readCell start address = some old → readCell finish address = some old := by
    intro address old read
    exact hitRetained address old (retained address old read)
  exact ⟨statusAddress, resultRep, statusResolved, statusCell,
    children_retained c start finish tail entries aliasesFinal allRetained tailRepresentation,
    Nat.lt_trans advances hitAdvances, aliasesFinal, finishBounded, allRetained⟩

/-- The Empty return constructs the actual empty list and Missing status in field order. -/
theorem checked_empty_missing_result {program : Program} {root emptyNode missingNode : NodeId}
    {c : Constructors} {env : Environment} {start finish : Store} {result : Value}
    (pair : CheckedTuple program root none [emptyNode, missingNode])
    (empty : CheckedTuple program emptyNode (some c.empty) [])
    (missing : CheckedTuple program missingNode (some c.missing) [])
    (bounded : BoundedLocations start) (evaluation : Eval program env root start result finish) :
    ∃ listAddress statusAddress,
      Result finish result (.location listAddress) (.location statusAddress) ∧
      Children c finish (.location listAddress) [] ∧
      Resolve finish statusAddress statusAddress ∧ readCell finish statusAddress = some [.tag c.missing] ∧
      start.nextLocation < finish.nextLocation ∧ finish.aliases = start.aliases ∧
      BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  obtain ⟨queried, afterFields, afterAlloc, pairAddress, values, queryStep, fieldEvals,
    allocated, initialized, resultEq⟩ := checked_tuple_inversion pair evaluation
  obtain ⟨middle, actualEmpty, actualMissing, emptyEval, missingEval, sameValues⟩ :=
    pair_fields_inversion fieldEvals
  have queryBound := query_preserves_bounded start queried .hostDefault .hostDefault bounded queryStep
  obtain ⟨listAddress, emptyEq, emptyFresh, _, emptyCell, emptyAliases, emptyBound, emptyRetained⟩ :=
    checked_nullary_retains empty queryBound emptyEval
  subst actualEmpty
  obtain ⟨statusAddress, missingEq, missingFresh, _, missingCell, missingAliases, missingBound, missingRetained⟩ :=
    checked_nullary_retains missing emptyBound missingEval
  subst actualMissing
  subst values
  have allocatePair : allocate .hostDefault ([.location listAddress, .location statusAddress] : List Value).length true afterFields =
      some (pairAddress, afterAlloc) := by simpa using allocated
  have initializePair : initializeStorage pairAddress ([.location listAddress, .location statusAddress] : List Value).length
      [.location listAddress, .location statusAddress] afterAlloc =
      some ([.location listAddress, .location statusAddress], finish) := by simpa [storedFields] using initialized
  obtain ⟨pairFresh, _, pairCell, pairAliases, finalBound, pairRetained⟩ :=
    host_allocation_retains missingBound allocatePair initializePair
  have queryAliases : queried.aliases = start.aliases := by
    simp only [query, Option.some.injEq, Prod.mk.injEq] at queryStep
    rcases queryStep with ⟨_, rfl⟩
    rfl
  have allAliases : finish.aliases = start.aliases :=
    pairAliases.trans (missingAliases.trans (emptyAliases.trans queryAliases))
  have finalEmpty := pairRetained listAddress _ (missingRetained listAddress _ emptyCell)
  have finalMissing := pairRetained statusAddress _ missingCell
  have emptyNoAlias : readAlias finish listAddress = none := by
    simpa [readAlias, pairAliases, missingAliases, emptyAliases, emptyFresh] using bounded_fresh_no_alias queried queryBound
  have missingNoAlias : readAlias finish statusAddress = none := by
    simpa [readAlias, pairAliases, missingAliases, missingFresh] using bounded_fresh_no_alias middle emptyBound
  have pairNoAlias : readAlias finish pairAddress = none := by
    simpa [readAlias, pairAliases, pairFresh] using bounded_fresh_no_alias afterFields missingBound
  have resultRep : Result finish result (.location listAddress) (.location statusAddress) := by
    rw [resultEq]
    exact Result.pair pairAddress pairAddress (.location listAddress) (.location statusAddress)
      (Resolve.cell pairAddress [.location listAddress, .location statusAddress] pairNoAlias pairCell) pairCell
  have progress : start.nextLocation < finish.nextLocation := by
    have finalEmptyBound := finalBound.2.1 listAddress _ (readCell_member finish listAddress _ finalEmpty)
    have queryNext : queried.nextLocation = start.nextLocation := by
      simp only [query, Option.some.injEq, Prod.mk.injEq] at queryStep
      rcases queryStep with ⟨_, rfl⟩
      rfl
    rw [emptyFresh, queryNext] at finalEmptyBound
    exact finalEmptyBound
  refine ⟨listAddress, statusAddress, resultRep,
    Children.empty listAddress listAddress (Resolve.cell listAddress [.tag c.empty] emptyNoAlias finalEmpty) finalEmpty,
    Resolve.cell statusAddress [.tag c.missing] missingNoAlias finalMissing, finalMissing,
    progress, allAliases, finalBound, ?_⟩
  intro address old read
  exact pairRetained address old (missingRetained address old (emptyRetained address old
    (query_preserves_cell queryStep read)))

/-- A checked removal on actual Empty returns a represented Empty/Missing pair. -/
theorem removal_empty_returns (c : Constructors) (program : Program) (env : Environment)
    (node scrutinee emptyBody moreBody emptyNode missingNode : NodeId)
    (binder entryName tailName : Binder) (start finish : Store) (list result : Value)
    (shape : program node = some (.caseMatch scrutinee
      [(.constructor c.empty none, emptyBody),
       (.constructor c.more (some (.tuple [.binder entryName, .binder tailName])), moreBody)]))
    (variableShape : program scrutinee = some (.variable binder))
    (binding : CoreEval.lookup env binder = some list)
    (pair : CheckedTuple program emptyBody none [emptyNode, missingNode])
    (empty : CheckedTuple program emptyNode (some c.empty) [])
    (missing : CheckedTuple program missingNode (some c.missing) [])
    (bounded : BoundedLocations start) (representation : Children c start list [])
    (evaluation : Eval program env node start result finish) :
    ∃ listAddress statusAddress,
      Result finish result (.location listAddress) (.location statusAddress) ∧
      Children c finish (.location listAddress) [] ∧
      Resolve finish statusAddress statusAddress ∧ readCell finish statusAddress = some [.tag c.missing] ∧
      start.nextLocation < finish.nextLocation ∧ finish.aliases = start.aliases ∧
      BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  cases representation with
  | empty address resolved resolution cell =>
    have emptyEval := empty_match_executes_first program start finish env node scrutinee binder c.empty c.more
      emptyBody moreBody (.tuple [.binder entryName, .binder tailName]) address resolved result
      shape variableShape binding resolution cell evaluation
    exact checked_empty_missing_result pair empty missing bounded emptyEval

/-- A checked unary constructor stores its nominal tag and exact operand. -/
theorem checked_unary_constructor_retains {program : Program} {node operand : NodeId}
    {tag : Constructor} {env : Environment} {start finish : Store} {result value : Value}
    (checked : CheckedTuple program node (some tag) [operand]) (name : Binder)
    (operandShape : program operand = some (.variable name))
    (fresh : name ≠ checked.contextBinder)
    (binding : CoreEval.lookup env name = some value)
    (bounded : BoundedLocations start) (evaluation : Eval program env node start result finish) :
    ∃ location, result = .location location ∧ location = start.nextLocation ∧
      finish.nextLocation = start.nextLocation + 1 ∧ readCell finish location = some [.tag tag, value] ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  obtain ⟨queried, afterFields, afterAlloc, location, values, queryStep, fieldEvals,
    allocated, initialized, resultEq⟩ := checked_tuple_inversion checked evaluation
  have extended : CoreEval.lookup (extend env checked.contextBinder .context) name = some value := by
    rw [lookup_extended_other env checked.contextBinder name fresh]
    exact binding
  cases fieldEvals with
  | cons head tail =>
    cases tail
    obtain ⟨actualBinding, sameStore⟩ := variable_inversion operandShape head
    have sameValue := Option.some.inj (actualBinding.symm.trans extended)
    have allocated' : allocate .hostDefault ([.tag tag, value] : List Value).length true queried =
        some (location, afterAlloc) := by simpa [sameStore] using allocated
    have initialized' : initializeStorage location ([.tag tag, value] : List Value).length
        [.tag tag, value] afterAlloc = some ([.tag tag, value], finish) := by
      simpa [storedFields, sameValue] using initialized
    obtain ⟨newLocation, advances, cell, aliasesSame, finalBound, retained⟩ :=
      host_construct_retains bounded queryStep allocated' initialized'
    exact ⟨location, resultEq, newLocation, advances, cell, aliasesSame, finalBound, retained⟩

/-- The linked capture-free constructor closure has the standard host allocation graph. -/
structure CheckedClosure (program : Program) (root : NodeId) where
  contextBinder : Binder
  queryNode : NodeId
  unitNode : NodeId
  closureNode : NodeId
  contextNode : NodeId
  storageNode : NodeId
  storageContextNode : NodeId
  requestNode : NodeId
  parameter : Binder
  body : NodeId
  rootShape : program root = some (.bind contextBinder queryNode closureNode)
  queryShape : program queryNode = some (.query unitNode)
  unitShape : program unitNode = some .unit
  closureShape : program closureNode = some (.closure contextNode [] storageNode parameter body)
  contextShape : program contextNode = some (.variable contextBinder)
  storageShape : program storageNode = some (.allocate storageContextNode requestNode)
  storageContextShape : program storageContextNode = some (.variable contextBinder)
  requestShape : program requestNode = some (.request 1)

/-- Normal closure initialization allocates its actual capture-free code cell. -/
theorem checked_closure_retains {program : Program} {node : NodeId}
    {env : Environment} {start finish : Store} {result : Value}
    (checked : CheckedClosure program node) (bounded : BoundedLocations start)
    (evaluation : Eval program env node start result finish) :
    ∃ location, result = .function location ∧ location = start.nextLocation ∧
      finish.nextLocation = start.nextLocation + 1 ∧
      readCell finish location = some [.closureCode checked.closureNode] ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  obtain ⟨queried, initialValue, initialEval, closureEval⟩ := bind_inversion checked.rootShape evaluation
  obtain ⟨valueEq, afterOperand, chosen, operandEval, queryStep⟩ := query_inversion checked.queryShape initialEval
  subst initialValue
  obtain ⟨_, operandState⟩ := unit_inversion checked.unitShape operandEval
  subst afterOperand
  have chosenHost := (query_projects start queried .hostDefault chosen queryStep).1
  subst chosen
  cases closureEval with
  | closure actualShape contextEval captureEvals storageEval initialized =>
    have sameShape := Option.some.inj (checked.closureShape.symm.trans actualShape)
    simp only [Node.closure.injEq] at sameShape
    rcases sameShape with ⟨rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨_, contextState⟩ := variable_inversion checked.contextShape contextEval
    cases captureEvals
    obtain ⟨afterStorageContext, afterRequest, requested, allocatedLocation,
      storageContextEval, requestEval, allocated, storageValue⟩ :=
      allocate_inversion checked.storageShape storageEval
    have storageShape : _ := storageValue
    simp only [Value.storage.injEq] at storageShape
    rcases storageShape with ⟨rfl, rfl⟩
    obtain ⟨_, storageContextState⟩ := variable_inversion checked.storageContextShape storageContextEval
    subst afterStorageContext
    obtain ⟨requestValue, requestState⟩ := request_inversion checked.requestShape requestEval
    subst afterRequest
    simp only [Value.request.injEq] at requestValue
    cases requestValue
    rw [contextState] at allocated
    obtain ⟨fresh, advances, cell, aliasesSame, finishBound, retained⟩ :=
      host_construct_retains (values := [.closureCode checked.closureNode]) bounded queryStep allocated initialized
    exact ⟨_, rfl, fresh, advances, cell, aliasesSame, finishBound, retained⟩
  | _ => simp_all [checked.closureShape]

/-- A freshly allocated closure reopens the same checked capture-free code. -/
theorem capture_free_function_target (program : Program) (store : Store)
    (address resolved code context storage parameter body : Nat)
    (resolution : Resolve store address resolved)
    (fields : readCell store resolved = some [.closureCode code])
    (shape : program code = some (.closure context [] storage parameter body))
    {actualParameter : Binder} {actualBody : NodeId} {captured : Environment}
    (target : CallTarget program store (.function address) actualParameter actualBody captured) :
    actualParameter = parameter ∧ actualBody = body ∧ captured = [] := by
  cases target with
  | stored actualAddress other actualCode actualContext actualStorage captures
      actualParameter actualBody values bindings callableAddress otherResolution otherFields actualShape captureBindings =>
    simp at callableAddress
    subst actualAddress
    have equalFields := resolved_fields_unique resolution otherResolution fields otherFields
    simp only [List.cons.injEq, Value.closureCode.injEq] at equalFields
    rcases equalFields with ⟨sameCode, sameValues⟩
    subst actualCode
    subst values
    have sameShape := Option.some.inj (shape.symm.trans actualShape)
    simp only [Node.closure.injEq] at sameShape
    rcases sameShape with ⟨_, sameCaptures, _, sameParameter, sameBody⟩
    subst captures
    cases captureBindings
    simp_all


/-- Rebuilding More evaluates the stored constructor closure and keeps the original whole entry. -/
theorem checked_more_rebuild (c : Constructors) (program : Program)
    (call function argument entryNode remainingNode operand : NodeId)
    (closure : CheckedClosure program function)
    (pair : CheckedTuple program argument none [entryNode, remainingNode])
    (constructor : CheckedTuple program closure.body (some c.more) [operand])
    (env : Environment) (start finish : Store) (result entry remaining : Value) (entries : List Value)
    (entryName remainingName : Binder)
    (callShape : program call = some (.apply function argument))
    (entryShape : program entryNode = some (.variable entryName))
    (remainingShape : program remainingNode = some (.variable remainingName))
    (entryFresh : entryName ≠ pair.contextBinder)
    (remainingFresh : remainingName ≠ pair.contextBinder)
    (entryBinding : CoreEval.lookup env entryName = some entry)
    (remainingBinding : CoreEval.lookup env remainingName = some remaining)
    (operandShape : program operand = some (.variable closure.parameter))
    (operandFresh : closure.parameter ≠ constructor.contextBinder)
    (bounded : BoundedLocations start) (tailRepresentation : Children c start remaining entries)
    (evaluation : Eval program env call start result finish) :
    Children c finish result (entry :: entries) ∧ start.nextLocation < finish.nextLocation ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  obtain ⟨afterFunction, afterArgument, callable, argumentValue, parameter, body, captured,
    functionEval, target, argumentEval, bodyEval⟩ := apply_inversion callShape evaluation
  obtain ⟨closureLocation, closureEq, closureFresh, _, closureCell, closureAliases, closureBound, closureRetained⟩ :=
    checked_closure_retains closure bounded functionEval
  subst callable
  have closureNoAlias : readAlias afterFunction closureLocation = none := by
    simpa [readAlias, closureAliases, closureFresh] using bounded_fresh_no_alias start bounded
  have closureResolution : Resolve afterFunction closureLocation closureLocation :=
    Resolve.cell closureLocation [.closureCode closure.closureNode] closureNoAlias closureCell
  obtain ⟨sameParameter, sameBody, sameCapture⟩ :=
    capture_free_function_target program afterFunction closureLocation closureLocation closure.closureNode
      closure.contextNode closure.storageNode closure.parameter closure.body closureResolution closureCell
      closure.closureShape target
  subst parameter
  subst body
  subst captured
  obtain ⟨payload, payloadFresh, payloadEq, payloadCell, payloadAliases, payloadBound, payloadRetained⟩ :=
    checked_variable_pair_retains pair entryName remainingName entryShape remainingShape entryFresh remainingFresh
      entryBinding remainingBinding closureBound argumentEval
  subst argumentValue
  have operandBinding : CoreEval.lookup (extend [] closure.parameter (.location payload)) closure.parameter =
      some (.location payload) := by simp [CoreEval.lookup, extend]
  obtain ⟨listAddress, resultEq, listFresh, _, listCell, listAliases, finalBound, listRetained⟩ :=
    checked_unary_constructor_retains constructor closure.parameter operandShape operandFresh operandBinding
      payloadBound bodyEval
  have aliasesFinal : finish.aliases = start.aliases := listAliases.trans (payloadAliases.trans closureAliases)
  have allRetained : ∀ address old, readCell start address = some old → readCell finish address = some old := by
    intro address old read
    exact listRetained address old (payloadRetained address old (closureRetained address old read))
  have listNoAlias : readAlias finish listAddress = none := by
    simpa [readAlias, listAliases, listFresh] using bounded_fresh_no_alias afterArgument payloadBound
  have payloadNoAlias : readAlias finish payload = none := by
    simpa [readAlias, listAliases, payloadAliases, payloadFresh] using bounded_fresh_no_alias afterFunction closureBound
  have finalPayload := listRetained payload _ payloadCell
  have tailFinal := children_retained c start finish remaining entries aliasesFinal allRetained tailRepresentation
  have listRep : Children c finish result (entry :: entries) := by
    rw [resultEq]
    exact Children.more listAddress listAddress payload payload entry remaining entries
      (Resolve.cell listAddress [.tag c.more, .location payload] listNoAlias listCell) listCell
      (Resolve.cell payload [entry, remaining] payloadNoAlias finalPayload) finalPayload tailFinal
  have progress : start.nextLocation < finish.nextLocation := by
    have live := finalBound.2.1 closureLocation _
      (readCell_member finish closureLocation _ (listRetained closureLocation _ (payloadRetained closureLocation _ closureCell)))
    rw [closureFresh] at live
    exact live
  exact ⟨listRep, progress, aliasesFinal, finalBound, allRetained⟩

/-- A recursive call reopens the stored closure before constructing the wanted/tail argument. -/
theorem checked_recursive_call (program : Program) (call function argument wantedNode tailNode : NodeId)
    (env : Environment) (start finish : Store) (result wanted tail : Value)
    (functionName wantedName tailName : Binder) (address resolved code context storage parameter body : NodeId)
    (captureNodes : List NodeId) (captureValues : List Value) (captureEnv : Environment)
    (pair : CheckedTuple program argument none [wantedNode, tailNode])
    (callShape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable functionName))
    (functionBinding : CoreEval.lookup env functionName = some (.location address))
    (resolution : Resolve start address resolved)
    (functionCell : readCell start resolved = some (.closureCode code :: captureValues))
    (closureShape : program code = some (.closure context captureNodes storage parameter body))
    (captureBindings : CaptureBindings program captureNodes captureValues captureEnv)
    (wantedShape : program wantedNode = some (.variable wantedName))
    (tailShape : program tailNode = some (.variable tailName))
    (wantedFresh : wantedName ≠ pair.contextBinder) (tailFresh : tailName ≠ pair.contextBinder)
    (wantedBinding : CoreEval.lookup env wantedName = some wanted)
    (tailBinding : CoreEval.lookup env tailName = some tail)
    (bounded : BoundedLocations start) (evaluation : Eval program env call start result finish) :
    ∃ afterArgument payload,
      Eval program (extend captureEnv.reverse parameter (.location payload)) body afterArgument result finish ∧
      Resolve afterArgument payload payload ∧ readCell afterArgument payload = some [wanted, tail] ∧
      afterArgument.nextLocation = start.nextLocation + 1 ∧
      afterArgument.aliases = start.aliases ∧ BoundedLocations afterArgument ∧
      (∀ address old, readCell start address = some old → readCell afterArgument address = some old) := by
  obtain ⟨afterFunction, afterArgument, callable, argumentValue, actualParameter, actualBody, captured,
    functionEval, target, argumentEval, bodyEval⟩ := apply_inversion callShape evaluation
  obtain ⟨actualBinding, sameStore⟩ := variable_inversion functionShape functionEval
  have sameFunction : callable = .location address := by simpa [functionBinding] using actualBinding.symm
  subst callable
  subst afterFunction
  obtain ⟨sameParameter, sameBody, sameCapture⟩ :=
    captured_target program start address resolved code context storage parameter body captureNodes captureValues
      captureEnv resolution functionCell closureShape captureBindings target
  subst actualParameter
  subst actualBody
  subst captured
  obtain ⟨payload, fresh, argumentEq, pairCell, aliasesSame, afterBound, retained⟩ :=
    checked_variable_pair_retains pair wantedName tailName wantedShape tailShape wantedFresh tailFresh
      wantedBinding tailBinding bounded argumentEval
  subst argumentValue
  have noAlias : readAlias afterArgument payload = none := by
    simpa [readAlias, aliasesSame, fresh] using bounded_fresh_no_alias start bounded
  have advances := checked_variable_pair_advances pair wantedName tailName wantedShape tailShape wantedFresh tailFresh
    wantedBinding tailBinding argumentEval
  exact ⟨afterArgument, payload, bodyEval, Resolve.cell payload [wanted, tail] noAlias pairCell,
    pairCell, advances, aliasesSame, afterBound, retained⟩

/-- The miss return rebuilds More from the original entry and preserves the recursive status. -/
theorem checked_rebuilt_status_result (c : Constructors) (program : Program)
    (root rebuild statusNode function argument entryNode remainingNode operand : NodeId)
    (closure : CheckedClosure program function)
    (arguments : CheckedTuple program argument none [entryNode, remainingNode])
    (constructor : CheckedTuple program closure.body (some c.more) [operand])
    (pair : CheckedTuple program root none [rebuild, statusNode])
    (env : Environment) (start finish : Store) (result entry remaining status : Value) (entries : List Value)
    (entryName remainingName statusName : Binder)
    (rebuildShape : program rebuild = some (.apply function argument))
    (entryShape : program entryNode = some (.variable entryName))
    (remainingShape : program remainingNode = some (.variable remainingName))
    (statusShape : program statusNode = some (.variable statusName))
    (entryFresh : entryName ≠ arguments.contextBinder)
    (remainingFresh : remainingName ≠ arguments.contextBinder)
    (entryOuterFresh : entryName ≠ pair.contextBinder)
    (remainingOuterFresh : remainingName ≠ pair.contextBinder)
    (statusOuterFresh : statusName ≠ pair.contextBinder)
    (entryBinding : CoreEval.lookup env entryName = some entry)
    (remainingBinding : CoreEval.lookup env remainingName = some remaining)
    (statusBinding : CoreEval.lookup env statusName = some status)
    (operandShape : program operand = some (.variable closure.parameter))
    (operandFresh : closure.parameter ≠ constructor.contextBinder)
    (bounded : BoundedLocations start) (tailRepresentation : Children c start remaining entries)
    (evaluation : Eval program env root start result finish) :
    ∃ rebuilt, Result finish result rebuilt status ∧ Children c finish rebuilt (entry :: entries) ∧
      start.nextLocation < finish.nextLocation ∧ finish.aliases = start.aliases ∧
      BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  obtain ⟨queried, afterFields, afterAlloc, pairAddress, values, queryStep, fieldEvals,
    allocated, initialized, resultEq⟩ := checked_tuple_inversion pair evaluation
  obtain ⟨middle, rebuilt, actualStatus, rebuildEval, statusEval, sameValues⟩ :=
    pair_fields_inversion fieldEvals
  have entryExtended : CoreEval.lookup (extend env pair.contextBinder .context) entryName = some entry := by
    rw [lookup_extended_other env pair.contextBinder entryName entryOuterFresh]
    exact entryBinding
  have remainingExtended : CoreEval.lookup (extend env pair.contextBinder .context) remainingName = some remaining := by
    rw [lookup_extended_other env pair.contextBinder remainingName remainingOuterFresh]
    exact remainingBinding
  have statusExtended : CoreEval.lookup (extend env pair.contextBinder .context) statusName = some status := by
    rw [lookup_extended_other env pair.contextBinder statusName statusOuterFresh]
    exact statusBinding
  have queryBound := query_preserves_bounded start queried .hostDefault .hostDefault bounded queryStep
  have queryAliases : queried.aliases = start.aliases := by
    simp only [query, Option.some.injEq, Prod.mk.injEq] at queryStep
    rcases queryStep with ⟨_, rfl⟩
    rfl
  have queryRetained : ∀ address old, readCell start address = some old → readCell queried address = some old := by
    intro address old read
    exact query_preserves_cell queryStep read
  have queryTail := children_retained c start queried remaining entries queryAliases queryRetained tailRepresentation
  obtain ⟨rebuiltRep, rebuildProgress, rebuildAliases, rebuildBound, rebuildRetained⟩ :=
    checked_more_rebuild c program rebuild function argument entryNode remainingNode operand closure arguments constructor
      (extend env pair.contextBinder .context) queried middle rebuilt entry remaining entries entryName remainingName
      rebuildShape entryShape remainingShape entryFresh remainingFresh entryExtended remainingExtended operandShape
      operandFresh queryBound queryTail rebuildEval
  obtain ⟨actualStatusBinding, statusStore⟩ := variable_inversion statusShape statusEval
  have sameStatus : actualStatus = status := by simpa [statusExtended] using actualStatusBinding.symm
  subst actualStatus
  subst afterFields
  subst values
  have allocatePair : allocate .hostDefault ([rebuilt, status] : List Value).length true middle =
      some (pairAddress, afterAlloc) := by simpa using allocated
  have initializePair : initializeStorage pairAddress ([rebuilt, status] : List Value).length
      [rebuilt, status] afterAlloc = some ([rebuilt, status], finish) := by simpa [storedFields] using initialized
  obtain ⟨pairFresh, _, pairCell, pairAliases, finishBounded, pairRetained⟩ :=
    host_allocation_retains rebuildBound allocatePair initializePair
  have allAliases : finish.aliases = start.aliases := pairAliases.trans (rebuildAliases.trans queryAliases)
  have allRetained : ∀ address old, readCell start address = some old → readCell finish address = some old := by
    intro address old read
    exact pairRetained address old (rebuildRetained address old (queryRetained address old read))
  have pairNoAlias : readAlias finish pairAddress = none := by
    simpa [readAlias, pairAliases, pairFresh] using bounded_fresh_no_alias middle rebuildBound
  have resultRep : Result finish result rebuilt status := by
    rw [resultEq]
    exact Result.pair pairAddress pairAddress rebuilt status
      (Resolve.cell pairAddress [rebuilt, status] pairNoAlias pairCell) pairCell
  have queryNext : queried.nextLocation = start.nextLocation := by
    simp only [query, Option.some.injEq, Prod.mk.injEq] at queryStep
    rcases queryStep with ⟨_, rfl⟩
    rfl
  have pairProgress : middle.nextLocation < finish.nextLocation := by
    have member := readCell_member finish pairAddress _ pairCell
    have less := finishBounded.2.1 pairAddress _ member
    simpa [pairFresh] using less
  rw [queryNext] at rebuildProgress
  exact ⟨rebuilt, resultRep, children_retained c middle finish rebuilt (entry :: entries)
    pairAliases pairRetained rebuiltRep, Nat.lt_trans rebuildProgress pairProgress,
    allAliases, finishBounded, allRetained⟩

/-- A returned status is the actual stored Found or Missing constructor. -/
inductive StatusRepresentation (c : Constructors) (store : Store) : Value → Ash.NetworkLedger.Status → Prop where
  | found (address resolved : Nat) (resolution : Resolve store address resolved)
      (cell : readCell store resolved = some [.tag c.found]) :
      StatusRepresentation c store (.location address) .found
  | missing (address resolved : Nat) (resolution : Resolve store address resolved)
      (cell : readCell store resolved = some [.tag c.missing]) :
      StatusRepresentation c store (.location address) .missing

/-- Unchanged alias links and stored cells retain the exact returned status. -/
theorem status_retained (c : Constructors) (before after : Store) (value : Value) (status : Ash.NetworkLedger.Status)
    (aliasesSame : after.aliases = before.aliases)
    (cellsRetained : ∀ location values, readCell before location = some values → readCell after location = some values)
    (representation : StatusRepresentation c before value status) : StatusRepresentation c after value status := by
  cases representation with
  | found address resolved resolution cell =>
    exact StatusRepresentation.found address resolved (resolve_preserved aliasesSame cellsRetained resolution)
      (cellsRetained resolved _ cell)
  | missing address resolved resolution cell =>
    exact StatusRepresentation.missing address resolved (resolve_preserved aliasesSame cellsRetained resolution)
      (cellsRetained resolved _ cell)

/-- Each actual whole entry carries the modeled key used by Remove. -/
def KeyedEntries (c : Constructors) (store : Store) (key : Value → Id) (entries : List Value) : Prop :=
  ∀ entry ∈ entries, ∃ keyAddress destination,
    Entry c store entry (.location keyAddress) destination ∧ Ident c store (.location keyAddress) (key entry)

/-- Retained heap cells keep each exact entry and its represented key. -/
theorem keyed_entries_retained (c : Constructors) (before after : Store) (key : Value → Id) (entries : List Value)
    (aliasesSame : after.aliases = before.aliases)
    (cellsRetained : ∀ location values, readCell before location = some values → readCell after location = some values)
    (keyed : KeyedEntries c before key entries) : KeyedEntries c after key entries := by
  intro entry member
  obtain ⟨keyAddress, destination, entryRep, keyRep⟩ := keyed entry member
  exact ⟨keyAddress, destination, entry_retained c before after entry (.location keyAddress) destination
    aliasesSame cellsRetained entryRep,
    ident_retained c before after (.location keyAddress) (key entry) aliasesSame cellsRetained keyRep⟩

/-- Every represented finite list has a stored location. -/
theorem children_is_location (c : Constructors) (store : Store) (value : Value) (entries : List Value)
    (representation : Children c store value entries) : ∃ address, value = .location address := by
  cases representation <;> exact ⟨_, rfl⟩

/-- Normal removal returns the actual list and status with all old storage retained. -/
def RemovalOutcome (c : Constructors) (start finish : Store) (result : Value)
    (entries : List Value) (status : Ash.NetworkLedger.Status) : Prop :=
  ∃ listValue statusValue, Result finish result listValue statusValue ∧
    Children c finish listValue entries ∧ StatusRepresentation c finish statusValue status ∧
    start.nextLocation < finish.nextLocation ∧ finish.aliases = start.aliases ∧ BoundedLocations finish ∧
    (∀ address old, readCell start address = some old → readCell finish address = some old)

/-- Exact checked miss branch and whole-entry reconstruction graph. -/
structure CheckedMiss (c : Constructors) (program : Program) where
  node : NodeId
  recursiveCall : NodeId
  recursiveFunction : NodeId
  recursiveArgument : NodeId
  wantedNode : NodeId
  tailNode : NodeId
  resultBody : NodeId
  rebuild : NodeId
  statusNode : NodeId
  constructorFunction : NodeId
  constructorArgument : NodeId
  entryNode : NodeId
  remainingNode : NodeId
  operand : NodeId
  functionName : Binder
  wantedName : Binder
  tailName : Binder
  entryName : Binder
  remainingName : Binder
  statusName : Binder
  recursivePair : CheckedTuple program recursiveArgument none [wantedNode, tailNode]
  constructorClosure : CheckedClosure program constructorFunction
  constructorPair : CheckedTuple program constructorArgument none [entryNode, remainingNode]
  constructorBody : CheckedTuple program constructorClosure.body (some c.more) [operand]
  resultPair : CheckedTuple program resultBody none [rebuild, statusNode]
  branchShape : program node = some (.caseMatch recursiveCall
    [(.tuple [.binder remainingName, .binder statusName], resultBody)])
  recursiveCallShape : program recursiveCall = some (.apply recursiveFunction recursiveArgument)
  recursiveFunctionShape : program recursiveFunction = some (.variable functionName)
  wantedShape : program wantedNode = some (.variable wantedName)
  tailShape : program tailNode = some (.variable tailName)
  rebuildShape : program rebuild = some (.apply constructorFunction constructorArgument)
  entryShape : program entryNode = some (.variable entryName)
  remainingShape : program remainingNode = some (.variable remainingName)
  statusShape : program statusNode = some (.variable statusName)
  operandShape : program operand = some (.variable constructorClosure.parameter)
  recursiveWantedFresh : wantedName ≠ recursivePair.contextBinder
  recursiveTailFresh : tailName ≠ recursivePair.contextBinder
  constructorEntryFresh : entryName ≠ constructorPair.contextBinder
  constructorRemainingFresh : remainingName ≠ constructorPair.contextBinder
  resultEntryFresh : entryName ≠ resultPair.contextBinder
  resultRemainingFresh : remainingName ≠ resultPair.contextBinder
  resultStatusFresh : statusName ≠ resultPair.contextBinder
  constructorOperandFresh : constructorClosure.parameter ≠ constructorBody.contextBinder
  entryRemainingDistinct : entryName ≠ remainingName
  entryStatusDistinct : entryName ≠ statusName
  remainingStatusDistinct : remainingName ≠ statusName

/-- A distinct binder retains an earlier binding for any bound value. -/
theorem lookup_extended_value_other (env : Environment) (bound name : Binder) (value : Value)
    (different : name ≠ bound) :
    CoreEval.lookup (extend env bound value) name = CoreEval.lookup env name := by
  simp [CoreEval.lookup, extend, Ne.symm different]

/-- The checked miss branch applies its induction hypothesis only to the actual tail. -/
theorem removal_miss_step_with (c : Constructors) (program : Program) (checked : CheckedMiss c program)
    (env : Environment) (start finish : Store) (result entry wanted tail : Value)
    (entries : List Value) (key : Value → Id) (queryId : Id)
    (address resolved code context storage parameter body : NodeId)
    (captureNodes : List NodeId) (captureValues : List Value) (captureEnv : Environment)
    (functionBinding : CoreEval.lookup env checked.functionName = some (.location address))
    (wantedBinding : CoreEval.lookup env checked.wantedName = some wanted)
    (tailBinding : CoreEval.lookup env checked.tailName = some tail)
    (entryBinding : CoreEval.lookup env checked.entryName = some entry)
    (resolution : Resolve start address resolved)
    (functionCell : readCell start resolved = some (.closureCode code :: captureValues))
    (closureShape : program code = some (.closure context captureNodes storage parameter body))
    (captureBindings : CaptureBindings program captureNodes captureValues captureEnv)
    (bounded : BoundedLocations start) (wantedRep : Ident c start wanted queryId)
    (tailRep : Children c start tail entries) (keys : Store → Prop) (tailKeys : keys start)
    (keysRetained : ∀ before after, after.aliases = before.aliases →
      (∀ location old, readCell before location = some old → readCell after location = some old) →
      keys before → keys after)
    (ih : ∀ afterArgument recursiveFinish payload recursiveResult,
      Resolve afterArgument payload payload → readCell afterArgument payload = some [wanted, tail] →
      BoundedLocations afterArgument → Ident c afterArgument wanted queryId →
      Children c afterArgument tail entries → keys afterArgument →
      afterArgument.aliases = start.aliases →
      (∀ location old, readCell start location = some old → readCell afterArgument location = some old) →
      Eval program (extend captureEnv.reverse parameter (.location payload)) body
        afterArgument recursiveResult recursiveFinish →
      RemovalOutcome c afterArgument recursiveFinish recursiveResult
        (Ash.NetworkLedger.remove key queryId entries).1 (Ash.NetworkLedger.remove key queryId entries).2)
    (evaluation : Eval program env checked.node start result finish) :
    RemovalOutcome c start finish result
      (entry :: (Ash.NetworkLedger.remove key queryId entries).1)
      (Ash.NetworkLedger.remove key queryId entries).2 := by
  obtain ⟨afterCall, recursiveResult, chosen, bindings, recursiveEval, selected, resultEval⟩ :=
    case_match_inversion checked.branchShape evaluation
  obtain ⟨afterArgument, payload, bodyEval, payloadResolution, payloadCell, argumentProgress,
    argumentAliases, argumentBound, argumentRetained⟩ :=
    checked_recursive_call program checked.recursiveCall checked.recursiveFunction checked.recursiveArgument
      checked.wantedNode checked.tailNode env start afterCall recursiveResult wanted tail checked.functionName
      checked.wantedName checked.tailName address resolved code context storage parameter body captureNodes captureValues
      captureEnv checked.recursivePair checked.recursiveCallShape checked.recursiveFunctionShape functionBinding
      resolution functionCell closureShape captureBindings checked.wantedShape checked.tailShape
      checked.recursiveWantedFresh checked.recursiveTailFresh wantedBinding tailBinding bounded recursiveEval
  have wantedAfter := ident_retained c start afterArgument wanted queryId argumentAliases argumentRetained wantedRep
  have tailAfter := children_retained c start afterArgument tail entries argumentAliases argumentRetained tailRep
  have keysAfter := keysRetained start afterArgument argumentAliases argumentRetained tailKeys
  obtain ⟨remaining, status, recursiveRep, remainingRep, statusRep, recursiveProgress,
    recursiveAliases, recursiveBound, recursiveRetained⟩ :=
    ih afterArgument afterCall payload recursiveResult payloadResolution payloadCell argumentBound wantedAfter
      tailAfter keysAfter argumentAliases argumentRetained bodyEval
  obtain ⟨remainingAddress, remainingEq⟩ := children_is_location c afterCall remaining _ remainingRep
  have plain : tupleFields [remaining, status] = some [remaining, status] := by rw [remainingEq]; rfl
  cases recursiveRep with
  | pair resultAddress resultResolved _ _ resultResolution resultCell =>
    obtain ⟨sameBody, sameBindings⟩ := pair_selects_single afterCall resultAddress resultResolved remaining status
      checked.remainingName checked.statusName checked.resultBody resultResolution resultCell plain selected
    subst chosen
    subst bindings
    have entryBound : CoreEval.lookup
        ([(checked.remainingName, remaining), (checked.statusName, status)].reverse ++ env) checked.entryName =
        some entry := by
      change CoreEval.lookup (extend (extend env checked.remainingName remaining) checked.statusName status)
        checked.entryName = some entry
      rw [lookup_extended_value_other _ checked.statusName checked.entryName status checked.entryStatusDistinct]
      rw [lookup_extended_value_other _ checked.remainingName checked.entryName remaining checked.entryRemainingDistinct]
      exact entryBinding
    have remainingBound : CoreEval.lookup
        ([(checked.remainingName, remaining), (checked.statusName, status)].reverse ++ env) checked.remainingName =
        some remaining := by simp [CoreEval.lookup, Ne.symm checked.remainingStatusDistinct]
    have statusBound : CoreEval.lookup
        ([(checked.remainingName, remaining), (checked.statusName, status)].reverse ++ env) checked.statusName =
        some status := by simp [CoreEval.lookup]
    obtain ⟨rebuilt, outputRep, rebuiltRep, rebuildProgress, rebuildAliases, finishBound, rebuildRetained⟩ :=
      checked_rebuilt_status_result c program checked.resultBody checked.rebuild checked.statusNode
        checked.constructorFunction checked.constructorArgument checked.entryNode checked.remainingNode checked.operand
        checked.constructorClosure checked.constructorPair checked.constructorBody checked.resultPair _ afterCall finish
        result entry remaining status _ checked.entryName checked.remainingName checked.statusName checked.rebuildShape
        checked.entryShape checked.remainingShape checked.statusShape checked.constructorEntryFresh
        checked.constructorRemainingFresh checked.resultEntryFresh checked.resultRemainingFresh checked.resultStatusFresh
        entryBound remainingBound statusBound checked.operandShape checked.constructorOperandFresh recursiveBound
        remainingRep resultEval
    have aliasesFinal : finish.aliases = start.aliases :=
      rebuildAliases.trans (recursiveAliases.trans argumentAliases)
    have allRetained : ∀ location old, readCell start location = some old → readCell finish location = some old := by
      intro location old read
      exact rebuildRetained location old (recursiveRetained location old (argumentRetained location old read))
    have progress : start.nextLocation < finish.nextLocation := by omega
    exact ⟨rebuilt, status, outputRep, rebuiltRep,
      status_retained c afterCall finish status _ rebuildAliases rebuildRetained statusRep,
      progress, aliasesFinal, finishBound, allRetained⟩

/-- Empty evaluation satisfies the same outcome used by the recursive induction. -/
theorem removal_empty_outcome (c : Constructors) (program : Program) (env : Environment)
    (node scrutinee emptyBody moreBody emptyNode missingNode : NodeId)
    (binder entryName tailName : Binder) (start finish : Store) (list result : Value)
    (shape : program node = some (.caseMatch scrutinee
      [(.constructor c.empty none, emptyBody),
       (.constructor c.more (some (.tuple [.binder entryName, .binder tailName])), moreBody)]))
    (variableShape : program scrutinee = some (.variable binder))
    (binding : CoreEval.lookup env binder = some list)
    (pair : CheckedTuple program emptyBody none [emptyNode, missingNode])
    (empty : CheckedTuple program emptyNode (some c.empty) [])
    (missing : CheckedTuple program missingNode (some c.missing) [])
    (bounded : BoundedLocations start) (representation : Children c start list [])
    (evaluation : Eval program env node start result finish) :
    RemovalOutcome c start finish result [] .missing := by
  obtain ⟨listAddress, statusAddress, resultRep, listRep, statusResolution, statusCell,
    progress, aliasesSame, finalBound, retained⟩ :=
    removal_empty_returns c program env node scrutinee emptyBody moreBody emptyNode missingNode
      binder entryName tailName start finish list result shape variableShape binding pair empty missing bounded
      representation evaluation
  exact ⟨.location listAddress, .location statusAddress, resultRep, listRep,
    StatusRepresentation.missing statusAddress statusAddress statusResolution statusCell,
    progress, aliasesSame, finalBound, retained⟩

/-- A matching child satisfies the same outcome used by the recursive induction. -/
theorem removal_hit_outcome (c : Constructors) (program : Program)
    (branch trueBody falseBody call function argument projection wantedNode : NodeId)
    (comparator : ComparatorFunction c program) (projectionShape : ProjectionCallShape program projection)
    (callerEnv : Environment) (start finish : Store) (result wanted : Value)
    (wantedId keyId : Id) (functionName wantedName : Binder)
    (checkedArgument : CheckedTuple program argument none [projection, wantedNode])
    (comparatorAddress comparatorResolved projectionAddress projectionResolved : Nat)
    (entryAddress entryResolved payload tuple keyAddress : Nat) (destination : Value)
    (callShape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable functionName))
    (functionBinding : CoreEval.lookup callerEnv functionName = some (.location comparatorAddress))
    (comparatorResolution : Resolve start comparatorAddress comparatorResolved)
    (comparatorCell : readCell start comparatorResolved = some [.closureCode comparator.code])
    (projectionFresh : projectionShape.functionName ≠ checkedArgument.contextBinder)
    (entryFresh : projectionShape.entryName ≠ checkedArgument.contextBinder)
    (wantedFresh : wantedName ≠ checkedArgument.contextBinder)
    (wantedShape : program wantedNode = some (.variable wantedName))
    (projectionBinding : CoreEval.lookup callerEnv projectionShape.functionName = some (.location projectionAddress))
    (entryBinding : CoreEval.lookup callerEnv projectionShape.entryName = some (.location entryAddress))
    (wantedBinding : CoreEval.lookup callerEnv wantedName = some wanted)
    (projectionResolution : Resolve start projectionAddress projectionResolved)
    (projectionCell : readCell start projectionResolved = some [.closureCode projectionShape.code])
    (entryResolution : Resolve start entryAddress entryResolved)
    (entryCell : readCell start entryResolved = some [.tag projectionShape.child, .location payload])
    (payloadResolution : Resolve start payload tuple)
    (entryFields : readCell start tuple = some [.location keyAddress, destination])
    (bounded : BoundedLocations start)
    (keyRepresentation : Ident c start (.location keyAddress) keyId)
    (wantedRepresentation : Ident c start wanted wantedId)
    (branchShape : program branch = some (.caseMatch call
      [(.boolean true, trueBody), (.boolean false, falseBody)]))
    (tailNode foundNode : NodeId) (tailName : Binder) (tail : Value) (entries : List Value)
    (hitPair : CheckedTuple program trueBody none [tailNode, foundNode])
    (found : CheckedTuple program foundNode (some c.found) [])
    (tailShape : program tailNode = some (.variable tailName))
    (tailFresh : tailName ≠ hitPair.contextBinder)
    (tailBinding : CoreEval.lookup callerEnv tailName = some tail)
    (tailRepresentation : Children c start tail entries)
    (sameKey : keyId = wantedId)
    (evaluation : Eval program callerEnv branch start result finish) :
    RemovalOutcome c start finish result entries .found := by
  obtain ⟨statusAddress, resultRep, statusResolution, statusCell, tailRep, progress,
    aliasesSame, finalBound, retained⟩ :=
    removal_hit_returns_tail c program branch trueBody falseBody call function argument projection wantedNode
      comparator projectionShape callerEnv start finish result wanted wantedId keyId functionName wantedName checkedArgument
      comparatorAddress comparatorResolved projectionAddress projectionResolved entryAddress entryResolved payload tuple
      keyAddress destination callShape functionShape functionBinding comparatorResolution comparatorCell projectionFresh
      entryFresh wantedFresh wantedShape projectionBinding entryBinding wantedBinding projectionResolution projectionCell
      entryResolution entryCell payloadResolution entryFields bounded keyRepresentation wantedRepresentation branchShape
      tailNode foundNode tailName tail entries hitPair found tailShape tailFresh tailBinding tailRepresentation sameKey evaluation
  exact ⟨tail, .location statusAddress, resultRep, tailRep,
    StatusRepresentation.found statusAddress statusAddress statusResolution statusCell,
    progress, aliasesSame, finalBound, retained⟩

/-- One checked recursive removal definition, including all branch links and helper bodies. -/
structure CheckedRemovalBase (c : Constructors) (program : Program) where
  code : NodeId
  context : NodeId
  storage : NodeId
  captureNodes : List NodeId
  parameter : Binder
  body : NodeId
  argumentScrutinee : NodeId
  listBody : NodeId
  listScrutinee : NodeId
  emptyBody : NodeId
  emptyNode : NodeId
  missingNode : NodeId
  moreBody : NodeId
  hitBody : NodeId
  tailNode : NodeId
  foundNode : NodeId
  comparisonCall : NodeId
  comparisonFunction : NodeId
  comparisonArgument : NodeId
  projection : NodeId
  wantedNode : NodeId
  listName : Binder
  comparisonName : Binder
  projectionName : Binder
  miss : CheckedMiss c program
  comparator : ComparatorFunction c program
  projectionCode : NodeId
  comparisonPair : CheckedTuple program comparisonArgument none [projection, wantedNode]
  emptyPair : CheckedTuple program emptyBody none [emptyNode, missingNode]
  emptyValue : CheckedTuple program emptyNode (some c.empty) []
  missingValue : CheckedTuple program missingNode (some c.missing) []
  hitPair : CheckedTuple program hitBody none [tailNode, foundNode]
  foundValue : CheckedTuple program foundNode (some c.found) []
  closureShape : program code = some (.closure context captureNodes storage parameter body)
  bodyShape : program body = some (.caseMatch argumentScrutinee
    [(.tuple [.binder miss.wantedName, .binder listName], listBody)])
  argumentShape : program argumentScrutinee = some (.variable parameter)
  listShape : program listBody = some (.caseMatch listScrutinee
    [(.constructor c.empty none, emptyBody),
     (.constructor c.more (some (.tuple [.binder miss.entryName, .binder miss.tailName])), moreBody)])
  listVariableShape : program listScrutinee = some (.variable listName)
  moreShape : program moreBody = some (.caseMatch comparisonCall
    [(.boolean true, hitBody), (.boolean false, miss.node)])
  callShape : program comparisonCall = some (.apply comparisonFunction comparisonArgument)
  comparisonShape : program comparisonFunction = some (.variable comparisonName)
  wantedShape : program wantedNode = some (.variable miss.wantedName)
  tailShape : program tailNode = some (.variable miss.tailName)
  projectionFresh : projectionName ≠ comparisonPair.contextBinder
  entryFresh : miss.entryName ≠ comparisonPair.contextBinder
  wantedFresh : miss.wantedName ≠ comparisonPair.contextBinder
  hitTailFresh : miss.tailName ≠ hitPair.contextBinder
  distinct : [parameter, miss.wantedName, listName, miss.entryName, miss.tailName,
    miss.functionName, comparisonName, projectionName].Nodup

/-- Child removal adds the exact linked Child projection to the shared shape. -/
structure CheckedRemoval (c : Constructors) (program : Program)
    extends CheckedRemovalBase c program where
  projectionShape : ProjectionCallShape program projection
  projectionFunctionName : projectionShape.functionName = projectionName
  projectionEntryName : projectionShape.entryName = miss.entryName
  projectionChild : projectionShape.child = c.child
  projectionCodeShape : projectionShape.code = projectionCode

/-- A More branch compares the actual head and recurses on its proper tail. -/
theorem removal_more_outcome_with (c : Constructors) (program : Program)
    (checked : CheckedRemovalBase c program) (env : Environment)
    (start finish : Store) (result wanted tail : Value) (entryAddress : Nat)
    (entries : List Value) (key : Value → Id) (queryId : Id)
    (selfAddress selfResolved comparisonAddress comparisonResolved keyAddress : Nat)
    (captureValues : List Value) (captureEnv : Environment)
    (selfBinding : CoreEval.lookup env checked.miss.functionName = some (.location selfAddress))
    (comparisonBinding : CoreEval.lookup env checked.comparisonName = some (.location comparisonAddress))
    (entryBinding : CoreEval.lookup env checked.miss.entryName = some (.location entryAddress))
    (wantedBinding : CoreEval.lookup env checked.miss.wantedName = some wanted)
    (tailBinding : CoreEval.lookup env checked.miss.tailName = some tail)
    (selfResolution : Resolve start selfAddress selfResolved)
    (selfCell : readCell start selfResolved = some (.closureCode checked.code :: captureValues))
    (captureBindings : CaptureBindings program checked.captureNodes captureValues captureEnv)
    (comparisonResolution : Resolve start comparisonAddress comparisonResolved)
    (comparisonCell : readCell start comparisonResolved = some [.closureCode checked.comparator.code])
    (projectionLaw : ProjectionAfterQuery program checked.projection env checked.comparisonPair.contextBinder start keyAddress)
    (keyRep : Ident c start (.location keyAddress) (key (.location entryAddress)))
    (wantedRep : Ident c start wanted queryId)
    (tailRep : Children c start tail entries) (keys : Store → Prop) (tailKeys : keys start)
    (keysRetained : ∀ before after, after.aliases = before.aliases →
      (∀ location old, readCell before location = some old → readCell after location = some old) →
      keys before → keys after)
    (bounded : BoundedLocations start)
    (ih : ∀ afterArgument recursiveFinish payload recursiveResult,
      Resolve afterArgument payload payload → readCell afterArgument payload = some [wanted, tail] →
      BoundedLocations afterArgument → Ident c afterArgument wanted queryId →
      Children c afterArgument tail entries → keys afterArgument →
      afterArgument.aliases = start.aliases →
      (∀ location old, readCell start location = some old → readCell afterArgument location = some old) →
      Eval program (extend captureEnv.reverse checked.parameter (.location payload)) checked.body
        afterArgument recursiveResult recursiveFinish →
      RemovalOutcome c afterArgument recursiveFinish recursiveResult
        (Ash.NetworkLedger.remove key queryId entries).1 (Ash.NetworkLedger.remove key queryId entries).2)
    (evaluation : Eval program env checked.moreBody start result finish) :
    RemovalOutcome c start finish result
      (Ash.NetworkLedger.remove key queryId (.location entryAddress :: entries)).1
      (Ash.NetworkLedger.remove key queryId (.location entryAddress :: entries)).2 := by
  obtain ⟨middle, selectedEval, comparisonProgress, comparisonAliases, comparisonBound, comparisonRetained⟩ :=
    comparison_selects_with c program checked.moreBody checked.hitBody checked.miss.node
      checked.comparisonCall checked.comparisonFunction checked.comparisonArgument checked.projection checked.wantedNode
      checked.comparator env start finish result wanted queryId (key (.location entryAddress))
      checked.comparisonName checked.miss.wantedName checked.comparisonPair comparisonAddress comparisonResolved
      keyAddress checked.callShape checked.comparisonShape comparisonBinding comparisonResolution
      comparisonCell checked.wantedFresh checked.wantedShape wantedBinding projectionLaw bounded keyRep wantedRep
      checked.moreShape evaluation
  by_cases equal : key (.location entryAddress) = queryId
  · have comparisonTrue : Ash.NetworkLedger.CoreRemoval.compareId (key (.location entryAddress)) queryId = true :=
      (Ash.NetworkLedger.CoreRemoval.compareId_correct _ _).mpr equal
    simp only [comparisonTrue] at selectedEval
    obtain ⟨_, statusAddress, _, resultRep, statusResolution, statusCell, hitProgress, hitAliases,
      finishBound, hitRetained⟩ :=
      checked_tail_status_result checked.hitPair checked.foundValue checked.miss.tailName checked.tailShape
        checked.hitTailFresh tailBinding comparisonBound selectedEval
    have aliasesFinal : finish.aliases = start.aliases := hitAliases.trans comparisonAliases
    have retainedFinal : ∀ location old, readCell start location = some old → readCell finish location = some old := by
      intro location old read
      exact hitRetained location old (comparisonRetained location old read)
    have outcome : RemovalOutcome c start finish result entries .found :=
      ⟨tail, .location statusAddress, resultRep,
        children_retained c start finish tail entries aliasesFinal retainedFinal tailRep,
        StatusRepresentation.found statusAddress statusAddress statusResolution statusCell,
        Nat.lt_trans comparisonProgress hitProgress, aliasesFinal, finishBound, retainedFinal⟩
    simpa [Ash.NetworkLedger.remove, equal] using outcome
  · have comparisonFalse : Ash.NetworkLedger.CoreRemoval.compareId (key (.location entryAddress)) queryId = false := by
      cases compared : Ash.NetworkLedger.CoreRemoval.compareId (key (.location entryAddress)) queryId with
      | false => rfl
      | true => exact False.elim (equal ((Ash.NetworkLedger.CoreRemoval.compareId_correct _ _).mp compared))
    simp only [comparisonFalse] at selectedEval
    have selfResolution' := resolve_preserved comparisonAliases comparisonRetained selfResolution
    have selfCell' := comparisonRetained selfResolved _ selfCell
    have wantedRep' := ident_retained c start middle wanted queryId comparisonAliases comparisonRetained wantedRep
    have tailRep' := children_retained c start middle tail entries comparisonAliases comparisonRetained tailRep
    have tailKeys' := keysRetained start middle comparisonAliases comparisonRetained tailKeys
    have tailIH : ∀ afterArgument recursiveFinish payload recursiveResult,
      Resolve afterArgument payload payload → readCell afterArgument payload = some [wanted, tail] →
      BoundedLocations afterArgument → Ident c afterArgument wanted queryId →
      Children c afterArgument tail entries → keys afterArgument →
      afterArgument.aliases = middle.aliases →
      (∀ location old, readCell middle location = some old → readCell afterArgument location = some old) →
      Eval program (extend captureEnv.reverse checked.parameter (.location payload)) checked.body
        afterArgument recursiveResult recursiveFinish →
      RemovalOutcome c afterArgument recursiveFinish recursiveResult
        (Ash.NetworkLedger.remove key queryId entries).1 (Ash.NetworkLedger.remove key queryId entries).2 := by
      intro afterArgument recursiveFinish recPayload recursiveResult recResolution recCell recBound recWanted recTail recKeys
        recAliases recRetained recEval
      apply ih afterArgument recursiveFinish recPayload recursiveResult recResolution recCell recBound recWanted recTail recKeys
        (recAliases.trans comparisonAliases) _ recEval
      intro location old read
      exact recRetained location old (comparisonRetained location old read)
    obtain ⟨listValue, statusValue, resultRep, listRep, statusRep, missProgress, missAliases,
      finishBound, missRetained⟩ :=
      removal_miss_step_with c program checked.miss env middle finish result (.location entryAddress) wanted tail entries key
        queryId selfAddress selfResolved checked.code checked.context checked.storage checked.parameter checked.body
        checked.captureNodes captureValues captureEnv selfBinding wantedBinding tailBinding entryBinding selfResolution'
        selfCell' checked.closureShape captureBindings comparisonBound wantedRep' tailRep' keys tailKeys' keysRetained tailIH selectedEval
    have aliasesFinal : finish.aliases = start.aliases := missAliases.trans comparisonAliases
    have retainedFinal : ∀ location old, readCell start location = some old → readCell finish location = some old := by
      intro location old read
      exact missRetained location old (comparisonRetained location old read)
    have outcome : RemovalOutcome c start finish result
        (.location entryAddress :: (Ash.NetworkLedger.remove key queryId entries).1)
        (Ash.NetworkLedger.remove key queryId entries).2 :=
      ⟨listValue, statusValue, resultRep, listRep, statusRep, Nat.lt_trans comparisonProgress missProgress,
        aliasesFinal, finishBound, retainedFinal⟩
    simpa [Ash.NetworkLedger.remove, equal] using outcome

/-- The removal function destructures the actual stored wanted/list argument. -/
theorem removal_argument_executes (c : Constructors) (program : Program) (checked : CheckedRemovalBase c program)
    (captures : Environment) (start finish : Store) (payload payloadResolved : Nat)
    (wanted list result : Value) (queryId : Id)
    (resolution : Resolve start payload payloadResolved)
    (cell : readCell start payloadResolved = some [wanted, list])
    (wantedRep : Ident c start wanted queryId)
    (evaluation : Eval program (extend captures checked.parameter (.location payload)) checked.body start result finish) :
    Eval program
      ([(checked.miss.wantedName, wanted), (checked.listName, list)].reverse ++
        extend captures checked.parameter (.location payload)) checked.listBody start result finish := by
  obtain ⟨middle, actual, chosen, bindings, argumentEval, selected, bodyEval⟩ :=
    case_match_inversion checked.bodyShape evaluation
  obtain ⟨actualBinding, sameStore⟩ := variable_inversion checked.argumentShape argumentEval
  have sameValue : actual = .location payload := by simpa [CoreEval.lookup, extend] using actualBinding.symm
  subst actual
  subst middle
  obtain ⟨wantedAddress, wantedEq⟩ := ident_is_location c start wanted queryId wantedRep
  have plain : tupleFields [wanted, list] = some [wanted, list] := by rw [wantedEq]; rfl
  obtain ⟨sameBody, sameBindings⟩ := pair_selects_single start payload payloadResolved wanted list
    checked.miss.wantedName checked.listName checked.listBody resolution cell plain selected
  subst chosen
  subst bindings
  exact bodyEval

/-- A prefix that does not bind a name cannot shadow its captured value. -/
theorem lookup_unshadowed_prefix (bindings env : Environment) (name : Binder)
    (absent : name ∉ bindings.map Prod.fst) :
    CoreEval.lookup (bindings ++ env) name = CoreEval.lookup env name := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
    rcases binding with ⟨bound, value⟩
    have different : name ≠ bound := by
      intro same
      apply absent
      simp [same]
    have absentRest : name ∉ rest.map Prod.fst := by
      intro member
      apply absent
      simp [member]
    change CoreEval.lookup (extend (rest ++ env) bound value) name = CoreEval.lookup env name
    rw [lookup_extended_value_other _ bound name value different]
    exact ih absentRest

/-- Distinct checked binders keep helper captures and branch operands in scope. -/
theorem removal_environment_bindings (c : Constructors) (program : Program) (checked : CheckedRemovalBase c program)
    (captures : Environment) (payload wanted list entry tail self comparison projection : Value)
    (selfBinding : CoreEval.lookup captures checked.miss.functionName = some self)
    (comparisonBinding : CoreEval.lookup captures checked.comparisonName = some comparison)
    (projectionBinding : CoreEval.lookup captures checked.projectionName = some projection) :
    let arguments := [(checked.listName, list), (checked.miss.wantedName, wanted), (checked.parameter, payload)] ++ captures
    let more := [(checked.miss.tailName, tail), (checked.miss.entryName, entry)] ++ arguments
    CoreEval.lookup arguments checked.listName = some list ∧
    CoreEval.lookup more checked.miss.wantedName = some wanted ∧
    CoreEval.lookup more checked.miss.entryName = some entry ∧
    CoreEval.lookup more checked.miss.tailName = some tail ∧
    CoreEval.lookup more checked.miss.functionName = some self ∧
    CoreEval.lookup more checked.comparisonName = some comparison ∧
    CoreEval.lookup more checked.projectionName = some projection := by
  have distinct := checked.distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_false_eq_true, not_or] at distinct
  rcases distinct with ⟨⟨hpw, hpl, hpe, hpt, hps, hpc, hpp⟩,
    ⟨hwl, hwe, hwt, hws, hwc, hwp⟩, ⟨hle, hlt, hls, hlc, hlp⟩,
    ⟨het, hes, hec, hep⟩, ⟨hts, htc, htp⟩, ⟨hsc, hsp⟩, hcp⟩
  have selfAbsent : checked.miss.functionName ∉
      [checked.miss.tailName, checked.miss.entryName, checked.listName, checked.miss.wantedName, checked.parameter] := by
    simp [Ne.symm hts, Ne.symm hes, Ne.symm hls, Ne.symm hws, Ne.symm hps]
  have comparisonAbsent : checked.comparisonName ∉
      [checked.miss.tailName, checked.miss.entryName, checked.listName, checked.miss.wantedName, checked.parameter] := by
    simp [Ne.symm htc, Ne.symm hec, Ne.symm hlc, Ne.symm hwc, Ne.symm hpc]
  have projectionAbsent : checked.projectionName ∉
      [checked.miss.tailName, checked.miss.entryName, checked.listName, checked.miss.wantedName, checked.parameter] := by
    simp [Ne.symm htp, Ne.symm hep, Ne.symm hlp, Ne.symm hwp, Ne.symm hpp]
  have wantedAbsent : checked.miss.wantedName ∉
      [checked.miss.tailName, checked.miss.entryName, checked.listName] := by simp [hwt, hwe, hwl]
  have entryAbsent : checked.miss.entryName ∉ [checked.miss.tailName] := by simp [het]
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [CoreEval.lookup]
  · have same := lookup_unshadowed_prefix
      [(checked.miss.tailName, tail), (checked.miss.entryName, entry), (checked.listName, list)]
      ([(checked.miss.wantedName, wanted), (checked.parameter, payload)] ++ captures) checked.miss.wantedName (by simpa using wantedAbsent)
    simpa [CoreEval.lookup] using same
  · have same := lookup_unshadowed_prefix [(checked.miss.tailName, tail)]
      ([(checked.miss.entryName, entry), (checked.listName, list), (checked.miss.wantedName, wanted), (checked.parameter, payload)] ++ captures)
      checked.miss.entryName (by simpa using entryAbsent)
    simpa [CoreEval.lookup] using same
  · simp [CoreEval.lookup]
  · have same := lookup_unshadowed_prefix
      [(checked.miss.tailName, tail), (checked.miss.entryName, entry), (checked.listName, list),
       (checked.miss.wantedName, wanted), (checked.parameter, payload)] captures checked.miss.functionName (by simpa using selfAbsent)
    exact same.trans selfBinding
  · have same := lookup_unshadowed_prefix
      [(checked.miss.tailName, tail), (checked.miss.entryName, entry), (checked.listName, list),
       (checked.miss.wantedName, wanted), (checked.parameter, payload)] captures checked.comparisonName (by simpa using comparisonAbsent)
    exact same.trans comparisonBinding
  · have same := lookup_unshadowed_prefix
      [(checked.miss.tailName, tail), (checked.miss.entryName, entry), (checked.listName, list),
       (checked.miss.wantedName, wanted), (checked.parameter, payload)] captures checked.projectionName (by simpa using projectionAbsent)
    exact same.trans projectionBinding

/-- Finite entries with their whole represented value and exact projected ID. -/
def RemovalRepresentedEntries (c : Constructors) (R : Store → Value → Nat → Prop)
    (store : Store) (key : Value → Id) (entries : List Value) : Prop :=
  ∀ entry ∈ entries, ∃ address keyAddress,
    entry = .location address ∧ R store entry keyAddress ∧
      Ident c store (.location keyAddress) (key entry)

theorem removal_represented_entries_retained (c : Constructors) (R : Store → Value → Nat → Prop)
    (before after : Store) (key : Value → Id) (entries : List Value)
    (relationRetained : ∀ before after entry keyAddress,
      after.aliases = before.aliases →
      (∀ location old, readCell before location = some old → readCell after location = some old) →
      R before entry keyAddress → R after entry keyAddress)
    (aliases : after.aliases = before.aliases)
    (cells : ∀ location old, readCell before location = some old → readCell after location = some old)
    (representation : RemovalRepresentedEntries c R before key entries) :
    RemovalRepresentedEntries c R after key entries := by
  intro entry member
  obtain ⟨address, keyAddress, same, entryRep, keyRep⟩ := representation entry member
  exact ⟨address, keyAddress, same, relationRetained before after entry keyAddress aliases cells entryRep,
    ident_retained c before after (.location keyAddress) (key entry) aliases cells keyRep⟩

/-- Every normal execution of the checked finite removal body removes the first match. -/
theorem removal_body_correct_with (c : Constructors) (program : Program)
    (checked : CheckedRemovalBase c program) (R : Store → Value → Nat → Prop)
    (relationRetained : ∀ before after entry keyAddress,
      after.aliases = before.aliases →
      (∀ location old, readCell before location = some old → readCell after location = some old) →
      R before entry keyAddress → R after entry keyAddress)
    (captureValues : List Value) (captureEnv : Environment)
    (selfAddress selfResolved comparisonAddress comparisonResolved projectionAddress projectionResolved : Nat)
    (wanted : Value) (queryId : Id) (key : Value → Id) (entries : List Value)
    (selfBinding : CoreEval.lookup captureEnv.reverse checked.miss.functionName = some (.location selfAddress))
    (comparisonBinding : CoreEval.lookup captureEnv.reverse checked.comparisonName = some (.location comparisonAddress))
    (projectionBinding : CoreEval.lookup captureEnv.reverse checked.projectionName = some (.location projectionAddress))
    (captureBindings : CaptureBindings program checked.captureNodes captureValues captureEnv)
    (projectionFor : ∀ env start entryAddress keyAddress,
      R start (.location entryAddress) keyAddress →
      CoreEval.lookup env checked.projectionName = some (.location projectionAddress) →
      CoreEval.lookup env checked.miss.entryName = some (.location entryAddress) →
      Resolve start projectionAddress projectionResolved →
      readCell start projectionResolved = some [.closureCode checked.projectionCode] →
      ProjectionAfterQuery program checked.projection env checked.comparisonPair.contextBinder start keyAddress) :
    ∀ start finish payload payloadResolved list result,
      Resolve start payload payloadResolved → readCell start payloadResolved = some [wanted, list] →
      BoundedLocations start → Ident c start wanted queryId → Children c start list entries →
      RemovalRepresentedEntries c R start key entries →
      Resolve start selfAddress selfResolved →
      readCell start selfResolved = some (.closureCode checked.code :: captureValues) →
      Resolve start comparisonAddress comparisonResolved →
      readCell start comparisonResolved = some [.closureCode checked.comparator.code] →
      Resolve start projectionAddress projectionResolved →
      readCell start projectionResolved = some [.closureCode checked.projectionCode] →
      Eval program (extend captureEnv.reverse checked.parameter (.location payload)) checked.body start result finish →
      RemovalOutcome c start finish result (Ash.NetworkLedger.remove key queryId entries).1
        (Ash.NetworkLedger.remove key queryId entries).2 := by
  induction entries with
  | nil =>
    intro start finish payload payloadResolved list result payloadResolution payloadCell bounded wantedRep listRep keys
      selfResolution selfCell comparisonResolution comparisonCell projectionResolution projectionCell evaluation
    have listEval := removal_argument_executes c program checked captureEnv.reverse start finish payload payloadResolved
      wanted list result queryId payloadResolution payloadCell wantedRep evaluation
    have scope := removal_environment_bindings c program checked captureEnv.reverse (.location payload) wanted list
      .unit .unit (.location selfAddress) (.location comparisonAddress) (.location projectionAddress)
      selfBinding comparisonBinding projectionBinding
    exact removal_empty_outcome c program _ checked.listBody checked.listScrutinee checked.emptyBody checked.moreBody
      checked.emptyNode checked.missingNode checked.listName checked.miss.entryName checked.miss.tailName
      start finish list result checked.listShape checked.listVariableShape scope.1 checked.emptyPair checked.emptyValue
      checked.missingValue bounded listRep listEval
  | cons entry entries ih =>
    intro start finish payload payloadResolved list result payloadResolution payloadCell bounded wantedRep listRep keys
      selfResolution selfCell comparisonResolution comparisonCell projectionResolution projectionCell evaluation
    have listEval := removal_argument_executes c program checked captureEnv.reverse start finish payload payloadResolved
      wanted list result queryId payloadResolution payloadCell wantedRep evaluation
    obtain ⟨entryAddress, keyAddress, entryEq, entryRep, keyRep⟩ := keys entry (by simp)
    subst entry
    cases listRep with
    | more listAddress listResolved listPayload listTuple _ tail _ listResolution listCell listPayloadResolution listFields tailRep =>
      have scope := removal_environment_bindings c program checked captureEnv.reverse (.location payload) wanted (.location listAddress)
        (.location entryAddress) tail (.location selfAddress) (.location comparisonAddress) (.location projectionAddress)
        selfBinding comparisonBinding projectionBinding
      have moreEval := more_match_executes_second program start finish _ checked.listBody checked.listScrutinee
        checked.listName c.empty c.more checked.emptyBody checked.moreBody checked.miss.entryName checked.miss.tailName
        listAddress listResolved listPayload listTuple entryAddress tail result checked.listShape checked.listVariableShape
        scope.1 listResolution listCell listPayloadResolution listFields listEval
      have tailKeys : RemovalRepresentedEntries c R start key entries := by
        intro other member
        exact keys other (by simp [member])
      have tailIH : ∀ afterArgument recursiveFinish recPayload recursiveResult,
        Resolve afterArgument recPayload recPayload → readCell afterArgument recPayload = some [wanted, tail] →
        BoundedLocations afterArgument → Ident c afterArgument wanted queryId →
        Children c afterArgument tail entries → RemovalRepresentedEntries c R afterArgument key entries →
        afterArgument.aliases = start.aliases →
        (∀ location old, readCell start location = some old → readCell afterArgument location = some old) →
        Eval program (extend captureEnv.reverse checked.parameter (.location recPayload)) checked.body
          afterArgument recursiveResult recursiveFinish →
        RemovalOutcome c afterArgument recursiveFinish recursiveResult
          (Ash.NetworkLedger.remove key queryId entries).1 (Ash.NetworkLedger.remove key queryId entries).2 := by
        intro afterArgument recursiveFinish recPayload recursiveResult recResolution recCell recBound recWanted recTail recKeys
          recAliases recRetained recEval
        apply ih afterArgument recursiveFinish recPayload recPayload tail recursiveResult recResolution recCell recBound
          recWanted recTail recKeys (resolve_preserved recAliases recRetained selfResolution)
          (recRetained selfResolved _ selfCell) (resolve_preserved recAliases recRetained comparisonResolution)
          (recRetained comparisonResolved _ comparisonCell) (resolve_preserved recAliases recRetained projectionResolution)
          (recRetained projectionResolved _ projectionCell) recEval
      have law := projectionFor _ start entryAddress keyAddress entryRep scope.2.2.2.2.2.2 scope.2.2.1
        projectionResolution projectionCell
      exact removal_more_outcome_with c program checked _ start finish result wanted tail entryAddress entries key
        queryId selfAddress selfResolved comparisonAddress comparisonResolved keyAddress captureValues captureEnv
        scope.2.2.2.2.1 scope.2.2.2.2.2.1 scope.2.2.1 scope.2.1 scope.2.2.2.1
        selfResolution selfCell captureBindings comparisonResolution comparisonCell law keyRep wantedRep tailRep
        (fun store => RemovalRepresentedEntries c R store key entries) tailKeys
        (fun before after aliases cells reps => removal_represented_entries_retained c R before after key entries
          relationRetained aliases cells reps) bounded tailIH moreEval

def RemovalChildEntry (c : Constructors) (store : Store) (entry : Value) (keyAddress : Nat) : Prop :=
  ∃ destination, Entry c store entry (.location keyAddress) destination

theorem removal_child_entry_retained (c : Constructors) (before after : Store) (entry : Value) (keyAddress : Nat)
    (aliases : after.aliases = before.aliases)
    (cells : ∀ location old, readCell before location = some old → readCell after location = some old)
    (entryRep : RemovalChildEntry c before entry keyAddress) : RemovalChildEntry c after entry keyAddress := by
  obtain ⟨destination, represented⟩ := entryRep
  exact ⟨destination, entry_retained c before after entry (.location keyAddress) destination aliases cells represented⟩

/-- Every normal execution of the checked removal body agrees with finite whole-entry removal. -/
theorem removal_body_correct (c : Constructors) (program : Program) (checked : CheckedRemoval c program)
    (captureValues : List Value) (captureEnv : Environment)
    (selfAddress selfResolved comparisonAddress comparisonResolved projectionAddress projectionResolved : Nat)
    (wanted : Value) (queryId : Id) (key : Value → Id) (entries : List Value)
    (selfBinding : CoreEval.lookup captureEnv.reverse checked.miss.functionName = some (.location selfAddress))
    (comparisonBinding : CoreEval.lookup captureEnv.reverse checked.comparisonName = some (.location comparisonAddress))
    (projectionBinding : CoreEval.lookup captureEnv.reverse checked.projectionName = some (.location projectionAddress))
    (captureBindings : CaptureBindings program checked.captureNodes captureValues captureEnv) :
    ∀ start finish payload payloadResolved list result,
      Resolve start payload payloadResolved → readCell start payloadResolved = some [wanted, list] →
      BoundedLocations start → Ident c start wanted queryId → Children c start list entries →
      KeyedEntries c start key entries →
      Resolve start selfAddress selfResolved →
      readCell start selfResolved = some (.closureCode checked.code :: captureValues) →
      Resolve start comparisonAddress comparisonResolved →
      readCell start comparisonResolved = some [.closureCode checked.comparator.code] →
      Resolve start projectionAddress projectionResolved →
      readCell start projectionResolved = some [.closureCode checked.projectionShape.code] →
      Eval program (extend captureEnv.reverse checked.parameter (.location payload)) checked.body start result finish →
      RemovalOutcome c start finish result (Ash.NetworkLedger.remove key queryId entries).1
        (Ash.NetworkLedger.remove key queryId entries).2 := by
  have projectionFor : ∀ env start entryAddress keyAddress,
      RemovalChildEntry c start (.location entryAddress) keyAddress →
      CoreEval.lookup env checked.projectionName = some (.location projectionAddress) →
      CoreEval.lookup env checked.miss.entryName = some (.location entryAddress) →
      Resolve start projectionAddress projectionResolved →
      readCell start projectionResolved = some [.closureCode checked.projectionCode] →
      ProjectionAfterQuery program checked.projection env checked.comparisonPair.contextBinder start keyAddress := by
    intro env start entryAddress keyAddress entryRep functionBinding entryBinding functionResolution functionCell
    obtain ⟨destination, represented⟩ := entryRep
    cases represented with
    | child address resolved payload tuple _ _ resolution cell payloadResolution fields =>
      have functionBound : CoreEval.lookup env checked.projectionShape.functionName = some (.location projectionAddress) := by
        simpa [checked.projectionFunctionName] using functionBinding
      have entryBound : CoreEval.lookup env checked.projectionShape.entryName = some (.location entryAddress) := by
        simpa [checked.projectionEntryName] using entryBinding
      have closureCell : readCell start projectionResolved = some [.closureCode checked.projectionShape.code] := by
        simpa [checked.projectionCodeShape] using functionCell
      have functionFresh : checked.projectionShape.functionName ≠ checked.comparisonPair.contextBinder := by
        simpa [checked.projectionFunctionName] using checked.projectionFresh
      have entryFresh : checked.projectionShape.entryName ≠ checked.comparisonPair.contextBinder := by
        simpa [checked.projectionEntryName] using checked.entryFresh
      intro queried middle actual queryStep evaluation
      have functionBound' : CoreEval.lookup (extend env checked.comparisonPair.contextBinder .context)
          checked.projectionShape.functionName = some (.location projectionAddress) := by
        rw [lookup_extended_other env checked.comparisonPair.contextBinder checked.projectionShape.functionName functionFresh]
        exact functionBound
      have entryBound' : CoreEval.lookup (extend env checked.comparisonPair.contextBinder .context)
          checked.projectionShape.entryName = some (.location entryAddress) := by
        rw [lookup_extended_other env checked.comparisonPair.contextBinder checked.projectionShape.entryName entryFresh]
        exact entryBound
      have childCell : readCell start resolved = some [.tag checked.projectionShape.child, .location payload] := by
        simpa [checked.projectionChild] using cell
      exact child_projection_call program queried middle (extend env checked.comparisonPair.contextBinder .context)
        checked.projection checked.projectionShape.function checked.projectionShape.argument checked.projectionShape.code
        checked.projectionShape.context checked.projectionShape.storage checked.projectionShape.parameter checked.projectionShape.body
        checked.projectionShape.scrutinee checked.projectionShape.returnKey checked.projectionShape.functionName
        checked.projectionShape.entryName checked.projectionShape.keyName checked.projectionShape.destinationName
        checked.projectionShape.child projectionAddress projectionResolved entryAddress resolved payload tuple keyAddress
        destination actual checked.projectionShape.callShape checked.projectionShape.functionShape
        checked.projectionShape.argumentShape functionBound' entryBound'
        (query_preserves_resolution queryStep functionResolution) (query_preserves_cell queryStep closureCell)
        checked.projectionShape.closureShape checked.projectionShape.distinct checked.projectionShape.bodyShape
        checked.projectionShape.scrutineeShape checked.projectionShape.returnShape
        (query_preserves_resolution queryStep resolution) (query_preserves_cell queryStep childCell)
        (query_preserves_resolution queryStep payloadResolution) (query_preserves_cell queryStep fields) evaluation
  intro start finish payload payloadResolved list result payloadResolution payloadCell bounded wantedRep listRep keys
    selfResolution selfCell comparisonResolution comparisonCell projectionResolution projectionCell evaluation
  have represented : RemovalRepresentedEntries c (RemovalChildEntry c) start key entries := by
    intro entry member
    obtain ⟨keyAddress, destination, entryRep, keyRep⟩ := keys entry member
    cases entryRep with
    | child address resolved entryPayload tuple _ _ resolution cell payloadResolution fields =>
      exact ⟨address, keyAddress, rfl, ⟨destination, Entry.child address resolved entryPayload tuple
        (.location keyAddress) destination resolution cell payloadResolution fields⟩, keyRep⟩
  have projectionCell' : readCell start projectionResolved = some [.closureCode checked.projectionCode] := by
    simpa [checked.projectionCodeShape] using projectionCell
  exact removal_body_correct_with c program checked.toCheckedRemovalBase (RemovalChildEntry c)
    (removal_child_entry_retained c) captureValues captureEnv selfAddress selfResolved comparisonAddress comparisonResolved
    projectionAddress projectionResolved wanted queryId key entries selfBinding comparisonBinding projectionBinding
    captureBindings projectionFor start finish payload payloadResolved list result payloadResolution payloadCell bounded
    wantedRep listRep represented selfResolution selfCell comparisonResolution comparisonCell projectionResolution
    projectionCell' evaluation



end Ash.NetworkLedger.CoreValues
