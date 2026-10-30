import NetworkLedgerCoreRecordLookup
import NetworkLedgerCoreInsert

/- The recursive Record update passes the actual wanted key, replacement and
   proper tail in that order. Finite input and linked capture/provider premises
   are established by the consuming call, not by this lemma. -/
namespace Ash.NetworkLedger.CoreRecordUpdate

open Ash.NetworkLedger.CoreRegion
open Ash.NetworkLedger.CoreEval
open Ash.NetworkLedger.CoreValues
open Ash.NetworkLedger.CoreLookup
open Ash.NetworkLedger.CoreInsert
open Ash.NetworkLedger

/-- A triple-pattern binds the exact original values in order. -/
theorem triple_binders_match (store : Store) (address resolved : Nat)
    (firstName secondName thirdName : Binder) (first second third : Value)
    (resolution : Resolve store address resolved)
    (cell : readCell store resolved = some [first, second, third])
    (plain : tupleFields [first, second, third] = some [first, second, third])
    {result : Option Environment}
    (attempt : Attempt store (.tuple [.binder firstName, .binder secondName, .binder thirdName])
      (.location address) result) :
    result = some [(firstName, first), (secondName, second), (thirdName, third)] := by
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
      | tailMiss _ _ _ _ bindings hit miss =>
        cases hit
        cases miss with
        | headMiss _ _ _ _ miss => cases miss
        | tailMiss _ _ _ _ bindings hit miss => cases hit; cases miss
    | hit _ _ _ _ firstBindings rest head tail =>
      cases head
      cases tail with
      | hit _ _ _ _ secondBindings rest head tail =>
        cases head
        cases tail with
        | hit _ _ _ _ thirdBindings rest head tail =>
          cases head
          cases tail
          rfl

/-- The single actual argument arm selects those exact bindings. -/
theorem triple_selects_single (store : Store) (address resolved : Nat) (first second third : Value)
    (firstName secondName thirdName : Binder) (body : NodeId)
    (resolution : Resolve store address resolved)
    (cell : readCell store resolved = some [first, second, third])
    (plain : tupleFields [first, second, third] = some [first, second, third])
    {chosen : NodeId} {bindings : Environment}
    (selected : Selected store (.location address)
      [(.tuple [.binder firstName, .binder secondName, .binder thirdName], body)] chosen bindings) :
    chosen = body ∧ bindings = [(firstName, first), (secondName, second), (thirdName, third)] := by
  cases selected with
  | first _ _ _ actual hit =>
    have same := triple_binders_match store address resolved firstName secondName thirdName
      first second third resolution cell plain hit
    cases same
    exact ⟨rfl, rfl⟩
  | later _ _ _ _ _ _ next => cases next

/-- Three variable fields execute strictly in source order without changing storage. -/
theorem variable_triple_fields {program : Program} {env : Environment} {first second third : NodeId}
    {before after : Store} {values : List Value} {firstName secondName thirdName : Binder}
    {firstValue secondValue thirdValue : Value}
    (firstShape : program first = some (.variable firstName))
    (secondShape : program second = some (.variable secondName))
    (thirdShape : program third = some (.variable thirdName))
    (firstBinding : CoreEval.lookup env firstName = some firstValue)
    (secondBinding : CoreEval.lookup env secondName = some secondValue)
    (thirdBinding : CoreEval.lookup env thirdName = some thirdValue)
    (evaluation : EvalFields program env [first, second, third] before values after) :
    values = [firstValue, secondValue, thirdValue] ∧ after = before := by
  cases evaluation with
  | cons firstEval rest =>
    cases rest with
    | cons secondEval rest =>
      cases rest with
      | cons thirdEval rest =>
        cases rest
        obtain ⟨firstFound, firstStore⟩ := variable_inversion firstShape firstEval
        obtain ⟨secondFound, secondStore⟩ := variable_inversion secondShape secondEval
        obtain ⟨thirdFound, thirdStore⟩ := variable_inversion thirdShape thirdEval
        simp_all

/-- A checked three-variable tuple preserves the old store and records exact fields. -/
theorem checked_variable_triple_retains {program : Program} {root first second third : NodeId}
    {env : Environment} {start finish : Store} {result firstValue secondValue thirdValue : Value}
    (checked : CheckedTuple program root none [first, second, third])
    (firstName secondName thirdName : Binder)
    (firstShape : program first = some (.variable firstName))
    (secondShape : program second = some (.variable secondName))
    (thirdShape : program third = some (.variable thirdName))
    (firstFresh : firstName ≠ checked.contextBinder)
    (secondFresh : secondName ≠ checked.contextBinder)
    (thirdFresh : thirdName ≠ checked.contextBinder)
    (firstBinding : CoreEval.lookup env firstName = some firstValue)
    (secondBinding : CoreEval.lookup env secondName = some secondValue)
    (thirdBinding : CoreEval.lookup env thirdName = some thirdValue)
    (bounded : BoundedLocations start)
    (evaluation : Eval program env root start result finish) :
    ∃ location, location = start.nextLocation ∧ result = .location location ∧
      readCell finish location = some [firstValue, secondValue, thirdValue] ∧
      finish.nextLocation = start.nextLocation + 1 ∧ finish.aliases = start.aliases ∧
      BoundedLocations finish ∧
      (∀ address values, readCell start address = some values → readCell finish address = some values) := by
  obtain ⟨queried, afterFields, afterAlloc, location, values, queryStep, fieldEvals,
    allocated, initialized, resultEq⟩ := checked_tuple_inversion checked evaluation
  have firstBound : CoreEval.lookup (extend env checked.contextBinder .context) firstName = some firstValue := by
    rw [lookup_extended_other env checked.contextBinder firstName firstFresh]
    exact firstBinding
  have secondBound : CoreEval.lookup (extend env checked.contextBinder .context) secondName = some secondValue := by
    rw [lookup_extended_other env checked.contextBinder secondName secondFresh]
    exact secondBinding
  have thirdBound : CoreEval.lookup (extend env checked.contextBinder .context) thirdName = some thirdValue := by
    rw [lookup_extended_other env checked.contextBinder thirdName thirdFresh]
    exact thirdBinding
  obtain ⟨sameValues, sameStore⟩ := variable_triple_fields firstShape secondShape thirdShape
    firstBound secondBound thirdBound fieldEvals
  subst values
  subst afterFields
  have allocationStep : allocate .hostDefault 3 true queried = some (location, afterAlloc) := by
    simpa using allocated
  have initializeStep : initializeStorage location 3 [firstValue, secondValue, thirdValue] afterAlloc =
      some ([firstValue, secondValue, thirdValue], finish) := by simpa [storedFields] using initialized
  obtain ⟨fresh, advances, cell, aliases, finalBound, retained⟩ :=
    host_construct_retains (values := [firstValue, secondValue, thirdValue]) bounded queryStep allocationStep initializeStep
  exact ⟨location, fresh, resultEq, cell, advances, aliases, finalBound, retained⟩

/-- A recursive update reopens its captured closure and passes the actual proper tail. -/
theorem checked_update_recursive_call (program : Program)
    (call function argument wantedNode replacementNode tailNode : NodeId)
    (env : Environment) (start finish : Store) (result wanted replacement tail : Value)
    (functionName wantedName replacementName tailName : Binder) (address resolved code context storage parameter body : NodeId)
    (captureNodes : List NodeId) (captureValues : List Value) (captureEnv : Environment)
    (triple : CheckedTuple program argument none [wantedNode, replacementNode, tailNode])
    (callShape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable functionName))
    (functionBinding : CoreEval.lookup env functionName = some (.location address))
    (resolution : Resolve start address resolved)
    (functionCell : readCell start resolved = some (.closureCode code :: captureValues))
    (closureShape : program code = some (.closure context captureNodes storage parameter body))
    (captureBindings : CaptureBindings program captureNodes captureValues captureEnv)
    (wantedShape : program wantedNode = some (.variable wantedName))
    (replacementShape : program replacementNode = some (.variable replacementName))
    (tailShape : program tailNode = some (.variable tailName))
    (wantedFresh : wantedName ≠ triple.contextBinder) (replacementFresh : replacementName ≠ triple.contextBinder)
    (tailFresh : tailName ≠ triple.contextBinder)
    (wantedBinding : CoreEval.lookup env wantedName = some wanted)
    (replacementBinding : CoreEval.lookup env replacementName = some replacement)
    (tailBinding : CoreEval.lookup env tailName = some tail)
    (bounded : BoundedLocations start) (evaluation : Eval program env call start result finish) :
    ∃ afterArgument payload,
      Eval program (extend captureEnv.reverse parameter (.location payload)) body afterArgument result finish ∧
      Resolve afterArgument payload payload ∧ readCell afterArgument payload = some [wanted, replacement, tail] ∧
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
  obtain ⟨payload, fresh, argumentEq, cell, advances, aliasesSame, afterBound, retained⟩ :=
    checked_variable_triple_retains triple wantedName replacementName tailName wantedShape replacementShape tailShape
      wantedFresh replacementFresh tailFresh wantedBinding replacementBinding tailBinding bounded argumentEval
  subst argumentValue
  have noAlias : readAlias afterArgument payload = none := by
    simpa [readAlias, aliasesSame, fresh] using bounded_fresh_no_alias start bounded
  exact ⟨afterArgument, payload, bodyEval, Resolve.cell payload [wanted, replacement, tail] noAlias cell,
    cell, advances, aliasesSame, afterBound, retained⟩

/-- Exact checked operands and branches of the ordinary first-match update. -/
structure CheckedRecordUpdate (c : Constructors) (program : Program) where
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
  moreBody : NodeId
  hitBody : NodeId
  missBody : NodeId
  comparisonCall : NodeId
  comparisonFunction : NodeId
  comparisonArgument : NodeId
  projection : NodeId
  wantedNode : NodeId
  hitFunction : NodeId
  hitArgument : NodeId
  hitReplacement : NodeId
  hitTail : NodeId
  hitOperand : NodeId
  missFunction : NodeId
  missArgument : NodeId
  missEntry : NodeId
  missOperand : NodeId
  recursiveCall : NodeId
  recursiveFunction : NodeId
  recursiveArgument : NodeId
  recursiveWanted : NodeId
  recursiveReplacement : NodeId
  recursiveTail : NodeId
  wantedName : Binder
  replacementName : Binder
  listName : Binder
  entryName : Binder
  tailName : Binder
  functionName : Binder
  comparisonName : Binder
  projectionName : Binder
  projectionCode : NodeId
  comparator : ComparatorFunction c program
  comparisonPair : CheckedTuple program comparisonArgument none [projection, wantedNode]
  emptyValue : CheckedTuple program emptyBody (some c.empty) []
  hitClosure : CheckedClosure program hitFunction
  hitPair : CheckedTuple program hitArgument none [hitReplacement, hitTail]
  hitValue : CheckedTuple program hitClosure.body (some c.more) [hitOperand]
  missClosure : CheckedClosure program missFunction
  missPair : CheckedTuple program missArgument none [missEntry, recursiveCall]
  missValue : CheckedTuple program missClosure.body (some c.more) [missOperand]
  recursiveTriple : CheckedTuple program recursiveArgument none [recursiveWanted, recursiveReplacement, recursiveTail]
  closureShape : program code = some (.closure context captureNodes storage parameter body)
  bodyShape : program body = some (.caseMatch argumentScrutinee
    [(.tuple [.binder wantedName, .binder replacementName, .binder listName], listBody)])
  argumentShape : program argumentScrutinee = some (.variable parameter)
  listShape : program listBody = some (.caseMatch listScrutinee
    [(.constructor c.empty none, emptyBody),
     (.constructor c.more (some (.tuple [.binder entryName, .binder tailName])), moreBody)])
  listVariableShape : program listScrutinee = some (.variable listName)
  moreShape : program moreBody = some (.caseMatch comparisonCall
    [(.boolean true, hitBody), (.boolean false, missBody)])
  comparisonCallShape : program comparisonCall = some (.apply comparisonFunction comparisonArgument)
  comparisonFunctionShape : program comparisonFunction = some (.variable comparisonName)
  wantedShape : program wantedNode = some (.variable wantedName)
  hitShape : program hitBody = some (.apply hitFunction hitArgument)
  hitReplacementShape : program hitReplacement = some (.variable replacementName)
  hitTailShape : program hitTail = some (.variable tailName)
  hitOperandShape : program hitOperand = some (.variable hitClosure.parameter)
  missShape : program missBody = some (.apply missFunction missArgument)
  missEntryShape : program missEntry = some (.variable entryName)
  missOperandShape : program missOperand = some (.variable missClosure.parameter)
  recursiveShape : program recursiveCall = some (.apply recursiveFunction recursiveArgument)
  recursiveFunctionShape : program recursiveFunction = some (.variable functionName)
  recursiveWantedShape : program recursiveWanted = some (.variable wantedName)
  recursiveReplacementShape : program recursiveReplacement = some (.variable replacementName)
  recursiveTailShape : program recursiveTail = some (.variable tailName)
  projectionFresh : projectionName ≠ comparisonPair.contextBinder
  entryFresh : entryName ≠ comparisonPair.contextBinder
  wantedFresh : wantedName ≠ comparisonPair.contextBinder
  hitReplacementFresh : replacementName ≠ hitPair.contextBinder
  hitTailFresh : tailName ≠ hitPair.contextBinder
  hitOperandFresh : hitClosure.parameter ≠ hitValue.contextBinder
  missEntryFresh : entryName ≠ missPair.contextBinder
  recursiveFunctionOuterFresh : functionName ≠ missPair.contextBinder
  recursiveWantedOuterFresh : wantedName ≠ missPair.contextBinder
  recursiveReplacementOuterFresh : replacementName ≠ missPair.contextBinder
  recursiveTailOuterFresh : tailName ≠ missPair.contextBinder
  missOperandFresh : missClosure.parameter ≠ missValue.contextBinder
  recursiveWantedFresh : wantedName ≠ recursiveTriple.contextBinder
  recursiveReplacementFresh : replacementName ≠ recursiveTriple.contextBinder
  recursiveTailFresh : tailName ≠ recursiveTriple.contextBinder
  distinct : [parameter, wantedName, replacementName, listName, entryName, tailName,
    functionName, comparisonName, projectionName].Nodup


/-- Update destructures the actual key, replacement and list in order. -/
theorem update_argument_executes (c : Constructors) (program : Program) (checked : CheckedRecordUpdate c program)
    (captures : Environment) (start finish : Store) (payload payloadResolved : Nat)
    (wanted replacement list result : Value) (queryId : Id)
    (resolution : Resolve start payload payloadResolved)
    (cell : readCell start payloadResolved = some [wanted, replacement, list])
    (wantedRep : Ident c start wanted queryId)
    (evaluation : Eval program (extend captures checked.parameter (.location payload)) checked.body start result finish) :
    Eval program ([(checked.wantedName, wanted), (checked.replacementName, replacement),
      (checked.listName, list)].reverse ++ extend captures checked.parameter (.location payload))
      checked.listBody start result finish := by
  obtain ⟨middle, actual, chosen, bindings, argumentEval, selected, bodyEval⟩ :=
    case_match_inversion checked.bodyShape evaluation
  obtain ⟨actualBinding, sameStore⟩ := variable_inversion checked.argumentShape argumentEval
  have sameValue : actual = .location payload := by simpa [CoreEval.lookup, extend] using actualBinding.symm
  subst actual
  subst middle
  obtain ⟨address, wantedEq⟩ := ident_is_location c start wanted queryId wantedRep
  have plain : tupleFields [wanted, replacement, list] = some [wanted, replacement, list] := by rw [wantedEq]; rfl
  obtain ⟨sameBody, sameBindings⟩ := triple_selects_single start payload payloadResolved wanted replacement list
    checked.wantedName checked.replacementName checked.listName checked.listBody resolution cell plain selected
  subst chosen
  subst bindings
  exact bodyEval

/-- Distinct argument and match binders preserve the original live values. -/
theorem update_environment_bindings (c : Constructors) (program : Program) (checked : CheckedRecordUpdate c program)
    (captures : Environment) (payload wanted replacement list entry tail self comparison projection : Value)
    (selfBinding : CoreEval.lookup captures checked.functionName = some self)
    (comparisonBinding : CoreEval.lookup captures checked.comparisonName = some comparison)
    (projectionBinding : CoreEval.lookup captures checked.projectionName = some projection) :
    let arguments := [(checked.listName, list), (checked.replacementName, replacement),
      (checked.wantedName, wanted), (checked.parameter, payload)] ++ captures
    let more := [(checked.tailName, tail), (checked.entryName, entry)] ++ arguments
    CoreEval.lookup arguments checked.listName = some list ∧
    CoreEval.lookup more checked.wantedName = some wanted ∧
    CoreEval.lookup more checked.replacementName = some replacement ∧
    CoreEval.lookup more checked.entryName = some entry ∧
    CoreEval.lookup more checked.tailName = some tail ∧
    CoreEval.lookup more checked.functionName = some self ∧
    CoreEval.lookup more checked.comparisonName = some comparison ∧
    CoreEval.lookup more checked.projectionName = some projection := by
  have distinct := checked.distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_false_eq_true, not_or] at distinct
  rcases distinct with ⟨⟨hpw, hpr, hpl, hpe, hpt, hps, hpc, hpp⟩,
    ⟨hwr, hwl, hwe, hwt, hws, hwc, hwp⟩, ⟨hrl, hre, hrt, hrs, hrc, hrp⟩,
    ⟨hle, hlt, hls, hlc, hlp⟩, ⟨het, hes, hec, hep⟩, ⟨hts, htc, htp⟩, ⟨hsc, hsp⟩, hcp⟩
  have selfAbsent : checked.functionName ∉
      [checked.tailName, checked.entryName, checked.listName, checked.replacementName, checked.wantedName, checked.parameter] := by
    simp [Ne.symm hts, Ne.symm hes, Ne.symm hls, Ne.symm hrs, Ne.symm hws, Ne.symm hps]
  have comparisonAbsent : checked.comparisonName ∉
      [checked.tailName, checked.entryName, checked.listName, checked.replacementName, checked.wantedName, checked.parameter] := by
    simp [Ne.symm htc, Ne.symm hec, Ne.symm hlc, Ne.symm hrc, Ne.symm hwc, Ne.symm hpc]
  have projectionAbsent : checked.projectionName ∉
      [checked.tailName, checked.entryName, checked.listName, checked.replacementName, checked.wantedName, checked.parameter] := by
    simp [Ne.symm htp, Ne.symm hep, Ne.symm hlp, Ne.symm hrp, Ne.symm hwp, Ne.symm hpp]
  have wantedAbsent : checked.wantedName ∉
      [checked.tailName, checked.entryName, checked.listName, checked.replacementName] := by simp [hwt, hwe, hwl, hwr]
  have replacementAbsent : checked.replacementName ∉
      [checked.tailName, checked.entryName, checked.listName] := by simp [hrt, hre, hrl]
  have entryAbsent : checked.entryName ∉ [checked.tailName] := by simp [het]
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [CoreEval.lookup]
  · have same := lookup_unshadowed_prefix
      [(checked.tailName, tail), (checked.entryName, entry), (checked.listName, list), (checked.replacementName, replacement)]
      ([(checked.wantedName, wanted), (checked.parameter, payload)] ++ captures) checked.wantedName (by simpa using wantedAbsent)
    simpa [CoreEval.lookup] using same
  · have same := lookup_unshadowed_prefix
      [(checked.tailName, tail), (checked.entryName, entry), (checked.listName, list)]
      ([(checked.replacementName, replacement), (checked.wantedName, wanted), (checked.parameter, payload)] ++ captures)
      checked.replacementName (by simpa using replacementAbsent)
    simpa [CoreEval.lookup] using same
  · have same := lookup_unshadowed_prefix [(checked.tailName, tail)]
      ([(checked.entryName, entry), (checked.listName, list), (checked.replacementName, replacement),
        (checked.wantedName, wanted), (checked.parameter, payload)] ++ captures)
      checked.entryName (by simpa using entryAbsent)
    simpa [CoreEval.lookup] using same
  · simp [CoreEval.lookup]
  · have same := lookup_unshadowed_prefix
      [(checked.tailName, tail), (checked.entryName, entry), (checked.listName, list), (checked.replacementName, replacement),
       (checked.wantedName, wanted), (checked.parameter, payload)] captures checked.functionName (by simpa using selfAbsent)
    exact same.trans selfBinding
  · have same := lookup_unshadowed_prefix
      [(checked.tailName, tail), (checked.entryName, entry), (checked.listName, list), (checked.replacementName, replacement),
       (checked.wantedName, wanted), (checked.parameter, payload)] captures checked.comparisonName (by simpa using comparisonAbsent)
    exact same.trans comparisonBinding
  · have same := lookup_unshadowed_prefix
      [(checked.tailName, tail), (checked.entryName, entry), (checked.listName, list), (checked.replacementName, replacement),
       (checked.wantedName, wanted), (checked.parameter, payload)] captures checked.projectionName (by simpa using projectionAbsent)
    exact same.trans projectionBinding


/-- The More arm replaces the first match or recurses on the original tail. -/
theorem update_more_outcome_with (c : Constructors) (program : Program)
    (checked : CheckedRecordUpdate c program) (env : Environment)
    (start finish : Store) (result wanted replacement tail : Value) (entryAddress : Nat) (entries : List Value)
    (key : Value → Id) (queryId : Id) (selfAddress selfResolved comparisonAddress comparisonResolved keyAddress : Nat)
    (captureValues : List Value) (captureEnv : Environment)
    (selfBinding : CoreEval.lookup env checked.functionName = some (.location selfAddress))
    (comparisonBinding : CoreEval.lookup env checked.comparisonName = some (.location comparisonAddress))
    (entryBinding : CoreEval.lookup env checked.entryName = some (.location entryAddress))
    (wantedBinding : CoreEval.lookup env checked.wantedName = some wanted)
    (replacementBinding : CoreEval.lookup env checked.replacementName = some replacement)
    (tailBinding : CoreEval.lookup env checked.tailName = some tail)
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
      Resolve afterArgument payload payload → readCell afterArgument payload = some [wanted, replacement, tail] →
      BoundedLocations afterArgument → Ident c afterArgument wanted queryId →
      Children c afterArgument tail entries → keys afterArgument →
      afterArgument.aliases = start.aliases →
      (∀ location old, readCell start location = some old → readCell afterArgument location = some old) →
      Eval program (extend captureEnv.reverse checked.parameter (.location payload)) checked.body
        afterArgument recursiveResult recursiveFinish →
      InsertOutcome c afterArgument recursiveFinish recursiveResult (Ash.NetworkLedger.update key queryId replacement entries))
    (evaluation : Eval program env checked.moreBody start result finish) :
    InsertOutcome c start finish result
      (Ash.NetworkLedger.update key queryId replacement (.location entryAddress :: entries)) := by
  obtain ⟨middle, selectedEval, comparisonProgress, comparisonAliases, comparisonBound, comparisonRetained⟩ :=
    comparison_selects_with c program checked.moreBody checked.hitBody checked.missBody
      checked.comparisonCall checked.comparisonFunction checked.comparisonArgument checked.projection checked.wantedNode
      checked.comparator env start finish result wanted queryId (key (.location entryAddress))
      checked.comparisonName checked.wantedName checked.comparisonPair comparisonAddress comparisonResolved
      keyAddress checked.comparisonCallShape checked.comparisonFunctionShape comparisonBinding comparisonResolution
      comparisonCell checked.wantedFresh checked.wantedShape wantedBinding projectionLaw bounded keyRep wantedRep
      checked.moreShape evaluation
  by_cases equal : key (.location entryAddress) = queryId
  · have comparisonTrue : Ash.NetworkLedger.CoreRemoval.compareId (key (.location entryAddress)) queryId = true :=
      (Ash.NetworkLedger.CoreRemoval.compareId_correct _ _).mpr equal
    simp only [comparisonTrue] at selectedEval
    have tailRep' := children_retained c start middle tail entries comparisonAliases comparisonRetained tailRep
    obtain ⟨resultRep, hitProgress, hitAliases, finalBound, hitRetained⟩ :=
      checked_more_rebuild c program checked.hitBody checked.hitFunction checked.hitArgument
        checked.hitReplacement checked.hitTail checked.hitOperand checked.hitClosure checked.hitPair checked.hitValue
        env middle finish result replacement tail entries checked.replacementName checked.tailName
        checked.hitShape checked.hitReplacementShape checked.hitTailShape checked.hitReplacementFresh checked.hitTailFresh
        replacementBinding tailBinding checked.hitOperandShape checked.hitOperandFresh comparisonBound tailRep' selectedEval
    have aliases : finish.aliases = start.aliases := hitAliases.trans comparisonAliases
    have retained : ∀ location old, readCell start location = some old → readCell finish location = some old := by
      intro location old read
      exact hitRetained location old (comparisonRetained location old read)
    have outcome : InsertOutcome c start finish result (replacement :: entries) :=
      ⟨resultRep, Nat.lt_trans comparisonProgress hitProgress, aliases, finalBound, retained⟩
    simpa [Ash.NetworkLedger.update, equal] using outcome
  · have comparisonFalse : Ash.NetworkLedger.CoreRemoval.compareId (key (.location entryAddress)) queryId = false := by
      cases compared : Ash.NetworkLedger.CoreRemoval.compareId (key (.location entryAddress)) queryId with
      | false => rfl
      | true => exact False.elim (equal ((Ash.NetworkLedger.CoreRemoval.compareId_correct _ _).mp compared))
    simp only [comparisonFalse] at selectedEval
    have selfResolution' := resolve_preserved comparisonAliases comparisonRetained selfResolution
    have selfCell' := comparisonRetained selfResolved _ selfCell
    have tailCorrect : ∀ before after remaining,
        BoundedLocations before → before.aliases = middle.aliases →
        (∀ address old, readCell middle address = some old → readCell before address = some old) →
        Eval program (extend env checked.missPair.contextBinder .context) checked.recursiveCall before remaining after →
        Children c after remaining (Ash.NetworkLedger.update key queryId replacement entries) ∧
        after.aliases = before.aliases ∧ BoundedLocations after ∧
        (∀ address old, readCell before address = some old → readCell after address = some old) := by
      intro before after remaining beforeBound beforeAliases beforeRetained recursiveEval
      have selfBound : CoreEval.lookup (extend env checked.missPair.contextBinder .context) checked.functionName =
          some (.location selfAddress) := by
        rw [lookup_extended_other env checked.missPair.contextBinder checked.functionName checked.recursiveFunctionOuterFresh]
        exact selfBinding
      have wantedBound : CoreEval.lookup (extend env checked.missPair.contextBinder .context) checked.wantedName = some wanted := by
        rw [lookup_extended_other env checked.missPair.contextBinder checked.wantedName checked.recursiveWantedOuterFresh]
        exact wantedBinding
      have replacementBound : CoreEval.lookup (extend env checked.missPair.contextBinder .context) checked.replacementName = some replacement := by
        rw [lookup_extended_other env checked.missPair.contextBinder checked.replacementName checked.recursiveReplacementOuterFresh]
        exact replacementBinding
      have tailBound : CoreEval.lookup (extend env checked.missPair.contextBinder .context) checked.tailName = some tail := by
        rw [lookup_extended_other env checked.missPair.contextBinder checked.tailName checked.recursiveTailOuterFresh]
        exact tailBinding
      have currentResolution := resolve_preserved beforeAliases beforeRetained selfResolution'
      have currentCell := beforeRetained selfResolved _ selfCell'
      obtain ⟨afterArgument, payload, bodyEval, payloadResolution, payloadCell, _, argumentAliases,
        argumentBound, argumentRetained⟩ :=
        checked_update_recursive_call program checked.recursiveCall checked.recursiveFunction checked.recursiveArgument
          checked.recursiveWanted checked.recursiveReplacement checked.recursiveTail _ before after remaining wanted replacement tail
          checked.functionName checked.wantedName checked.replacementName checked.tailName selfAddress selfResolved
          checked.code checked.context checked.storage checked.parameter checked.body checked.captureNodes captureValues captureEnv
          checked.recursiveTriple checked.recursiveShape checked.recursiveFunctionShape selfBound currentResolution currentCell
          checked.closureShape captureBindings checked.recursiveWantedShape checked.recursiveReplacementShape checked.recursiveTailShape
          checked.recursiveWantedFresh checked.recursiveReplacementFresh checked.recursiveTailFresh wantedBound replacementBound tailBound
          beforeBound recursiveEval
      have aliasesStart : afterArgument.aliases = start.aliases := argumentAliases.trans (beforeAliases.trans comparisonAliases)
      have retainedStart : ∀ address old, readCell start address = some old → readCell afterArgument address = some old := by
        intro address old read
        exact argumentRetained address old (beforeRetained address old (comparisonRetained address old read))
      have wantedAfter := ident_retained c start afterArgument wanted queryId aliasesStart retainedStart wantedRep
      have tailAfter := children_retained c start afterArgument tail entries aliasesStart retainedStart tailRep
      have keysAfter := keysRetained start afterArgument aliasesStart retainedStart tailKeys
      obtain ⟨resultRep, _, recursiveAliases, finalBound, recursiveRetained⟩ :=
        ih afterArgument after payload remaining payloadResolution payloadCell argumentBound wantedAfter tailAfter keysAfter
          aliasesStart retainedStart bodyEval
      exact ⟨resultRep, recursiveAliases.trans argumentAliases, finalBound,
        fun address old read => recursiveRetained address old (argumentRetained address old read)⟩
    obtain ⟨resultRep, missProgress, missAliases, finalBound, missRetained⟩ :=
      checked_prepend_outcome c program checked.missBody checked.missFunction checked.missArgument
        checked.missEntry checked.recursiveCall checked.missOperand checked.missClosure checked.missPair checked.missValue
        env middle finish result (.location entryAddress) (Ash.NetworkLedger.update key queryId replacement entries)
        checked.entryName checked.missShape checked.missEntryShape checked.missEntryFresh entryBinding
        checked.missOperandShape checked.missOperandFresh comparisonBound tailCorrect selectedEval
    have aliases : finish.aliases = start.aliases := missAliases.trans comparisonAliases
    have retained : ∀ location old, readCell start location = some old → readCell finish location = some old := by
      intro location old read
      exact missRetained location old (comparisonRetained location old read)
    have outcome : InsertOutcome c start finish result
        (.location entryAddress :: Ash.NetworkLedger.update key queryId replacement entries) :=
      ⟨resultRep, Nat.lt_trans comparisonProgress missProgress, aliases, finalBound, retained⟩
    simpa [Ash.NetworkLedger.update, equal] using outcome

/-- The Empty branch returns a fresh represented empty list. -/
theorem update_empty_outcome (c : Constructors) (program : Program) (checked : CheckedRecordUpdate c program)
    (env : Environment) (start finish : Store) (list result : Value)
    (binding : CoreEval.lookup env checked.listName = some list)
    (bounded : BoundedLocations start) (representation : Children c start list [])
    (evaluation : Eval program env checked.listBody start result finish) :
    InsertOutcome c start finish result [] := by
  cases representation with
  | empty address resolved resolution cell =>
    have emptyEval := empty_match_executes_first program start finish env checked.listBody checked.listScrutinee
      checked.listName c.empty c.more checked.emptyBody checked.moreBody (.tuple [.binder checked.entryName, .binder checked.tailName])
      address resolved result checked.listShape checked.listVariableShape binding resolution cell evaluation
    obtain ⟨location, resultEq, fresh, advances, resultCell, aliases, finalBound, retained⟩ :=
      checked_nullary_retains checked.emptyValue bounded emptyEval
    have noAlias : readAlias finish location = none := by
      simpa [readAlias, aliases, fresh] using bounded_fresh_no_alias start bounded
    have resultRep : Children c finish result [] := by
      rw [resultEq]
      exact Children.empty location location (Resolve.cell location [.tag c.empty] noAlias resultCell) resultCell
    refine ⟨resultRep, ?_, aliases, finalBound, retained⟩
    omega

/-- Every finite normal execution replaces the first matching whole Record. -/
theorem update_body_correct_with (c : Constructors) (program : Program)
    (checked : CheckedRecordUpdate c program) (R : Store → Value → Nat → Prop)
    (relationRetained : ∀ before after entry keyAddress,
      after.aliases = before.aliases →
      (∀ location old, readCell before location = some old → readCell after location = some old) →
      R before entry keyAddress → R after entry keyAddress)
    (captureValues : List Value) (captureEnv : Environment)
    (selfAddress selfResolved comparisonAddress comparisonResolved projectionAddress projectionResolved : Nat)
    (wanted replacement : Value) (queryId : Id) (key : Value → Id) (entries : List Value)
    (selfBinding : CoreEval.lookup captureEnv.reverse checked.functionName = some (.location selfAddress))
    (comparisonBinding : CoreEval.lookup captureEnv.reverse checked.comparisonName = some (.location comparisonAddress))
    (projectionBinding : CoreEval.lookup captureEnv.reverse checked.projectionName = some (.location projectionAddress))
    (captureBindings : CaptureBindings program checked.captureNodes captureValues captureEnv)
    (projectionFor : ∀ env start entryAddress keyAddress,
      R start (.location entryAddress) keyAddress →
      CoreEval.lookup env checked.projectionName = some (.location projectionAddress) →
      CoreEval.lookup env checked.entryName = some (.location entryAddress) →
      Resolve start projectionAddress projectionResolved →
      readCell start projectionResolved = some [.closureCode checked.projectionCode] →
      ProjectionAfterQuery program checked.projection env checked.comparisonPair.contextBinder start keyAddress) :
    ∀ start finish payload payloadResolved list result,
      Resolve start payload payloadResolved → readCell start payloadResolved = some [wanted, replacement, list] →
      BoundedLocations start → Ident c start wanted queryId → Children c start list entries →
      RepresentedEntries c R start key entries →
      Resolve start selfAddress selfResolved →
      readCell start selfResolved = some (.closureCode checked.code :: captureValues) →
      Resolve start comparisonAddress comparisonResolved →
      readCell start comparisonResolved = some [.closureCode checked.comparator.code] →
      Resolve start projectionAddress projectionResolved →
      readCell start projectionResolved = some [.closureCode checked.projectionCode] →
      Eval program (extend captureEnv.reverse checked.parameter (.location payload)) checked.body start result finish →
      InsertOutcome c start finish result (Ash.NetworkLedger.update key queryId replacement entries) := by
  induction entries with
  | nil =>
    intro start finish payload payloadResolved list result payloadResolution payloadCell bounded wantedRep listRep keys
      selfResolution selfCell comparisonResolution comparisonCell projectionResolution projectionCell evaluation
    have listEval := update_argument_executes c program checked captureEnv.reverse start finish payload payloadResolved
      wanted replacement list result queryId payloadResolution payloadCell wantedRep evaluation
    have scope := update_environment_bindings c program checked captureEnv.reverse (.location payload) wanted replacement list
      .unit .unit (.location selfAddress) (.location comparisonAddress) (.location projectionAddress)
      selfBinding comparisonBinding projectionBinding
    simpa [Ash.NetworkLedger.update] using
      update_empty_outcome c program checked _ start finish list result scope.1 bounded listRep listEval
  | cons entry entries ih =>
    intro start finish payload payloadResolved list result payloadResolution payloadCell bounded wantedRep listRep keys
      selfResolution selfCell comparisonResolution comparisonCell projectionResolution projectionCell evaluation
    have listEval := update_argument_executes c program checked captureEnv.reverse start finish payload payloadResolved
      wanted replacement list result queryId payloadResolution payloadCell wantedRep evaluation
    obtain ⟨entryAddress, keyAddress, entryEq, entryRep, keyRep⟩ := keys entry (by simp)
    subst entry
    cases listRep with
    | more listAddress listResolved listPayload listTuple _ tail _ listResolution listCell listPayloadResolution listFields tailRep =>
      have scope := update_environment_bindings c program checked captureEnv.reverse (.location payload) wanted replacement (.location listAddress)
        (.location entryAddress) tail (.location selfAddress) (.location comparisonAddress) (.location projectionAddress)
        selfBinding comparisonBinding projectionBinding
      have moreEval := more_match_executes_second program start finish _ checked.listBody checked.listScrutinee
        checked.listName c.empty c.more checked.emptyBody checked.moreBody checked.entryName checked.tailName
        listAddress listResolved listPayload listTuple entryAddress tail result checked.listShape checked.listVariableShape
        scope.1 listResolution listCell listPayloadResolution listFields listEval
      have tailKeys : RepresentedEntries c R start key entries := by
        intro other member
        exact keys other (by simp [member])
      have tailIH : ∀ afterArgument recursiveFinish recPayload recursiveResult,
        Resolve afterArgument recPayload recPayload → readCell afterArgument recPayload = some [wanted, replacement, tail] →
        BoundedLocations afterArgument → Ident c afterArgument wanted queryId →
        Children c afterArgument tail entries → RepresentedEntries c R afterArgument key entries →
        afterArgument.aliases = start.aliases →
        (∀ location old, readCell start location = some old → readCell afterArgument location = some old) →
        Eval program (extend captureEnv.reverse checked.parameter (.location recPayload)) checked.body
          afterArgument recursiveResult recursiveFinish →
        InsertOutcome c afterArgument recursiveFinish recursiveResult (Ash.NetworkLedger.update key queryId replacement entries) := by
        intro afterArgument recursiveFinish recPayload recursiveResult recResolution recCell recBound recWanted recTail recKeys
          recAliases recRetained recEval
        apply ih afterArgument recursiveFinish recPayload recPayload tail recursiveResult recResolution recCell recBound
          recWanted recTail recKeys (resolve_preserved recAliases recRetained selfResolution)
          (recRetained selfResolved _ selfCell) (resolve_preserved recAliases recRetained comparisonResolution)
          (recRetained comparisonResolved _ comparisonCell) (resolve_preserved recAliases recRetained projectionResolution)
          (recRetained projectionResolved _ projectionCell) recEval
      have law := projectionFor _ start entryAddress keyAddress entryRep scope.2.2.2.2.2.2.2 scope.2.2.2.1
        projectionResolution projectionCell
      exact update_more_outcome_with c program checked _ start finish result wanted replacement tail entryAddress entries key
        queryId selfAddress selfResolved comparisonAddress comparisonResolved keyAddress captureValues captureEnv
        scope.2.2.2.2.2.1 scope.2.2.2.2.2.2.1 scope.2.2.2.1 scope.2.1 scope.2.2.1 scope.2.2.2.2.1
        selfResolution selfCell captureBindings comparisonResolution comparisonCell law keyRep wantedRep tailRep
        (fun store => RepresentedEntries c R store key entries) tailKeys
        (fun before after aliases cells reps => represented_entries_retained c R before after key entries
          relationRetained aliases cells reps) bounded tailIH moreEval

/-- The four-field Record helper instantiates exact first-match update. -/
theorem record_update_body_correct (c : Constructors) (program : Program)
    (checked : CheckedRecordUpdate c program)
    (projection : Ash.NetworkLedger.CoreRecordLookup.RecordProjectionShape program checked.projection)
    (functionName : projection.functionName = checked.projectionName)
    (entryName : projection.recordName = checked.entryName)
    (code : projection.code = checked.projectionCode)
    (captureValues : List Value) (captureEnv : Environment)
    (selfAddress selfResolved comparisonAddress comparisonResolved projectionAddress projectionResolved : Nat)
    (wanted replacement : Value) (queryId : Id) (key : Value → Id) (entries : List Value)
    (selfBinding : CoreEval.lookup captureEnv.reverse checked.functionName = some (.location selfAddress))
    (comparisonBinding : CoreEval.lookup captureEnv.reverse checked.comparisonName = some (.location comparisonAddress))
    (projectionBinding : CoreEval.lookup captureEnv.reverse checked.projectionName = some (.location projectionAddress))
    (captureBindings : CaptureBindings program checked.captureNodes captureValues captureEnv) :
    ∀ start finish payload payloadResolved list result,
      Resolve start payload payloadResolved → readCell start payloadResolved = some [wanted, replacement, list] →
      BoundedLocations start → Ident c start wanted queryId → Children c start list entries →
      RepresentedEntries c (Ash.NetworkLedger.CoreRecordLookup.RecordEntry projection.record) start key entries →
      Resolve start selfAddress selfResolved →
      readCell start selfResolved = some (.closureCode checked.code :: captureValues) →
      Resolve start comparisonAddress comparisonResolved →
      readCell start comparisonResolved = some [.closureCode checked.comparator.code] →
      Resolve start projectionAddress projectionResolved →
      readCell start projectionResolved = some [.closureCode checked.projectionCode] →
      Eval program (extend captureEnv.reverse checked.parameter (.location payload)) checked.body start result finish →
      InsertOutcome c start finish result (Ash.NetworkLedger.update key queryId replacement entries) := by
  apply update_body_correct_with c program checked (Ash.NetworkLedger.CoreRecordLookup.RecordEntry projection.record)
    (Ash.NetworkLedger.CoreRecordLookup.record_entry_retained projection.record) captureValues captureEnv selfAddress selfResolved
    comparisonAddress comparisonResolved projectionAddress projectionResolved wanted replacement queryId key entries
    selfBinding comparisonBinding projectionBinding captureBindings
  intro env start entryAddress keyAddress entryRep functionBinding entryBinding functionResolution functionCell
  obtain ⟨address, resolved, payload, tuple, parent, phase, children, same, resolution, cell,
    payloadResolution, fields⟩ := entryRep
  have addressEq : address = entryAddress := by simpa using same.symm
  subst address
  have functionBound : CoreEval.lookup env projection.functionName = some (.location projectionAddress) := by
    simpa [functionName] using functionBinding
  have entryBound : CoreEval.lookup env projection.recordName = some (.location entryAddress) := by
    simpa [entryName] using entryBinding
  have closureCell : readCell start projectionResolved = some [.closureCode projection.code] := by
    simpa [code] using functionCell
  have functionFresh : projection.functionName ≠ checked.comparisonPair.contextBinder := by
    simpa [functionName] using checked.projectionFresh
  have entryFresh : projection.recordName ≠ checked.comparisonPair.contextBinder := by
    simpa [entryName] using checked.entryFresh
  exact Ash.NetworkLedger.CoreRecordProjection.record_projection_after_query program env start checked.projection
    projection.function projection.argument projection.code projection.context projection.storage projection.parameter
    projection.body projection.scrutinee projection.returnKey projection.functionName projection.recordName
    projection.keyName projection.parentName projection.phaseName projection.childrenName checked.comparisonPair.contextBinder
    projection.record projectionAddress projectionResolved entryAddress resolved payload tuple keyAddress parent phase children
    functionFresh entryFresh projection.callShape projection.functionShape projection.argumentShape functionBound entryBound
    functionResolution closureCell projection.closureShape projection.differentParent projection.differentPhase
    projection.differentChildren projection.bodyShape projection.scrutineeShape projection.returnShape
    resolution cell payloadResolution fields

end Ash.NetworkLedger.CoreRecordUpdate
