import NetworkLedgerCoreValues

/-
The finite ordered lookup schema over the same strict Core evaluator used by
removal. A checked graph and a normal evaluation remain premises; the Rust
arena, selected allocation handler, captures and finite input must separately
be authenticated before this model can authorize a fact.
-/
namespace Ash.NetworkLedger.CoreLookup

open Ash.NetworkLedger
open Ash.NetworkLedger.CoreRegion
open Ash.NetworkLedger.CoreEval
open Ash.NetworkLedger.CoreValues

/-- The returned option retains the actual first matching whole entry. -/
inductive LookupResult (absent present : Constructor) (store : Store) : Value → Option Value → Prop where
  | absentResult (address resolved : Nat)
      (resolution : Resolve store address resolved)
      (cell : readCell store resolved = some [.tag absent]) :
      LookupResult absent present store (.location address) none
  | presentResult (address resolved : Nat) (entry : Value)
      (resolution : Resolve store address resolved)
      (cell : readCell store resolved = some [.tag present, entry]) :
      LookupResult absent present store (.location address) (some entry)

def LookupOutcome (absent present : Constructor) (start finish : Store)
    (result : Value) (expected : Option Value) : Prop :=
  LookupResult absent present finish result expected ∧
  start.nextLocation < finish.nextLocation ∧ finish.aliases = start.aliases ∧
  BoundedLocations finish ∧
  (∀ address old, readCell start address = some old → readCell finish address = some old)

/-- The empty arm actually returns the checked absent constructor. -/
theorem lookup_empty_outcome (c : Constructors) (program : Program) (env : Environment)
    (node scrutinee emptyBody moreBody : NodeId) (listName entryName tailName : Binder)
    (absent : Constructor) (start finish : Store) (list result : Value)
    (shape : program node = some (.caseMatch scrutinee
      [(.constructor c.empty none, emptyBody),
       (.constructor c.more (some (.tuple [.binder entryName, .binder tailName])), moreBody)]))
    (variableShape : program scrutinee = some (.variable listName))
    (binding : CoreEval.lookup env listName = some list)
    (absentValue : CheckedTuple program emptyBody (some absent) [])
    (bounded : BoundedLocations start) (representation : Children c start list [])
    (evaluation : Eval program env node start result finish) :
    ∀ present, LookupOutcome absent present start finish result none := by
  intro present
  cases representation with
  | empty address resolved resolution cell =>
    have emptyEval := empty_match_executes_first program start finish env node scrutinee listName c.empty c.more
      emptyBody moreBody (.tuple [.binder entryName, .binder tailName]) address resolved result
      shape variableShape binding resolution cell evaluation
    obtain ⟨location, resultEq, fresh, advance, resultCell, aliases, finalBound, retained⟩ :=
      checked_nullary_retains absentValue bounded emptyEval
    have noAlias : readAlias finish location = none := by
      simpa [readAlias, aliases, fresh] using bounded_fresh_no_alias start bounded
    have resultRep : LookupResult absent present finish result none := by
      rw [resultEq]
      exact LookupResult.absentResult location location
        (Resolve.cell location [.tag absent] noAlias resultCell) resultCell
    refine ⟨resultRep, ?_, aliases, finalBound, retained⟩
    omega

/-- The checked constructor call stores the actual entry, with no replacement. -/
theorem checked_present_outcome (program : Program) (env : Environment)
    (call function argument operand : NodeId) (entryName : Binder)
    (present absent : Constructor) (closure : CheckedClosure program function)
    (constructed : CheckedTuple program closure.body (some present) [operand])
    (start finish : Store) (entry result : Value)
    (callShape : program call = some (.apply function argument))
    (argumentShape : program argument = some (.variable entryName))
    (entryBinding : CoreEval.lookup env entryName = some entry)
    (operandShape : program operand = some (.variable closure.parameter))
    (operandFresh : closure.parameter ≠ constructed.contextBinder)
    (bounded : BoundedLocations start) (evaluation : Eval program env call start result finish) :
    LookupOutcome absent present start finish result (some entry) := by
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
  obtain ⟨argumentBinding, sameStore⟩ := variable_inversion argumentShape argumentEval
  have sameValue : argumentValue = entry := Option.some.inj (argumentBinding.symm.trans entryBinding)
  subst argumentValue
  subst afterArgument
  have operandBinding : CoreEval.lookup (extend [] closure.parameter entry) closure.parameter = some entry := by
    simp [CoreEval.lookup, extend]
  obtain ⟨resultAddress, resultEq, resultFresh, _, resultCell, resultAliases, finalBound, resultRetained⟩ :=
    checked_unary_constructor_retains constructed closure.parameter operandShape operandFresh operandBinding
      closureBound bodyEval
  have finalAliases : finish.aliases = start.aliases := resultAliases.trans closureAliases
  have retained : ∀ address old, readCell start address = some old → readCell finish address = some old := by
    intro address old read
    exact resultRetained address old (closureRetained address old read)
  have noAlias : readAlias finish resultAddress = none := by
    simpa [readAlias, resultAliases, resultFresh] using bounded_fresh_no_alias afterFunction closureBound
  have resultRep : LookupResult absent present finish result (some entry) := by
    rw [resultEq]
    exact LookupResult.presentResult resultAddress resultAddress entry
      (Resolve.cell resultAddress [.tag present, entry] noAlias resultCell) resultCell
  have progress : start.nextLocation < finish.nextLocation := by
    have live := finalBound.2.1 closureLocation _
      (readCell_member finish closureLocation _ (resultRetained closureLocation _ closureCell))
    rw [closureFresh] at live
    exact live
  exact ⟨resultRep, progress, finalAliases, finalBound, retained⟩


/-- All operands, bindings and branches of the supported actual lookup body. -/
structure CheckedLookupBase (c : Constructors) (program : Program) (absent present : Constructor) where
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
  comparisonCall : NodeId
  comparisonFunction : NodeId
  comparisonArgument : NodeId
  projection : NodeId
  wantedNode : NodeId
  recursiveCall : NodeId
  recursiveFunction : NodeId
  recursiveArgument : NodeId
  recursiveWanted : NodeId
  recursiveTail : NodeId
  hitFunction : NodeId
  hitArgument : NodeId
  hitOperand : NodeId
  wantedName : Binder
  listName : Binder
  entryName : Binder
  tailName : Binder
  functionName : Binder
  comparisonName : Binder
  projectionName : Binder
  comparator : ComparatorFunction c program
  projectionCode : NodeId
  comparisonPair : CheckedTuple program comparisonArgument none [projection, wantedNode]
  recursivePair : CheckedTuple program recursiveArgument none [recursiveWanted, recursiveTail]
  absentValue : CheckedTuple program emptyBody (some absent) []
  presentClosure : CheckedClosure program hitFunction
  presentValue : CheckedTuple program presentClosure.body (some present) [hitOperand]
  closureShape : program code = some (.closure context captureNodes storage parameter body)
  bodyShape : program body = some (.caseMatch argumentScrutinee
    [(.tuple [.binder wantedName, .binder listName], listBody)])
  argumentShape : program argumentScrutinee = some (.variable parameter)
  listShape : program listBody = some (.caseMatch listScrutinee
    [(.constructor c.empty none, emptyBody),
     (.constructor c.more (some (.tuple [.binder entryName, .binder tailName])), moreBody)])
  listVariableShape : program listScrutinee = some (.variable listName)
  moreShape : program moreBody = some (.caseMatch comparisonCall
    [(.boolean true, hitBody), (.boolean false, recursiveCall)])
  comparisonCallShape : program comparisonCall = some (.apply comparisonFunction comparisonArgument)
  comparisonFunctionShape : program comparisonFunction = some (.variable comparisonName)
  wantedShape : program wantedNode = some (.variable wantedName)
  recursiveCallShape : program recursiveCall = some (.apply recursiveFunction recursiveArgument)
  recursiveFunctionShape : program recursiveFunction = some (.variable functionName)
  recursiveWantedShape : program recursiveWanted = some (.variable wantedName)
  recursiveTailShape : program recursiveTail = some (.variable tailName)
  hitShape : program hitBody = some (.apply hitFunction hitArgument)
  hitArgumentShape : program hitArgument = some (.variable entryName)
  hitOperandShape : program hitOperand = some (.variable presentClosure.parameter)
  projectionFresh : projectionName ≠ comparisonPair.contextBinder
  entryFresh : entryName ≠ comparisonPair.contextBinder
  wantedFresh : wantedName ≠ comparisonPair.contextBinder
  recursiveWantedFresh : wantedName ≠ recursivePair.contextBinder
  recursiveTailFresh : tailName ≠ recursivePair.contextBinder
  presentFresh : presentClosure.parameter ≠ presentValue.contextBinder
  distinct : [parameter, wantedName, listName, entryName, tailName,
    functionName, comparisonName, projectionName].Nodup


/-- The original Child projection remains a concrete checked specialization. -/
structure CheckedLookup (c : Constructors) (program : Program) (absent present : Constructor)
    extends CheckedLookupBase c program absent present where
  projectionShape : ProjectionCallShape program projection
  projectionFunctionName : projectionShape.functionName = projectionName
  projectionEntryName : projectionShape.entryName = entryName
  projectionChild : projectionShape.child = c.child
  projectionCodeShape : projectionShape.code = projectionCode


/-- A miss applies the checked closure to the original wanted value and proper tail. -/
theorem lookup_miss_outcome_with (c : Constructors) (program : Program) (absent present : Constructor)
    (checked : CheckedLookupBase c program absent present) (env : Environment)
    (start finish : Store) (result wanted tail : Value) (entries : List Value)
    (key : Value → Id) (queryId : Id) (address resolved : Nat)
    (captureValues : List Value) (captureEnv : Environment)
    (functionBinding : CoreEval.lookup env checked.functionName = some (.location address))
    (wantedBinding : CoreEval.lookup env checked.wantedName = some wanted)
    (tailBinding : CoreEval.lookup env checked.tailName = some tail)
    (resolution : Resolve start address resolved)
    (functionCell : readCell start resolved = some (.closureCode checked.code :: captureValues))
    (captureBindings : CaptureBindings program checked.captureNodes captureValues captureEnv)
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
      Eval program (extend captureEnv.reverse checked.parameter (.location payload)) checked.body
        afterArgument recursiveResult recursiveFinish →
      LookupOutcome absent present afterArgument recursiveFinish recursiveResult
        (Ash.NetworkLedger.lookup key queryId entries))
    (evaluation : Eval program env checked.recursiveCall start result finish) :
    LookupOutcome absent present start finish result (Ash.NetworkLedger.lookup key queryId entries) := by
  obtain ⟨afterArgument, payload, bodyEval, payloadResolution, payloadCell, argumentProgress,
    argumentAliases, argumentBound, argumentRetained⟩ :=
    checked_recursive_call program checked.recursiveCall checked.recursiveFunction checked.recursiveArgument
      checked.recursiveWanted checked.recursiveTail env start finish result wanted tail checked.functionName
      checked.wantedName checked.tailName address resolved checked.code checked.context checked.storage
      checked.parameter checked.body checked.captureNodes captureValues captureEnv checked.recursivePair
      checked.recursiveCallShape checked.recursiveFunctionShape functionBinding resolution functionCell
      checked.closureShape captureBindings checked.recursiveWantedShape checked.recursiveTailShape
      checked.recursiveWantedFresh checked.recursiveTailFresh wantedBinding tailBinding bounded evaluation
  have wantedAfter := ident_retained c start afterArgument wanted queryId argumentAliases argumentRetained wantedRep
  have tailAfter := children_retained c start afterArgument tail entries argumentAliases argumentRetained tailRep
  have keysAfter := keysRetained start afterArgument argumentAliases argumentRetained tailKeys
  obtain ⟨resultRep, recursiveProgress, recursiveAliases, finalBound, recursiveRetained⟩ :=
    ih afterArgument finish payload result payloadResolution payloadCell argumentBound wantedAfter tailAfter keysAfter
      argumentAliases argumentRetained bodyEval
  have aliases : finish.aliases = start.aliases := recursiveAliases.trans argumentAliases
  have retained : ∀ location old, readCell start location = some old → readCell finish location = some old := by
    intro location old read
    exact recursiveRetained location old (argumentRetained location old read)
  have argumentIncreases : start.nextLocation < afterArgument.nextLocation := by omega
  exact ⟨resultRep, Nat.lt_trans argumentIncreases recursiveProgress, aliases, finalBound, retained⟩


theorem lookup_miss_outcome (c : Constructors) (program : Program) (absent present : Constructor)
    (checked : CheckedLookup c program absent present) (env : Environment)
    (start finish : Store) (result wanted tail : Value) (entries : List Value)
    (key : Value → Id) (queryId : Id) (address resolved : Nat)
    (captureValues : List Value) (captureEnv : Environment)
    (functionBinding : CoreEval.lookup env checked.functionName = some (.location address))
    (wantedBinding : CoreEval.lookup env checked.wantedName = some wanted)
    (tailBinding : CoreEval.lookup env checked.tailName = some tail)
    (resolution : Resolve start address resolved)
    (functionCell : readCell start resolved = some (.closureCode checked.code :: captureValues))
    (captureBindings : CaptureBindings program checked.captureNodes captureValues captureEnv)
    (bounded : BoundedLocations start) (wantedRep : Ident c start wanted queryId)
    (tailRep : Children c start tail entries) (tailKeys : KeyedEntries c start key entries)
    (ih : ∀ afterArgument recursiveFinish payload recursiveResult,
      Resolve afterArgument payload payload → readCell afterArgument payload = some [wanted, tail] →
      BoundedLocations afterArgument → Ident c afterArgument wanted queryId →
      Children c afterArgument tail entries → KeyedEntries c afterArgument key entries →
      afterArgument.aliases = start.aliases →
      (∀ location old, readCell start location = some old → readCell afterArgument location = some old) →
      Eval program (extend captureEnv.reverse checked.parameter (.location payload)) checked.body
        afterArgument recursiveResult recursiveFinish →
      LookupOutcome absent present afterArgument recursiveFinish recursiveResult
        (Ash.NetworkLedger.lookup key queryId entries))
    (evaluation : Eval program env checked.recursiveCall start result finish) :
    LookupOutcome absent present start finish result (Ash.NetworkLedger.lookup key queryId entries) := by
  obtain ⟨afterArgument, payload, bodyEval, payloadResolution, payloadCell, argumentProgress,
    argumentAliases, argumentBound, argumentRetained⟩ :=
    checked_recursive_call program checked.recursiveCall checked.recursiveFunction checked.recursiveArgument
      checked.recursiveWanted checked.recursiveTail env start finish result wanted tail checked.functionName
      checked.wantedName checked.tailName address resolved checked.code checked.context checked.storage
      checked.parameter checked.body checked.captureNodes captureValues captureEnv checked.recursivePair
      checked.recursiveCallShape checked.recursiveFunctionShape functionBinding resolution functionCell
      checked.closureShape captureBindings checked.recursiveWantedShape checked.recursiveTailShape
      checked.recursiveWantedFresh checked.recursiveTailFresh wantedBinding tailBinding bounded evaluation
  have wantedAfter := ident_retained c start afterArgument wanted queryId argumentAliases argumentRetained wantedRep
  have tailAfter := children_retained c start afterArgument tail entries argumentAliases argumentRetained tailRep
  have keysAfter := keyed_entries_retained c start afterArgument key entries argumentAliases argumentRetained tailKeys
  obtain ⟨resultRep, recursiveProgress, recursiveAliases, finalBound, recursiveRetained⟩ :=
    ih afterArgument finish payload result payloadResolution payloadCell argumentBound wantedAfter tailAfter keysAfter
      argumentAliases argumentRetained bodyEval
  have aliases : finish.aliases = start.aliases := recursiveAliases.trans argumentAliases
  have retained : ∀ location old, readCell start location = some old → readCell finish location = some old := by
    intro location old read
    exact recursiveRetained location old (argumentRetained location old read)
  have argumentIncreases : start.nextLocation < afterArgument.nextLocation := by omega
  exact ⟨resultRep, Nat.lt_trans argumentIncreases recursiveProgress, aliases, finalBound, retained⟩


/-- A More arm uses the exact represented key and preserves the whole head. -/
theorem lookup_more_outcome_with (c : Constructors) (program : Program) (absent present : Constructor)
    (checked : CheckedLookupBase c program absent present) (env : Environment)
    (start finish : Store) (result wanted tail : Value) (entryAddress : Nat) (entries : List Value)
    (key : Value → Id) (queryId : Id) (selfAddress selfResolved comparisonAddress comparisonResolved keyAddress : Nat)
    (captureValues : List Value) (captureEnv : Environment)
    (selfBinding : CoreEval.lookup env checked.functionName = some (.location selfAddress))
    (comparisonBinding : CoreEval.lookup env checked.comparisonName = some (.location comparisonAddress))
    (entryBinding : CoreEval.lookup env checked.entryName = some (.location entryAddress))
    (wantedBinding : CoreEval.lookup env checked.wantedName = some wanted)
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
      Resolve afterArgument payload payload → readCell afterArgument payload = some [wanted, tail] →
      BoundedLocations afterArgument → Ident c afterArgument wanted queryId →
      Children c afterArgument tail entries → keys afterArgument →
      afterArgument.aliases = start.aliases →
      (∀ location old, readCell start location = some old → readCell afterArgument location = some old) →
      Eval program (extend captureEnv.reverse checked.parameter (.location payload)) checked.body
        afterArgument recursiveResult recursiveFinish →
      LookupOutcome absent present afterArgument recursiveFinish recursiveResult
        (Ash.NetworkLedger.lookup key queryId entries))
    (evaluation : Eval program env checked.moreBody start result finish) :
    LookupOutcome absent present start finish result
      (Ash.NetworkLedger.lookup key queryId (.location entryAddress :: entries)) := by
  obtain ⟨middle, selectedEval, comparisonProgress, comparisonAliases, comparisonBound, comparisonRetained⟩ :=
    comparison_selects_with c program checked.moreBody checked.hitBody checked.recursiveCall
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
    obtain ⟨resultRep, hitProgress, hitAliases, finalBound, hitRetained⟩ :=
      checked_present_outcome program env checked.hitBody checked.hitFunction checked.hitArgument checked.hitOperand
        checked.entryName present absent checked.presentClosure checked.presentValue middle finish (.location entryAddress) result
        checked.hitShape checked.hitArgumentShape entryBinding checked.hitOperandShape checked.presentFresh
        comparisonBound selectedEval
    have aliases : finish.aliases = start.aliases := hitAliases.trans comparisonAliases
    have retained : ∀ location old, readCell start location = some old → readCell finish location = some old := by
      intro location old read
      exact hitRetained location old (comparisonRetained location old read)
    have outcome : LookupOutcome absent present start finish result (some (.location entryAddress)) :=
      ⟨resultRep, Nat.lt_trans comparisonProgress hitProgress, aliases, finalBound, retained⟩
    simpa [Ash.NetworkLedger.lookup, equal] using outcome
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
      LookupOutcome absent present afterArgument recursiveFinish recursiveResult
        (Ash.NetworkLedger.lookup key queryId entries) := by
      intro afterArgument recursiveFinish recPayload recursiveResult recResolution recCell recBound recWanted recTail recKeys
        recAliases recRetained recEval
      apply ih afterArgument recursiveFinish recPayload recursiveResult recResolution recCell recBound recWanted recTail recKeys
        (recAliases.trans comparisonAliases) _ recEval
      intro location old read
      exact recRetained location old (comparisonRetained location old read)
    obtain ⟨resultRep, missProgress, missAliases, finalBound, missRetained⟩ :=
      lookup_miss_outcome_with c program absent present checked env middle finish result wanted tail entries key queryId
        selfAddress selfResolved captureValues captureEnv selfBinding wantedBinding tailBinding selfResolution' selfCell'
        captureBindings comparisonBound wantedRep' tailRep' keys tailKeys' keysRetained tailIH selectedEval
    have aliases : finish.aliases = start.aliases := missAliases.trans comparisonAliases
    have retained : ∀ location old, readCell start location = some old → readCell finish location = some old := by
      intro location old read
      exact missRetained location old (comparisonRetained location old read)
    have outcome : LookupOutcome absent present start finish result (Ash.NetworkLedger.lookup key queryId entries) :=
      ⟨resultRep, Nat.lt_trans comparisonProgress missProgress, aliases, finalBound, retained⟩
    simpa [Ash.NetworkLedger.lookup, equal] using outcome


/-- The More arm compares the real head and recurses only on its actual tail. -/
theorem lookup_more_outcome (c : Constructors) (program : Program) (absent present : Constructor)
    (checked : CheckedLookup c program absent present) (env : Environment)
    (start finish : Store) (result entry wanted tail : Value) (entries : List Value)
    (key : Value → Id) (queryId : Id)
    (selfAddress selfResolved comparisonAddress comparisonResolved projectionAddress projectionResolved keyAddress : Nat)
    (destination : Value) (captureValues : List Value) (captureEnv : Environment)
    (selfBinding : CoreEval.lookup env checked.functionName = some (.location selfAddress))
    (comparisonBinding : CoreEval.lookup env checked.comparisonName = some (.location comparisonAddress))
    (projectionBinding : CoreEval.lookup env checked.projectionName = some (.location projectionAddress))
    (entryBinding : CoreEval.lookup env checked.entryName = some entry)
    (wantedBinding : CoreEval.lookup env checked.wantedName = some wanted)
    (tailBinding : CoreEval.lookup env checked.tailName = some tail)
    (selfResolution : Resolve start selfAddress selfResolved)
    (selfCell : readCell start selfResolved = some (.closureCode checked.code :: captureValues))
    (captureBindings : CaptureBindings program checked.captureNodes captureValues captureEnv)
    (comparisonResolution : Resolve start comparisonAddress comparisonResolved)
    (comparisonCell : readCell start comparisonResolved = some [.closureCode checked.comparator.code])
    (projectionResolution : Resolve start projectionAddress projectionResolved)
    (projectionCell : readCell start projectionResolved = some [.closureCode checked.projectionShape.code])
    (entryRep : Entry c start entry (.location keyAddress) destination)
    (keyRep : Ident c start (.location keyAddress) (key entry))
    (wantedRep : Ident c start wanted queryId)
    (tailRep : Children c start tail entries) (tailKeys : KeyedEntries c start key entries)
    (bounded : BoundedLocations start)
    (ih : ∀ afterArgument recursiveFinish payload recursiveResult,
      Resolve afterArgument payload payload → readCell afterArgument payload = some [wanted, tail] →
      BoundedLocations afterArgument → Ident c afterArgument wanted queryId →
      Children c afterArgument tail entries → KeyedEntries c afterArgument key entries →
      afterArgument.aliases = start.aliases →
      (∀ location old, readCell start location = some old → readCell afterArgument location = some old) →
      Eval program (extend captureEnv.reverse checked.parameter (.location payload)) checked.body
        afterArgument recursiveResult recursiveFinish →
      LookupOutcome absent present afterArgument recursiveFinish recursiveResult
        (Ash.NetworkLedger.lookup key queryId entries))
    (evaluation : Eval program env checked.moreBody start result finish) :
    LookupOutcome absent present start finish result (Ash.NetworkLedger.lookup key queryId (entry :: entries)) := by
  cases entryRep with
  | child entryAddress entryResolved payload tuple _ _ entryResolution entryCell payloadResolution entryFields =>
    have projectionBound : CoreEval.lookup env checked.projectionShape.functionName = some (.location projectionAddress) := by
      simpa [checked.projectionFunctionName] using projectionBinding
    have entryBound : CoreEval.lookup env checked.projectionShape.entryName = some (.location entryAddress) := by
      simpa [checked.projectionEntryName] using entryBinding
    have childCell : readCell start entryResolved = some [.tag checked.projectionShape.child, .location payload] := by
      simpa [checked.projectionChild] using entryCell
    have projectionFresh : checked.projectionShape.functionName ≠ checked.comparisonPair.contextBinder := by
      simpa [checked.projectionFunctionName] using checked.projectionFresh
    have entryFresh : checked.projectionShape.entryName ≠ checked.comparisonPair.contextBinder := by
      simpa [checked.projectionEntryName] using checked.entryFresh
    obtain ⟨middle, selectedEval, comparisonProgress, comparisonAliases, comparisonBound, comparisonRetained⟩ :=
      removal_comparison_selects c program checked.moreBody checked.hitBody checked.recursiveCall
        checked.comparisonCall checked.comparisonFunction checked.comparisonArgument checked.projection checked.wantedNode
        checked.comparator checked.projectionShape env start finish result wanted queryId (key (.location entryAddress))
        checked.comparisonName checked.wantedName checked.comparisonPair comparisonAddress comparisonResolved
        projectionAddress projectionResolved entryAddress entryResolved payload tuple keyAddress destination checked.comparisonCallShape
        checked.comparisonFunctionShape comparisonBinding comparisonResolution comparisonCell projectionFresh entryFresh
        checked.wantedFresh checked.wantedShape projectionBound entryBound wantedBinding projectionResolution projectionCell
        entryResolution childCell payloadResolution entryFields bounded keyRep wantedRep checked.moreShape evaluation
    by_cases equal : key (.location entryAddress) = queryId
    · have comparisonTrue : Ash.NetworkLedger.CoreRemoval.compareId (key (.location entryAddress)) queryId = true :=
        (Ash.NetworkLedger.CoreRemoval.compareId_correct _ _).mpr equal
      simp only [comparisonTrue] at selectedEval
      obtain ⟨resultRep, hitProgress, hitAliases, finalBound, hitRetained⟩ :=
        checked_present_outcome program env checked.hitBody checked.hitFunction checked.hitArgument checked.hitOperand
          checked.entryName present absent checked.presentClosure checked.presentValue middle finish (.location entryAddress) result
          checked.hitShape checked.hitArgumentShape entryBinding checked.hitOperandShape checked.presentFresh
          comparisonBound selectedEval
      have aliases : finish.aliases = start.aliases := hitAliases.trans comparisonAliases
      have retained : ∀ location old, readCell start location = some old → readCell finish location = some old := by
        intro location old read
        exact hitRetained location old (comparisonRetained location old read)
      have outcome : LookupOutcome absent present start finish result (some (.location entryAddress)) :=
        ⟨resultRep, Nat.lt_trans comparisonProgress hitProgress, aliases, finalBound, retained⟩
      simpa [Ash.NetworkLedger.lookup, equal] using outcome
    · have comparisonFalse : Ash.NetworkLedger.CoreRemoval.compareId (key (.location entryAddress)) queryId = false := by
        cases compared : Ash.NetworkLedger.CoreRemoval.compareId (key (.location entryAddress)) queryId with
        | false => rfl
        | true => exact False.elim (equal ((Ash.NetworkLedger.CoreRemoval.compareId_correct _ _).mp compared))
      simp only [comparisonFalse] at selectedEval
      have selfResolution' := resolve_preserved comparisonAliases comparisonRetained selfResolution
      have selfCell' := comparisonRetained selfResolved _ selfCell
      have wantedRep' := ident_retained c start middle wanted queryId comparisonAliases comparisonRetained wantedRep
      have tailRep' := children_retained c start middle tail entries comparisonAliases comparisonRetained tailRep
      have tailKeys' := keyed_entries_retained c start middle key entries comparisonAliases comparisonRetained tailKeys
      have tailIH : ∀ afterArgument recursiveFinish payload recursiveResult,
        Resolve afterArgument payload payload → readCell afterArgument payload = some [wanted, tail] →
        BoundedLocations afterArgument → Ident c afterArgument wanted queryId →
        Children c afterArgument tail entries → KeyedEntries c afterArgument key entries →
        afterArgument.aliases = middle.aliases →
        (∀ location old, readCell middle location = some old → readCell afterArgument location = some old) →
        Eval program (extend captureEnv.reverse checked.parameter (.location payload)) checked.body
          afterArgument recursiveResult recursiveFinish →
        LookupOutcome absent present afterArgument recursiveFinish recursiveResult
          (Ash.NetworkLedger.lookup key queryId entries) := by
        intro afterArgument recursiveFinish recPayload recursiveResult recResolution recCell recBound recWanted recTail recKeys
          recAliases recRetained recEval
        apply ih afterArgument recursiveFinish recPayload recursiveResult recResolution recCell recBound recWanted recTail recKeys
          (recAliases.trans comparisonAliases) _ recEval
        intro location old read
        exact recRetained location old (comparisonRetained location old read)
      obtain ⟨resultRep, missProgress, missAliases, finalBound, missRetained⟩ :=
        lookup_miss_outcome c program absent present checked env middle finish result wanted tail entries key queryId
          selfAddress selfResolved captureValues captureEnv selfBinding wantedBinding tailBinding selfResolution' selfCell'
          captureBindings comparisonBound wantedRep' tailRep' tailKeys' tailIH selectedEval
      have aliases : finish.aliases = start.aliases := missAliases.trans comparisonAliases
      have retained : ∀ location old, readCell start location = some old → readCell finish location = some old := by
        intro location old read
        exact missRetained location old (comparisonRetained location old read)
      have outcome : LookupOutcome absent present start finish result (Ash.NetworkLedger.lookup key queryId entries) :=
        ⟨resultRep, Nat.lt_trans comparisonProgress missProgress, aliases, finalBound, retained⟩
      simpa [Ash.NetworkLedger.lookup, equal] using outcome

/-- A finite list carries exact located entries and their represented keys. -/
def RepresentedEntries (c : Constructors) (R : Store → Value → Nat → Prop)
    (store : Store) (key : Value → Id) (entries : List Value) : Prop :=
  ∀ entry ∈ entries, ∃ address keyAddress,
    entry = .location address ∧ R store entry keyAddress ∧
      Ident c store (.location keyAddress) (key entry)

/-- Retaining old cells and aliases retains every exact entry and key. -/
theorem represented_entries_retained (c : Constructors) (R : Store → Value → Nat → Prop)
    (before after : Store) (key : Value → Id) (entries : List Value)
    (relationRetained : ∀ before after entry keyAddress,
      after.aliases = before.aliases →
      (∀ location old, readCell before location = some old → readCell after location = some old) →
      R before entry keyAddress → R after entry keyAddress)
    (aliases : after.aliases = before.aliases)
    (cells : ∀ location old, readCell before location = some old → readCell after location = some old)
    (representation : RepresentedEntries c R before key entries) :
    RepresentedEntries c R after key entries := by
  intro entry member
  obtain ⟨address, keyAddress, same, entryRep, keyRep⟩ := representation entry member
  exact ⟨address, keyAddress, same, relationRetained before after entry keyAddress aliases cells entryRep,
    ident_retained c before after (.location keyAddress) (key entry) aliases cells keyRep⟩

/-- The removal function destructures the actual stored wanted/list argument. -/
theorem lookup_argument_executes (c : Constructors) (program : Program) (absent present : Constructor) (checked : CheckedLookupBase c program absent present)
    (captures : Environment) (start finish : Store) (payload payloadResolved : Nat)
    (wanted list result : Value) (queryId : Id)
    (resolution : Resolve start payload payloadResolved)
    (cell : readCell start payloadResolved = some [wanted, list])
    (wantedRep : Ident c start wanted queryId)
    (evaluation : Eval program (extend captures checked.parameter (.location payload)) checked.body start result finish) :
    Eval program
      ([(checked.wantedName, wanted), (checked.listName, list)].reverse ++
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
    checked.wantedName checked.listName checked.listBody resolution cell plain selected
  subst chosen
  subst bindings
  exact bodyEval

/-- Distinct checked binders keep helper captures and branch operands in scope. -/
theorem lookup_environment_bindings (c : Constructors) (program : Program) (absent present : Constructor) (checked : CheckedLookupBase c program absent present)
    (captures : Environment) (payload wanted list entry tail self comparison projection : Value)
    (selfBinding : CoreEval.lookup captures checked.functionName = some self)
    (comparisonBinding : CoreEval.lookup captures checked.comparisonName = some comparison)
    (projectionBinding : CoreEval.lookup captures checked.projectionName = some projection) :
    let arguments := [(checked.listName, list), (checked.wantedName, wanted), (checked.parameter, payload)] ++ captures
    let more := [(checked.tailName, tail), (checked.entryName, entry)] ++ arguments
    CoreEval.lookup arguments checked.listName = some list ∧
    CoreEval.lookup more checked.wantedName = some wanted ∧
    CoreEval.lookup more checked.entryName = some entry ∧
    CoreEval.lookup more checked.tailName = some tail ∧
    CoreEval.lookup more checked.functionName = some self ∧
    CoreEval.lookup more checked.comparisonName = some comparison ∧
    CoreEval.lookup more checked.projectionName = some projection := by
  have distinct := checked.distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_false_eq_true, not_or] at distinct
  rcases distinct with ⟨⟨hpw, hpl, hpe, hpt, hps, hpc, hpp⟩,
    ⟨hwl, hwe, hwt, hws, hwc, hwp⟩, ⟨hle, hlt, hls, hlc, hlp⟩,
    ⟨het, hes, hec, hep⟩, ⟨hts, htc, htp⟩, ⟨hsc, hsp⟩, hcp⟩
  have selfAbsent : checked.functionName ∉
      [checked.tailName, checked.entryName, checked.listName, checked.wantedName, checked.parameter] := by
    simp [Ne.symm hts, Ne.symm hes, Ne.symm hls, Ne.symm hws, Ne.symm hps]
  have comparisonAbsent : checked.comparisonName ∉
      [checked.tailName, checked.entryName, checked.listName, checked.wantedName, checked.parameter] := by
    simp [Ne.symm htc, Ne.symm hec, Ne.symm hlc, Ne.symm hwc, Ne.symm hpc]
  have projectionAbsent : checked.projectionName ∉
      [checked.tailName, checked.entryName, checked.listName, checked.wantedName, checked.parameter] := by
    simp [Ne.symm htp, Ne.symm hep, Ne.symm hlp, Ne.symm hwp, Ne.symm hpp]
  have wantedAbsent : checked.wantedName ∉
      [checked.tailName, checked.entryName, checked.listName] := by simp [hwt, hwe, hwl]
  have entryAbsent : checked.entryName ∉ [checked.tailName] := by simp [het]
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [CoreEval.lookup]
  · have same := lookup_unshadowed_prefix
      [(checked.tailName, tail), (checked.entryName, entry), (checked.listName, list)]
      ([(checked.wantedName, wanted), (checked.parameter, payload)] ++ captures) checked.wantedName (by simpa using wantedAbsent)
    simpa [CoreEval.lookup] using same
  · have same := lookup_unshadowed_prefix [(checked.tailName, tail)]
      ([(checked.entryName, entry), (checked.listName, list), (checked.wantedName, wanted), (checked.parameter, payload)] ++ captures)
      checked.entryName (by simpa using entryAbsent)
    simpa [CoreEval.lookup] using same
  · simp [CoreEval.lookup]
  · have same := lookup_unshadowed_prefix
      [(checked.tailName, tail), (checked.entryName, entry), (checked.listName, list),
       (checked.wantedName, wanted), (checked.parameter, payload)] captures checked.functionName (by simpa using selfAbsent)
    exact same.trans selfBinding
  · have same := lookup_unshadowed_prefix
      [(checked.tailName, tail), (checked.entryName, entry), (checked.listName, list),
       (checked.wantedName, wanted), (checked.parameter, payload)] captures checked.comparisonName (by simpa using comparisonAbsent)
    exact same.trans comparisonBinding
  · have same := lookup_unshadowed_prefix
      [(checked.tailName, tail), (checked.entryName, entry), (checked.listName, list),
       (checked.wantedName, wanted), (checked.parameter, payload)] captures checked.projectionName (by simpa using projectionAbsent)
    exact same.trans projectionBinding



/-- Finite lookup with a concrete, retained entry relation and projection law. -/
theorem lookup_body_correct_with (c : Constructors) (program : Program) (absent present : Constructor)
    (checked : CheckedLookupBase c program absent present)
    (R : Store → Value → Nat → Prop)
    (relationRetained : ∀ before after entry keyAddress,
      after.aliases = before.aliases →
      (∀ location old, readCell before location = some old → readCell after location = some old) →
      R before entry keyAddress → R after entry keyAddress)
    (captureValues : List Value) (captureEnv : Environment)
    (selfAddress selfResolved comparisonAddress comparisonResolved projectionAddress projectionResolved : Nat)
    (wanted : Value) (queryId : Id) (key : Value → Id) (entries : List Value)
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
      Resolve start payload payloadResolved → readCell start payloadResolved = some [wanted, list] →
      BoundedLocations start → Ident c start wanted queryId → Children c start list entries →
      RepresentedEntries c R start key entries →
      Resolve start selfAddress selfResolved →
      readCell start selfResolved = some (.closureCode checked.code :: captureValues) →
      Resolve start comparisonAddress comparisonResolved →
      readCell start comparisonResolved = some [.closureCode checked.comparator.code] →
      Resolve start projectionAddress projectionResolved →
      readCell start projectionResolved = some [.closureCode checked.projectionCode] →
      Eval program (extend captureEnv.reverse checked.parameter (.location payload)) checked.body start result finish →
      LookupOutcome absent present start finish result (Ash.NetworkLedger.lookup key queryId entries) := by
  induction entries with
  | nil =>
    intro start finish payload payloadResolved list result payloadResolution payloadCell bounded wantedRep listRep keys
      selfResolution selfCell comparisonResolution comparisonCell projectionResolution projectionCell evaluation
    have listEval := lookup_argument_executes c program absent present checked captureEnv.reverse start finish payload payloadResolved
      wanted list result queryId payloadResolution payloadCell wantedRep evaluation
    have scope := lookup_environment_bindings c program absent present checked captureEnv.reverse (.location payload) wanted list
      .unit .unit (.location selfAddress) (.location comparisonAddress) (.location projectionAddress)
      selfBinding comparisonBinding projectionBinding
    simpa [Ash.NetworkLedger.lookup] using
      lookup_empty_outcome c program _ checked.listBody checked.listScrutinee checked.emptyBody checked.moreBody
        checked.listName checked.entryName checked.tailName absent start finish list result checked.listShape
        checked.listVariableShape scope.1 checked.absentValue bounded listRep listEval present
  | cons entry entries ih =>
    intro start finish payload payloadResolved list result payloadResolution payloadCell bounded wantedRep listRep keys
      selfResolution selfCell comparisonResolution comparisonCell projectionResolution projectionCell evaluation
    have listEval := lookup_argument_executes c program absent present checked captureEnv.reverse start finish payload payloadResolved
      wanted list result queryId payloadResolution payloadCell wantedRep evaluation
    obtain ⟨entryAddress, keyAddress, entryEq, entryRep, keyRep⟩ := keys entry (by simp)
    subst entry
    cases listRep with
    | more listAddress listResolved listPayload listTuple _ tail _ listResolution listCell listPayloadResolution listFields tailRep =>
      have scope := lookup_environment_bindings c program absent present checked captureEnv.reverse (.location payload) wanted (.location listAddress)
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
        Resolve afterArgument recPayload recPayload → readCell afterArgument recPayload = some [wanted, tail] →
        BoundedLocations afterArgument → Ident c afterArgument wanted queryId →
        Children c afterArgument tail entries → RepresentedEntries c R afterArgument key entries →
        afterArgument.aliases = start.aliases →
        (∀ location old, readCell start location = some old → readCell afterArgument location = some old) →
        Eval program (extend captureEnv.reverse checked.parameter (.location recPayload)) checked.body
          afterArgument recursiveResult recursiveFinish →
        LookupOutcome absent present afterArgument recursiveFinish recursiveResult
          (Ash.NetworkLedger.lookup key queryId entries) := by
        intro afterArgument recursiveFinish recPayload recursiveResult recResolution recCell recBound recWanted recTail recKeys
          recAliases recRetained recEval
        apply ih afterArgument recursiveFinish recPayload recPayload tail recursiveResult recResolution recCell recBound
          recWanted recTail recKeys (resolve_preserved recAliases recRetained selfResolution)
          (recRetained selfResolved _ selfCell) (resolve_preserved recAliases recRetained comparisonResolution)
          (recRetained comparisonResolved _ comparisonCell) (resolve_preserved recAliases recRetained projectionResolution)
          (recRetained projectionResolved _ projectionCell) recEval
      have law := projectionFor _ start entryAddress keyAddress entryRep scope.2.2.2.2.2.2 scope.2.2.1
        projectionResolution projectionCell
      exact lookup_more_outcome_with c program absent present checked _ start finish result wanted tail entryAddress entries key
        queryId selfAddress selfResolved comparisonAddress comparisonResolved keyAddress captureValues captureEnv
        scope.2.2.2.2.1 scope.2.2.2.2.2.1 scope.2.2.1 scope.2.1 scope.2.2.2.1
        selfResolution selfCell captureBindings comparisonResolution comparisonCell law keyRep wantedRep tailRep
        (fun store => RepresentedEntries c R store key entries) tailKeys
        (fun before after aliases cells reps => represented_entries_retained c R before after key entries
          relationRetained aliases cells reps) bounded tailIH moreEval



/-- A Child entry retains its entire destination as well as its key. -/
def ChildEntry (c : Constructors) (store : Store) (entry : Value) (keyAddress : Nat) : Prop :=
  ∃ destination, Entry c store entry (.location keyAddress) destination

/-- The Child specialization preserves its original whole entry. -/
theorem child_entry_retained (c : Constructors) (before after : Store) (entry : Value) (keyAddress : Nat)
    (aliases : after.aliases = before.aliases)
    (cells : ∀ location old, readCell before location = some old → readCell after location = some old)
    (entryRep : ChildEntry c before entry keyAddress) : ChildEntry c after entry keyAddress := by
  obtain ⟨destination, represented⟩ := entryRep
  exact ⟨destination, entry_retained c before after entry (.location keyAddress) destination aliases cells represented⟩

/-- Every normal execution returns the first matching original whole entry. -/
theorem lookup_body_correct (c : Constructors) (program : Program) (absent present : Constructor)
    (checked : CheckedLookup c program absent present)
    (captureValues : List Value) (captureEnv : Environment)
    (selfAddress selfResolved comparisonAddress comparisonResolved projectionAddress projectionResolved : Nat)
    (wanted : Value) (queryId : Id) (key : Value → Id) (entries : List Value)
    (selfBinding : CoreEval.lookup captureEnv.reverse checked.functionName = some (.location selfAddress))
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
      LookupOutcome absent present start finish result (Ash.NetworkLedger.lookup key queryId entries) := by
  have projectionFor : ∀ env start entryAddress keyAddress,
      ChildEntry c start (.location entryAddress) keyAddress →
      CoreEval.lookup env checked.projectionName = some (.location projectionAddress) →
      CoreEval.lookup env checked.entryName = some (.location entryAddress) →
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
  have represented : RepresentedEntries c (ChildEntry c) start key entries := by
    intro entry member
    obtain ⟨keyAddress, destination, entryRep, keyRep⟩ := keys entry member
    cases entryRep with
    | child address resolved entryPayload tuple _ _ resolution cell payloadResolution fields =>
      exact ⟨address, keyAddress, rfl, ⟨destination, Entry.child address resolved entryPayload tuple
        (.location keyAddress) destination resolution cell payloadResolution fields⟩, keyRep⟩
  have projectionCell' : readCell start projectionResolved = some [.closureCode checked.projectionCode] := by
    simpa [checked.projectionCodeShape] using projectionCell
  exact lookup_body_correct_with c program absent present checked.toCheckedLookupBase (ChildEntry c)
    (child_entry_retained c) captureValues captureEnv selfAddress selfResolved comparisonAddress comparisonResolved
    projectionAddress projectionResolved wanted queryId key entries selfBinding comparisonBinding projectionBinding
    captureBindings projectionFor start finish payload payloadResolved list result payloadResolution payloadCell bounded
    wantedRep listRep represented selfResolution selfCell comparisonResolution comparisonCell projectionResolution
    projectionCell' evaluation


end Ash.NetworkLedger.CoreLookup
