import NetworkLedgerCoreValues

/-
Normal-return correspondence for ordered insertion in the finite ordinary
child list. This models the real closure, field order and allocation nodes.
Actual provider selection, input finiteness and the validated Rust arena's
mapping remain separate premises and no fact is published by this file.
-/
namespace Ash.NetworkLedger.CoreInsert

open Ash.NetworkLedger
open Ash.NetworkLedger.CoreRegion
open Ash.NetworkLedger.CoreEval
open Ash.NetworkLedger.CoreValues

/-- Successful insertion keeps the exact old entries and appends the new one. -/
def InsertOutcome (c : Constructors) (start finish : Store) (result : Value)
    (entries : List Value) : Prop :=
  Children c finish result entries ∧ start.nextLocation < finish.nextLocation ∧
  finish.aliases = start.aliases ∧ BoundedLocations finish ∧
  (∀ address old, readCell start address = some old → readCell finish address = some old)

/-- The checked body carries actual constructor and recursive-call coordinates. -/
structure CheckedInsert (c : Constructors) (program : Program) where
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
  singletonFunction : NodeId
  singletonArgument : NodeId
  singletonEntry : NodeId
  singletonEmpty : NodeId
  prependFunction : NodeId
  prependArgument : NodeId
  prependEntry : NodeId
  recursiveCall : NodeId
  recursiveFunction : NodeId
  recursiveArgument : NodeId
  recursiveEntry : NodeId
  recursiveTail : NodeId
  singletonOperand : NodeId
  prependOperand : NodeId
  newName : Binder
  listName : Binder
  entryName : Binder
  tailName : Binder
  functionName : Binder
  singletonClosure : CheckedClosure program singletonFunction
  singletonPair : CheckedTuple program singletonArgument none [singletonEntry, singletonEmpty]
  singletonValue : CheckedTuple program singletonClosure.body (some c.more) [singletonOperand]
  emptyValue : CheckedTuple program singletonEmpty (some c.empty) []
  prependClosure : CheckedClosure program prependFunction
  prependPair : CheckedTuple program prependArgument none [prependEntry, recursiveCall]
  prependValue : CheckedTuple program prependClosure.body (some c.more) [prependOperand]
  recursivePair : CheckedTuple program recursiveArgument none [recursiveEntry, recursiveTail]
  closureShape : program code = some (.closure context captureNodes storage parameter body)
  bodyShape : program body = some (.caseMatch argumentScrutinee
    [(.tuple [.binder newName, .binder listName], listBody)])
  argumentShape : program argumentScrutinee = some (.variable parameter)
  listShape : program listBody = some (.caseMatch listScrutinee
    [(.constructor c.empty none, emptyBody),
     (.constructor c.more (some (.tuple [.binder entryName, .binder tailName])), moreBody)])
  listVariableShape : program listScrutinee = some (.variable listName)
  singletonShape : program emptyBody = some (.apply singletonFunction singletonArgument)
  singletonEntryShape : program singletonEntry = some (.variable newName)
  singletonOperandShape : program singletonOperand = some (.variable singletonClosure.parameter)
  prependShape : program moreBody = some (.apply prependFunction prependArgument)
  prependEntryShape : program prependEntry = some (.variable entryName)
  prependOperandShape : program prependOperand = some (.variable prependClosure.parameter)
  recursiveShape : program recursiveCall = some (.apply recursiveFunction recursiveArgument)
  recursiveFunctionShape : program recursiveFunction = some (.variable functionName)
  recursiveEntryShape : program recursiveEntry = some (.variable newName)
  recursiveTailShape : program recursiveTail = some (.variable tailName)
  singletonEntryFresh : newName ≠ singletonPair.contextBinder
  singletonOperandFresh : singletonClosure.parameter ≠ singletonValue.contextBinder
  prependEntryFresh : entryName ≠ prependPair.contextBinder
  recursiveFunctionFresh : functionName ≠ prependPair.contextBinder
  recursiveEntryInPrependFresh : newName ≠ prependPair.contextBinder
  recursiveTailInPrependFresh : tailName ≠ prependPair.contextBinder
  prependOperandFresh : prependClosure.parameter ≠ prependValue.contextBinder
  recursiveEntryFresh : newName ≠ recursivePair.contextBinder
  recursiveTailFresh : tailName ≠ recursivePair.contextBinder
  distinct : [parameter, newName, listName, entryName, tailName, functionName].Nodup


/-- A More constructor evaluates the left entry, then the checked tail computation. -/
theorem checked_prepend_outcome (c : Constructors) (program : Program)
    (call function argument entryNode tailNode operand : NodeId)
    (closure : CheckedClosure program function)
    (pair : CheckedTuple program argument none [entryNode, tailNode])
    (constructor : CheckedTuple program closure.body (some c.more) [operand])
    (env : Environment) (start finish : Store) (result entry : Value) (entries : List Value)
    (entryName : Binder)
    (callShape : program call = some (.apply function argument))
    (entryShape : program entryNode = some (.variable entryName))
    (entryFresh : entryName ≠ pair.contextBinder)
    (entryBinding : CoreEval.lookup env entryName = some entry)
    (operandShape : program operand = some (.variable closure.parameter))
    (operandFresh : closure.parameter ≠ constructor.contextBinder)
    (bounded : BoundedLocations start)
    (tailCorrect : ∀ before after tail,
      BoundedLocations before → before.aliases = start.aliases →
      (∀ address old, readCell start address = some old → readCell before address = some old) →
      Eval program (extend env pair.contextBinder .context) tailNode before tail after →
      Children c after tail entries ∧ after.aliases = before.aliases ∧ BoundedLocations after ∧
      (∀ address old, readCell before address = some old → readCell after address = some old))
    (evaluation : Eval program env call start result finish) :
    InsertOutcome c start finish result (entry :: entries) := by
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
  obtain ⟨queried, afterFields, afterAlloc, pairAddress, values, queryStep, fieldEvals,
    allocated, initialized, pairEq⟩ := checked_tuple_inversion pair argumentEval
  obtain ⟨middle, actualEntry, actualTail, entryEval, tailEval, sameValues⟩ :=
    pair_fields_inversion fieldEvals
  obtain ⟨actualBinding, sameStore⟩ := variable_inversion entryShape entryEval
  have entryBound : CoreEval.lookup (extend env pair.contextBinder .context) entryName = some entry := by
    rw [lookup_extended_other env pair.contextBinder entryName entryFresh]
    exact entryBinding
  have sameEntry := Option.some.inj (actualBinding.symm.trans entryBound)
  subst middle
  subst actualEntry
  subst values
  have queryBound := query_preserves_bounded afterFunction queried .hostDefault .hostDefault closureBound queryStep
  have queryAliases : queried.aliases = start.aliases := by
    have same : queried.aliases = afterFunction.aliases := by
      simp only [query, Option.some.injEq, Prod.mk.injEq] at queryStep
      rcases queryStep with ⟨_, rfl⟩
      rfl
    exact same.trans closureAliases
  have queryRetained : ∀ address old, readCell start address = some old → readCell queried address = some old := by
    intro address old read
    exact query_preserves_cell queryStep (closureRetained address old read)
  obtain ⟨tailRep, tailAliases, tailBound, tailRetained⟩ :=
    tailCorrect queried afterFields actualTail queryBound queryAliases queryRetained tailEval
  have allocatePair : allocate .hostDefault ([entry, actualTail] : List Value).length true afterFields =
      some (pairAddress, afterAlloc) := by simpa using allocated
  have initializePair : initializeStorage pairAddress ([entry, actualTail] : List Value).length
      [entry, actualTail] afterAlloc = some ([entry, actualTail], afterArgument) := by
    simpa [storedFields] using initialized
  obtain ⟨pairFresh, _, pairCell, pairAliases, pairBound, pairRetained⟩ :=
    host_allocation_retains tailBound allocatePair initializePair
  subst argumentValue
  have operandBinding : CoreEval.lookup (extend [] closure.parameter (.location pairAddress)) closure.parameter =
      some (.location pairAddress) := by simp [CoreEval.lookup, extend]
  obtain ⟨listAddress, resultEq, listFresh, _, listCell, listAliases, finalBound, listRetained⟩ :=
    checked_unary_constructor_retains constructor closure.parameter operandShape operandFresh operandBinding
      pairBound bodyEval
  have aliases : finish.aliases = start.aliases :=
    listAliases.trans (pairAliases.trans (tailAliases.trans queryAliases))
  have retained : ∀ address old, readCell start address = some old → readCell finish address = some old := by
    intro address old read
    exact listRetained address old (pairRetained address old (tailRetained address old (queryRetained address old read)))
  have listNoAlias : readAlias finish listAddress = none := by
    simpa [readAlias, listAliases, listFresh] using bounded_fresh_no_alias afterArgument pairBound
  have pairNoAlias : readAlias finish pairAddress = none := by
    simpa [readAlias, listAliases, pairAliases, pairFresh] using bounded_fresh_no_alias afterFields tailBound
  have finalPair := listRetained pairAddress _ pairCell
  have tailFinal := children_retained c afterFields finish actualTail entries
    (listAliases.trans pairAliases) (fun address old read => listRetained address old (pairRetained address old read)) tailRep
  have listRep : Children c finish result (entry :: entries) := by
    rw [resultEq]
    exact Children.more listAddress listAddress pairAddress pairAddress entry actualTail entries
      (Resolve.cell listAddress [.tag c.more, .location pairAddress] listNoAlias listCell) listCell
      (Resolve.cell pairAddress [entry, actualTail] pairNoAlias finalPair) finalPair tailFinal
  have progress : start.nextLocation < finish.nextLocation := by
    have live := finalBound.2.1 closureLocation _
      (readCell_member finish closureLocation _
        (listRetained closureLocation _ (pairRetained closureLocation _
          (tailRetained closureLocation _ (query_preserves_cell queryStep closureCell)))))
    rw [closureFresh] at live
    exact live
  exact ⟨listRep, progress, aliases, finalBound, retained⟩


/-- Inserting into Empty evaluates the real Empty operand and appends the new entry. -/
theorem insertion_empty_outcome (c : Constructors) (program : Program) (checked : CheckedInsert c program)
    (env : Environment) (start finish : Store) (result newEntry : Value)
    (newBinding : CoreEval.lookup env checked.newName = some newEntry)
    (bounded : BoundedLocations start)
    (evaluation : Eval program env checked.emptyBody start result finish) :
    InsertOutcome c start finish result [newEntry] := by
  have tailCorrect : ∀ before after tail,
      BoundedLocations before → before.aliases = start.aliases →
      (∀ address old, readCell start address = some old → readCell before address = some old) →
      Eval program (extend env checked.singletonPair.contextBinder .context) checked.singletonEmpty before tail after →
      Children c after tail [] ∧ after.aliases = before.aliases ∧ BoundedLocations after ∧
      (∀ address old, readCell before address = some old → readCell after address = some old) := by
    intro before after tail beforeBound _ _ tailEval
    obtain ⟨location, resultEq, fresh, _, cell, aliases, afterBound, retained⟩ :=
      checked_nullary_retains checked.emptyValue beforeBound tailEval
    have noAlias : readAlias after location = none := by
      simpa [readAlias, aliases, fresh] using bounded_fresh_no_alias before beforeBound
    have tailRep : Children c after tail [] := by
      rw [resultEq]
      exact Children.empty location location (Resolve.cell location [.tag c.empty] noAlias cell) cell
    exact ⟨tailRep, aliases, afterBound, retained⟩
  simpa using checked_prepend_outcome c program checked.emptyBody checked.singletonFunction
    checked.singletonArgument checked.singletonEntry checked.singletonEmpty checked.singletonOperand
    checked.singletonClosure checked.singletonPair checked.singletonValue env start finish result newEntry []
    checked.newName checked.singletonShape checked.singletonEntryShape checked.singletonEntryFresh newBinding
    checked.singletonOperandShape checked.singletonOperandFresh bounded tailCorrect evaluation


/-- In the More arm the recursive call receives the original new value and tail. -/
theorem insertion_more_outcome (c : Constructors) (program : Program) (checked : CheckedInsert c program)
    (env : Environment) (start finish : Store) (result entry newEntry tail : Value) (entries : List Value)
    (selfAddress selfResolved : Nat) (captureValues : List Value) (captureEnv : Environment)
    (entryBinding : CoreEval.lookup env checked.entryName = some entry)
    (newBinding : CoreEval.lookup env checked.newName = some newEntry)
    (tailBinding : CoreEval.lookup env checked.tailName = some tail)
    (selfBinding : CoreEval.lookup env checked.functionName = some (.location selfAddress))
    (selfResolution : Resolve start selfAddress selfResolved)
    (selfCell : readCell start selfResolved = some (.closureCode checked.code :: captureValues))
    (captureBindings : CaptureBindings program checked.captureNodes captureValues captureEnv)
    (bounded : BoundedLocations start) (tailRep : Children c start tail entries)
    (ih : ∀ afterArgument recursiveFinish payload recursiveResult,
      Resolve afterArgument payload payload → readCell afterArgument payload = some [newEntry, tail] →
      BoundedLocations afterArgument → Children c afterArgument tail entries →
      afterArgument.aliases = start.aliases →
      (∀ location old, readCell start location = some old → readCell afterArgument location = some old) →
      Eval program (extend captureEnv.reverse checked.parameter (.location payload)) checked.body
        afterArgument recursiveResult recursiveFinish →
      InsertOutcome c afterArgument recursiveFinish recursiveResult (entries ++ [newEntry]))
    (evaluation : Eval program env checked.moreBody start result finish) :
    InsertOutcome c start finish result (entry :: (entries ++ [newEntry])) := by
  have tailCorrect : ∀ before after remaining,
      BoundedLocations before → before.aliases = start.aliases →
      (∀ address old, readCell start address = some old → readCell before address = some old) →
      Eval program (extend env checked.prependPair.contextBinder .context) checked.recursiveCall before remaining after →
      Children c after remaining (entries ++ [newEntry]) ∧ after.aliases = before.aliases ∧ BoundedLocations after ∧
      (∀ address old, readCell before address = some old → readCell after address = some old) := by
    intro before after remaining beforeBound beforeAliases beforeRetained recursiveEval
    have selfBound : CoreEval.lookup (extend env checked.prependPair.contextBinder .context) checked.functionName =
        some (.location selfAddress) := by
      rw [lookup_extended_other env checked.prependPair.contextBinder checked.functionName checked.recursiveFunctionFresh]
      exact selfBinding
    have newBound : CoreEval.lookup (extend env checked.prependPair.contextBinder .context) checked.newName = some newEntry := by
      rw [lookup_extended_other env checked.prependPair.contextBinder checked.newName checked.recursiveEntryInPrependFresh]
      exact newBinding
    have tailBound : CoreEval.lookup (extend env checked.prependPair.contextBinder .context) checked.tailName = some tail := by
      rw [lookup_extended_other env checked.prependPair.contextBinder checked.tailName checked.recursiveTailInPrependFresh]
      exact tailBinding
    have selfResolution' := resolve_preserved beforeAliases beforeRetained selfResolution
    have selfCell' := beforeRetained selfResolved _ selfCell
    obtain ⟨afterArgument, payload, bodyEval, payloadResolution, payloadCell, _, argumentAliases,
      argumentBound, argumentRetained⟩ :=
      checked_recursive_call program checked.recursiveCall checked.recursiveFunction checked.recursiveArgument
        checked.recursiveEntry checked.recursiveTail _ before after remaining newEntry tail checked.functionName
        checked.newName checked.tailName selfAddress selfResolved checked.code checked.context checked.storage
        checked.parameter checked.body checked.captureNodes captureValues captureEnv checked.recursivePair
        checked.recursiveShape checked.recursiveFunctionShape selfBound selfResolution' selfCell' checked.closureShape
        captureBindings checked.recursiveEntryShape checked.recursiveTailShape checked.recursiveEntryFresh
        checked.recursiveTailFresh newBound tailBound beforeBound recursiveEval
    have tailAfter := children_retained c start afterArgument tail entries (argumentAliases.trans beforeAliases)
      (fun address old read => argumentRetained address old (beforeRetained address old read)) tailRep
    obtain ⟨resultRep, _, recursiveAliases, finalBound, recursiveRetained⟩ :=
      ih afterArgument after payload remaining payloadResolution payloadCell argumentBound tailAfter
        (argumentAliases.trans beforeAliases)
        (fun address old read => argumentRetained address old (beforeRetained address old read)) bodyEval
    exact ⟨resultRep, recursiveAliases.trans argumentAliases, finalBound,
      fun address old read => recursiveRetained address old (argumentRetained address old read)⟩
  exact checked_prepend_outcome c program checked.moreBody checked.prependFunction checked.prependArgument
    checked.prependEntry checked.recursiveCall checked.prependOperand checked.prependClosure checked.prependPair
    checked.prependValue env start finish result entry (entries ++ [newEntry]) checked.entryName checked.prependShape
    checked.prependEntryShape checked.prependEntryFresh entryBinding checked.prependOperandShape checked.prependOperandFresh
    bounded tailCorrect evaluation


/-- The actual pair argument is destructured before the list is matched. -/
theorem insertion_argument_executes (c : Constructors) (program : Program) (checked : CheckedInsert c program)
    (captures : Environment) (start finish : Store) (payload payloadResolved : Nat)
    (newEntry list result : Value) (newAddress : Nat) (newLocation : newEntry = .location newAddress)
    (resolution : Resolve start payload payloadResolved)
    (cell : readCell start payloadResolved = some [newEntry, list])
    (evaluation : Eval program (extend captures checked.parameter (.location payload)) checked.body start result finish) :
    Eval program
      ([(checked.newName, newEntry), (checked.listName, list)].reverse ++
        extend captures checked.parameter (.location payload)) checked.listBody start result finish := by
  obtain ⟨middle, actual, chosen, bindings, argumentEval, selected, bodyEval⟩ :=
    case_match_inversion checked.bodyShape evaluation
  obtain ⟨actualBinding, sameStore⟩ := variable_inversion checked.argumentShape argumentEval
  have sameValue : actual = .location payload := by simpa [CoreEval.lookup, extend] using actualBinding.symm
  subst actual
  subst middle
  have plain : tupleFields [newEntry, list] = some [newEntry, list] := by rw [newLocation]; rfl
  obtain ⟨sameBody, sameBindings⟩ := pair_selects_single start payload payloadResolved newEntry list
    checked.newName checked.listName checked.listBody resolution cell plain selected
  subst chosen
  subst bindings
  exact bodyEval

/-- Distinct actual binders retain the closure and operands through both matches. -/
theorem insertion_environment_bindings (c : Constructors) (program : Program) (checked : CheckedInsert c program)
    (captures : Environment) (payload newEntry list entry tail self : Value)
    (selfBinding : CoreEval.lookup captures checked.functionName = some self) :
    let arguments := [(checked.listName, list), (checked.newName, newEntry), (checked.parameter, payload)] ++ captures
    let more := [(checked.tailName, tail), (checked.entryName, entry)] ++ arguments
    CoreEval.lookup arguments checked.listName = some list ∧
    CoreEval.lookup arguments checked.newName = some newEntry ∧
    CoreEval.lookup more checked.newName = some newEntry ∧
    CoreEval.lookup more checked.entryName = some entry ∧
    CoreEval.lookup more checked.tailName = some tail ∧
    CoreEval.lookup more checked.functionName = some self := by
  have distinct := checked.distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_false_eq_true, not_or] at distinct
  rcases distinct with ⟨⟨hpn, hpl, hpe, hpt, hps⟩,
    ⟨hnl, hne, hnt, hns⟩, ⟨hle, hlt, hls⟩, ⟨het, hes⟩, ⟨hts, _, _⟩⟩
  have selfAbsent : checked.functionName ∉
      [checked.tailName, checked.entryName, checked.listName, checked.newName, checked.parameter] := by
    simp [Ne.symm hts, Ne.symm hes, Ne.symm hls, Ne.symm hns, Ne.symm hps]
  have newAbsent : checked.newName ∉ [checked.tailName, checked.entryName, checked.listName] := by
    simp [hnt, hne, hnl]
  have entryAbsent : checked.entryName ∉ [checked.tailName] := by simp [het]
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [CoreEval.lookup]
  · have same := lookup_unshadowed_prefix [(checked.listName, list)]
      ([(checked.newName, newEntry), (checked.parameter, payload)] ++ captures) checked.newName (by simpa using hnl)
    simpa [CoreEval.lookup] using same
  · have same := lookup_unshadowed_prefix
      [(checked.tailName, tail), (checked.entryName, entry), (checked.listName, list)]
      ([(checked.newName, newEntry), (checked.parameter, payload)] ++ captures) checked.newName (by simpa using newAbsent)
    simpa [CoreEval.lookup] using same
  · have same := lookup_unshadowed_prefix [(checked.tailName, tail)]
      ([(checked.entryName, entry), (checked.listName, list), (checked.newName, newEntry), (checked.parameter, payload)] ++ captures)
      checked.entryName (by simpa using entryAbsent)
    simpa [CoreEval.lookup] using same
  · simp [CoreEval.lookup]
  · have same := lookup_unshadowed_prefix
      [(checked.tailName, tail), (checked.entryName, entry), (checked.listName, list),
       (checked.newName, newEntry), (checked.parameter, payload)] captures checked.functionName (by simpa using selfAbsent)
    exact same.trans selfBinding


/-- Every normal execution appends the exact new entry to the represented finite list. -/
theorem insertion_body_correct (c : Constructors) (program : Program) (checked : CheckedInsert c program)
    (captureValues : List Value) (captureEnv : Environment) (selfAddress selfResolved : Nat)
    (newEntry : Value) (newAddress : Nat) (newLocation : newEntry = .location newAddress)
    (key : Value → Id) (entries : List Value)
    (selfBinding : CoreEval.lookup captureEnv.reverse checked.functionName = some (.location selfAddress))
    (captureBindings : CaptureBindings program checked.captureNodes captureValues captureEnv) :
    ∀ start finish payload payloadResolved list result,
      Resolve start payload payloadResolved → readCell start payloadResolved = some [newEntry, list] →
      BoundedLocations start → Children c start list entries → KeyedEntries c start key entries →
      Resolve start selfAddress selfResolved →
      readCell start selfResolved = some (.closureCode checked.code :: captureValues) →
      Eval program (extend captureEnv.reverse checked.parameter (.location payload)) checked.body start result finish →
      InsertOutcome c start finish result (entries ++ [newEntry]) := by
  induction entries with
  | nil =>
    intro start finish payload payloadResolved list result payloadResolution payloadCell bounded listRep keys
      selfResolution selfCell evaluation
    have listEval := insertion_argument_executes c program checked captureEnv.reverse start finish payload payloadResolved
      newEntry list result newAddress newLocation payloadResolution payloadCell evaluation
    have scope := insertion_environment_bindings c program checked captureEnv.reverse (.location payload) newEntry list
      .unit .unit (.location selfAddress) selfBinding
    cases listRep with
    | empty address resolved resolution cell =>
      have emptyEval := empty_match_executes_first program start finish _ checked.listBody checked.listScrutinee
        checked.listName c.empty c.more checked.emptyBody checked.moreBody (.tuple [.binder checked.entryName, .binder checked.tailName])
        address resolved result checked.listShape checked.listVariableShape scope.1 resolution cell listEval
      simpa using insertion_empty_outcome c program checked _ start finish result newEntry scope.2.1 bounded emptyEval
  | cons entry entries ih =>
    intro start finish payload payloadResolved list result payloadResolution payloadCell bounded listRep keys
      selfResolution selfCell evaluation
    have listEval := insertion_argument_executes c program checked captureEnv.reverse start finish payload payloadResolved
      newEntry list result newAddress newLocation payloadResolution payloadCell evaluation
    obtain ⟨keyAddress, destination, entryRep, keyRep⟩ := keys entry (by simp)
    cases entryRep with
    | child entryAddress entryResolved childPayload childTuple _ _ entryResolution entryCell childResolution childFields =>
      cases listRep with
      | more listAddress listResolved listPayload listTuple _ tail _ listResolution listCell listPayloadResolution listFields tailRep =>
        have scope := insertion_environment_bindings c program checked captureEnv.reverse (.location payload) newEntry (.location listAddress)
          (.location entryAddress) tail (.location selfAddress) selfBinding
        have moreEval := more_match_executes_second program start finish _ checked.listBody checked.listScrutinee
          checked.listName c.empty c.more checked.emptyBody checked.moreBody checked.entryName checked.tailName
          listAddress listResolved listPayload listTuple entryAddress tail result checked.listShape checked.listVariableShape
          scope.1 listResolution listCell listPayloadResolution listFields listEval
        have tailKeys : KeyedEntries c start key entries := by
          intro other member
          exact keys other (by simp [member])
        have tailIH : ∀ afterArgument recursiveFinish recPayload recursiveResult,
          Resolve afterArgument recPayload recPayload → readCell afterArgument recPayload = some [newEntry, tail] →
          BoundedLocations afterArgument → Children c afterArgument tail entries →
          afterArgument.aliases = start.aliases →
          (∀ location old, readCell start location = some old → readCell afterArgument location = some old) →
          Eval program (extend captureEnv.reverse checked.parameter (.location recPayload)) checked.body
            afterArgument recursiveResult recursiveFinish →
          InsertOutcome c afterArgument recursiveFinish recursiveResult (entries ++ [newEntry]) := by
          intro afterArgument recursiveFinish recPayload recursiveResult recResolution recCell recBound recTail
            recAliases recRetained recEval
          have recKeys := keyed_entries_retained c start afterArgument key entries recAliases recRetained tailKeys
          exact ih afterArgument recursiveFinish recPayload recPayload tail recursiveResult recResolution recCell recBound
            recTail recKeys (resolve_preserved recAliases recRetained selfResolution)
            (recRetained selfResolved _ selfCell) recEval
        simpa using insertion_more_outcome c program checked _ start finish result (.location entryAddress) newEntry tail entries
          selfAddress selfResolved captureValues captureEnv scope.2.2.2.1 scope.2.2.1 scope.2.2.2.2.1 scope.2.2.2.2.2
          selfResolution selfCell captureBindings bounded tailRep tailIH moreEval

end Ash.NetworkLedger.CoreInsert
