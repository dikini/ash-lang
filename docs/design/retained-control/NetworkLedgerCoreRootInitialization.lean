import NetworkLedgerCoreInitialization

/- The root initialization path constructs its record fields in order before
   assembling the singleton record list. Normal-return reasoning is conditional
   on the checked modeled graph and selected default provider. -/
namespace Ash.NetworkLedger.CoreRootInitialization

open Ash.NetworkLedger.CoreEval
open Ash.NetworkLedger.CoreRegion
open Ash.NetworkLedger.CoreValues

/-- Exact fields of the root record: Root, NoParent, Open, Empty. -/
structure CheckedRootArguments (program : Program) where
  root : NodeId
  identity : NodeId
  parent : NodeId
  phase : NodeId
  children : NodeId
  identityTag : Constructor
  parentTag : Constructor
  phaseTag : Constructor
  childrenTag : Constructor
  payload : CheckedTuple program root none [identity, parent, phase, children]
  identityValue : CheckedTuple program identity (some identityTag) []
  parentValue : CheckedTuple program parent (some parentTag) []
  phaseValue : CheckedTuple program phase (some phaseTag) []
  childrenValue : CheckedTuple program children (some childrenTag) []

/-- Successful strict evaluation retains each exact root-record field. -/
theorem root_arguments_return (program : Program) (checked : CheckedRootArguments program)
    (env : Environment) (start finish : Store) (result : Value)
    (bounded : BoundedLocations start)
    (evaluation : Eval program env checked.root start result finish) :
    ∃ payload identity parent phase children,
      result = .location payload ∧
      Resolve finish payload payload ∧ Resolve finish identity identity ∧
      Resolve finish parent parent ∧ Resolve finish phase phase ∧ Resolve finish children children ∧
      readCell finish payload = some [.location identity, .location parent, .location phase, .location children] ∧
      readCell finish identity = some [.tag checked.identityTag] ∧
      readCell finish parent = some [.tag checked.parentTag] ∧
      readCell finish phase = some [.tag checked.phaseTag] ∧
      readCell finish children = some [.tag checked.childrenTag] ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  obtain ⟨queried, afterFields, afterAlloc, payload, values, queryStep, fieldEvals,
    allocated, initialized, resultEq⟩ := checked_tuple_inversion checked.payload evaluation
  have queriedBound := query_preserves_bounded start queried .hostDefault .hostDefault bounded queryStep
  cases fieldEvals with
  | cons identityEval rest =>
    obtain ⟨identity, identityEq, identityFresh, _, identityCell, identityAliases, identityBound, identityRetained⟩ :=
      checked_nullary_retains checked.identityValue queriedBound identityEval
    cases rest with
    | cons parentEval rest =>
      obtain ⟨parent, parentEq, parentFresh, _, parentCell, parentAliases, parentBound, parentRetained⟩ :=
        checked_nullary_retains checked.parentValue identityBound parentEval
      cases rest with
      | cons phaseEval rest =>
        obtain ⟨phase, phaseEq, phaseFresh, _, phaseCell, phaseAliases, phaseBound, phaseRetained⟩ :=
          checked_nullary_retains checked.phaseValue parentBound phaseEval
        cases rest with
        | cons childrenEval rest =>
          obtain ⟨children, childrenEq, childrenFresh, _, childrenCell, childrenAliases, childrenBound, childrenRetained⟩ :=
            checked_nullary_retains checked.childrenValue phaseBound childrenEval
          cases rest
          have alloc : allocate .hostDefault
              ([.location identity, .location parent, .location phase, .location children] : List Value).length
              true afterFields = some (payload, afterAlloc) := by
            simpa [identityEq, parentEq, phaseEq, childrenEq] using allocated
          have init : initializeStorage payload
              ([.location identity, .location parent, .location phase, .location children] : List Value).length
              [.location identity, .location parent, .location phase, .location children] afterAlloc =
                some ([.location identity, .location parent, .location phase, .location children], finish) := by
            simpa [storedFields, identityEq, parentEq, phaseEq, childrenEq] using initialized
          obtain ⟨payloadFresh, _, payloadCell, finalAliases, finalBound, finalRetained⟩ :=
            host_allocation_retains childrenBound alloc init
          have payloadNoAlias : readAlias finish payload = none := by
            simpa [readAlias, finalAliases, payloadFresh] using bounded_fresh_no_alias afterFields childrenBound
          have identityNoAlias : readAlias finish identity = none := by
            simpa [readAlias, finalAliases, childrenAliases, phaseAliases, parentAliases, identityAliases,
              identityFresh] using bounded_fresh_no_alias queried queriedBound
          have parentNoAlias : readAlias finish parent = none := by
            simpa [readAlias, finalAliases, childrenAliases, phaseAliases, parentAliases, parentFresh] using
              bounded_fresh_no_alias _ identityBound
          have phaseNoAlias : readAlias finish phase = none := by
            simpa [readAlias, finalAliases, childrenAliases, phaseAliases, phaseFresh] using
              bounded_fresh_no_alias _ parentBound
          have childrenNoAlias : readAlias finish children = none := by
            simpa [readAlias, finalAliases, childrenAliases, childrenFresh] using
              bounded_fresh_no_alias _ phaseBound
          have queryAliases : queried.aliases = start.aliases := by
            simp [query] at queryStep
            subst queried
            rfl
          have queryRetained : ∀ address old, readCell start address = some old → readCell queried address = some old := by
            intro address old read
            simp [query] at queryStep
            subst queried
            simpa [readCell] using read
          have finalIdentity := finalRetained identity _ (childrenRetained identity _ (phaseRetained identity _ (parentRetained identity _ identityCell)))
          have finalParent := finalRetained parent _ (childrenRetained parent _ (phaseRetained parent _ parentCell))
          have finalPhase := finalRetained phase _ (childrenRetained phase _ phaseCell)
          have finalChildren := finalRetained children _ childrenCell
          refine ⟨payload, identity, parent, phase, children, resultEq,
            Resolve.cell payload _ payloadNoAlias payloadCell, Resolve.cell identity _ identityNoAlias finalIdentity,
            Resolve.cell parent _ parentNoAlias finalParent, Resolve.cell phase _ phaseNoAlias finalPhase,
            Resolve.cell children _ childrenNoAlias finalChildren,
            payloadCell, finalIdentity, finalParent, finalPhase, finalChildren,
            finalAliases.trans (childrenAliases.trans (phaseAliases.trans (parentAliases.trans (identityAliases.trans queryAliases)))),
            finalBound, ?_⟩
          intro address old read
          exact finalRetained address old (childrenRetained address old (phaseRetained address old
            (parentRetained address old (identityRetained address old (queryRetained address old read)))))

/-- The ordinary capture-free Record constructor around the checked fields. -/
structure CheckedRootRecord (program : Program) where
  call : NodeId
  function : NodeId
  operand : NodeId
  recordTag : Constructor
  closure : CheckedClosure program function
  argument : CheckedRootArguments program
  value : CheckedTuple program closure.body (some recordTag) [operand]
  callShape : program call = some (.apply function argument.root)
  operandShape : program operand = some (.variable closure.parameter)
  operandFresh : closure.parameter ≠ value.contextBinder

/-- A normal return contains the exact root record and retained fields. -/
theorem root_record_return (program : Program) (checked : CheckedRootRecord program)
    (env : Environment) (start finish : Store) (result : Value)
    (bounded : BoundedLocations start) (evaluation : Eval program env checked.call start result finish) :
    ∃ record payload identity parent phase children,
      result = .location record ∧
      Resolve finish record record ∧ Resolve finish payload payload ∧
      Resolve finish identity identity ∧ Resolve finish parent parent ∧
      Resolve finish phase phase ∧ Resolve finish children children ∧
      readCell finish record = some [.tag checked.recordTag, .location payload] ∧
      readCell finish payload = some [.location identity, .location parent, .location phase, .location children] ∧
      readCell finish identity = some [.tag checked.argument.identityTag] ∧
      readCell finish parent = some [.tag checked.argument.parentTag] ∧
      readCell finish phase = some [.tag checked.argument.phaseTag] ∧
      readCell finish children = some [.tag checked.argument.childrenTag] ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  obtain ⟨afterFunction, afterArgument, callable, argumentValue, parameter, body, captured,
    functionEval, target, argumentEval, bodyEval⟩ := apply_inversion checked.callShape evaluation
  obtain ⟨closureLocation, closureEq, closureFresh, _, closureCell, closureAliases, closureBound, closureRetained⟩ :=
    checked_closure_retains checked.closure bounded functionEval
  subst callable
  have closureNoAlias : readAlias afterFunction closureLocation = none := by
    simpa [readAlias, closureAliases, closureFresh] using bounded_fresh_no_alias start bounded
  have closureResolution : Resolve afterFunction closureLocation closureLocation :=
    Resolve.cell closureLocation [.closureCode checked.closure.closureNode] closureNoAlias closureCell
  obtain ⟨sameParameter, sameBody, sameCapture⟩ :=
    capture_free_function_target program afterFunction closureLocation closureLocation checked.closure.closureNode
      checked.closure.contextNode checked.closure.storageNode checked.closure.parameter checked.closure.body
      closureResolution closureCell checked.closure.closureShape target
  subst parameter
  subst body
  subst captured
  obtain ⟨payload, identity, parent, phase, children, payloadEq, payloadResolution, identityResolution,
    parentResolution, phaseResolution, childrenResolution, payloadCell, identityCell, parentCell,
    phaseCell, childrenCell, payloadAliases, payloadBound, payloadRetained⟩ :=
      root_arguments_return program checked.argument env afterFunction afterArgument argumentValue closureBound argumentEval
  subst argumentValue
  have operandBinding : CoreEval.lookup (extend [] checked.closure.parameter (.location payload))
      checked.closure.parameter = some (.location payload) := by simp [CoreEval.lookup, extend]
  obtain ⟨record, resultEq, recordFresh, _, recordCell, recordAliases, finalBound, recordRetained⟩ :=
    checked_unary_constructor_retains checked.value checked.closure.parameter checked.operandShape
      checked.operandFresh operandBinding payloadBound bodyEval
  have recordNoAlias : readAlias finish record = none := by
    simpa [readAlias, recordAliases, recordFresh] using bounded_fresh_no_alias afterArgument payloadBound
  refine ⟨record, payload, identity, parent, phase, children, resultEq,
    Resolve.cell record _ recordNoAlias recordCell,
    resolve_preserved recordAliases recordRetained payloadResolution,
    resolve_preserved recordAliases recordRetained identityResolution,
    resolve_preserved recordAliases recordRetained parentResolution,
    resolve_preserved recordAliases recordRetained phaseResolution,
    resolve_preserved recordAliases recordRetained childrenResolution,
    recordCell, recordRetained payload _ payloadCell, recordRetained identity _ identityCell,
    recordRetained parent _ parentCell, recordRetained phase _ phaseCell, recordRetained children _ childrenCell,
    recordAliases.trans (payloadAliases.trans closureAliases), finalBound, ?_⟩
  intro address old read
  exact recordRetained address old (payloadRetained address old (closureRetained address old read))


/-- The actual singleton record-list payload, evaluated in source order. -/
structure CheckedRootListArguments (program : Program) where
  root : NodeId
  empty : NodeId
  emptyTag : Constructor
  record : CheckedRootRecord program
  payload : CheckedTuple program root none [record.call, empty]
  emptyValue : CheckedTuple program empty (some emptyTag) []

/-- The root record and the empty record tail survive the enclosing pair. -/
theorem root_list_arguments_return (program : Program) (checked : CheckedRootListArguments program)
    (env : Environment) (start finish : Store) (result : Value)
    (bounded : BoundedLocations start) (evaluation : Eval program env checked.root start result finish) :
    ∃ pair record recordPayload identity parent phase children empty,
      result = .location pair ∧
      Resolve finish pair pair ∧ Resolve finish record record ∧ Resolve finish recordPayload recordPayload ∧
      Resolve finish identity identity ∧ Resolve finish parent parent ∧ Resolve finish phase phase ∧
      Resolve finish children children ∧ Resolve finish empty empty ∧
      readCell finish pair = some [.location record, .location empty] ∧
      readCell finish record = some [.tag checked.record.recordTag, .location recordPayload] ∧
      readCell finish recordPayload = some [.location identity, .location parent, .location phase, .location children] ∧
      readCell finish identity = some [.tag checked.record.argument.identityTag] ∧
      readCell finish parent = some [.tag checked.record.argument.parentTag] ∧
      readCell finish phase = some [.tag checked.record.argument.phaseTag] ∧
      readCell finish children = some [.tag checked.record.argument.childrenTag] ∧
      readCell finish empty = some [.tag checked.emptyTag] ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  obtain ⟨queried, afterFields, afterAlloc, pair, values, queryStep, fieldEvals,
    allocated, initialized, resultEq⟩ := checked_tuple_inversion checked.payload evaluation
  have queriedBound := query_preserves_bounded start queried .hostDefault .hostDefault bounded queryStep
  cases fieldEvals with
  | cons recordEval rest =>
    obtain ⟨record, recordPayload, identity, parent, phase, children, recordEq,
      recordResolution, recordPayloadResolution, identityResolution, parentResolution, phaseResolution,
      childrenResolution, recordCell, recordPayloadCell, identityCell, parentCell, phaseCell, childrenCell,
      recordAliases, recordBound, recordRetained⟩ :=
        root_record_return program checked.record _ queried _ _ queriedBound recordEval
    cases rest with
    | cons emptyEval rest =>
      obtain ⟨empty, emptyEq, emptyFresh, _, emptyCell, emptyAliases, emptyBound, emptyRetained⟩ :=
        checked_nullary_retains checked.emptyValue recordBound emptyEval
      cases rest
      have alloc : allocate .hostDefault ([.location record, .location empty] : List Value).length
          true afterFields = some (pair, afterAlloc) := by simpa [recordEq, emptyEq] using allocated
      have init : initializeStorage pair ([.location record, .location empty] : List Value).length
          [.location record, .location empty] afterAlloc = some ([.location record, .location empty], finish) := by
        simpa [storedFields, recordEq, emptyEq] using initialized
      obtain ⟨pairFresh, _, pairCell, finalAliases, finalBound, finalRetained⟩ :=
        host_allocation_retains emptyBound alloc init
      have pairNoAlias : readAlias finish pair = none := by
        simpa [readAlias, finalAliases, pairFresh] using bounded_fresh_no_alias afterFields emptyBound
      have emptyNoAlias : readAlias finish empty = none := by
        simpa [readAlias, finalAliases, emptyAliases, emptyFresh] using bounded_fresh_no_alias _ recordBound
      have queryAliases : queried.aliases = start.aliases := by
        simp [query] at queryStep
        subst queried
        rfl
      have queryRetained : ∀ address old, readCell start address = some old → readCell queried address = some old := by
        intro address old read
        simp [query] at queryStep
        subst queried
        simpa [readCell] using read
      have finalEmpty := finalRetained empty _ emptyCell
      refine ⟨pair, record, recordPayload, identity, parent, phase, children, empty, resultEq,
        Resolve.cell pair _ pairNoAlias pairCell,
        resolve_preserved finalAliases finalRetained (resolve_preserved emptyAliases emptyRetained recordResolution),
        resolve_preserved finalAliases finalRetained (resolve_preserved emptyAliases emptyRetained recordPayloadResolution),
        resolve_preserved finalAliases finalRetained (resolve_preserved emptyAliases emptyRetained identityResolution),
        resolve_preserved finalAliases finalRetained (resolve_preserved emptyAliases emptyRetained parentResolution),
        resolve_preserved finalAliases finalRetained (resolve_preserved emptyAliases emptyRetained phaseResolution),
        resolve_preserved finalAliases finalRetained (resolve_preserved emptyAliases emptyRetained childrenResolution),
        Resolve.cell empty _ emptyNoAlias finalEmpty,
        pairCell, finalRetained record _ (emptyRetained record _ recordCell), finalRetained recordPayload _ (emptyRetained recordPayload _ recordPayloadCell),
        finalRetained identity _ (emptyRetained identity _ identityCell), finalRetained parent _ (emptyRetained parent _ parentCell),
        finalRetained phase _ (emptyRetained phase _ phaseCell), finalRetained children _ (emptyRetained children _ childrenCell), finalEmpty,
        finalAliases.trans (emptyAliases.trans (recordAliases.trans queryAliases)), finalBound, ?_⟩
      intro address old read
      exact finalRetained address old (emptyRetained address old (recordRetained address old (queryRetained address old read)))


/-- The capture-free More constructor enclosing the singleton root record. -/
structure CheckedRootList (program : Program) where
  call : NodeId
  function : NodeId
  operand : NodeId
  moreTag : Constructor
  closure : CheckedClosure program function
  argument : CheckedRootListArguments program
  value : CheckedTuple program closure.body (some moreTag) [operand]
  callShape : program call = some (.apply function argument.root)
  operandShape : program operand = some (.variable closure.parameter)
  operandFresh : closure.parameter ≠ value.contextBinder

/-- Every normal return preserves the whole singleton Root record list. -/
theorem root_list_return (program : Program) (checked : CheckedRootList program)
    (env : Environment) (start finish : Store) (result : Value)
    (bounded : BoundedLocations start) (evaluation : Eval program env checked.call start result finish) :
    ∃ list pair record recordPayload identity parent phase children empty,
      result = .location list ∧
      Resolve finish list list ∧ Resolve finish pair pair ∧ Resolve finish record record ∧
      Resolve finish recordPayload recordPayload ∧ Resolve finish identity identity ∧
      Resolve finish parent parent ∧ Resolve finish phase phase ∧ Resolve finish children children ∧
      Resolve finish empty empty ∧
      readCell finish list = some [.tag checked.moreTag, .location pair] ∧
      readCell finish pair = some [.location record, .location empty] ∧
      readCell finish record = some [.tag checked.argument.record.recordTag, .location recordPayload] ∧
      readCell finish recordPayload = some [.location identity, .location parent, .location phase, .location children] ∧
      readCell finish identity = some [.tag checked.argument.record.argument.identityTag] ∧
      readCell finish parent = some [.tag checked.argument.record.argument.parentTag] ∧
      readCell finish phase = some [.tag checked.argument.record.argument.phaseTag] ∧
      readCell finish children = some [.tag checked.argument.record.argument.childrenTag] ∧
      readCell finish empty = some [.tag checked.argument.emptyTag] ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  obtain ⟨afterFunction, afterArgument, callable, argumentValue, parameter, body, captured,
    functionEval, target, argumentEval, bodyEval⟩ := apply_inversion checked.callShape evaluation
  obtain ⟨closureLocation, closureEq, closureFresh, _, closureCell, closureAliases, closureBound, closureRetained⟩ :=
    checked_closure_retains checked.closure bounded functionEval
  subst callable
  have closureNoAlias : readAlias afterFunction closureLocation = none := by
    simpa [readAlias, closureAliases, closureFresh] using bounded_fresh_no_alias start bounded
  have closureResolution : Resolve afterFunction closureLocation closureLocation :=
    Resolve.cell closureLocation [.closureCode checked.closure.closureNode] closureNoAlias closureCell
  obtain ⟨sameParameter, sameBody, sameCapture⟩ :=
    capture_free_function_target program afterFunction closureLocation closureLocation checked.closure.closureNode
      checked.closure.contextNode checked.closure.storageNode checked.closure.parameter checked.closure.body
      closureResolution closureCell checked.closure.closureShape target
  subst parameter
  subst body
  subst captured
  obtain ⟨pair, record, recordPayload, identity, parent, phase, children, empty, pairEq,
    pairResolution, recordResolution, recordPayloadResolution, identityResolution, parentResolution,
    phaseResolution, childrenResolution, emptyResolution, pairCell, recordCell, recordPayloadCell,
    identityCell, parentCell, phaseCell, childrenCell, emptyCell, pairAliases, pairBound, pairRetained⟩ :=
      root_list_arguments_return program checked.argument env afterFunction afterArgument argumentValue closureBound argumentEval
  subst argumentValue
  have operandBinding : CoreEval.lookup (extend [] checked.closure.parameter (.location pair))
      checked.closure.parameter = some (.location pair) := by simp [CoreEval.lookup, extend]
  obtain ⟨list, resultEq, listFresh, _, listCell, listAliases, finalBound, listRetained⟩ :=
    checked_unary_constructor_retains checked.value checked.closure.parameter checked.operandShape
      checked.operandFresh operandBinding pairBound bodyEval
  have listNoAlias : readAlias finish list = none := by
    simpa [readAlias, listAliases, listFresh] using bounded_fresh_no_alias afterArgument pairBound
  refine ⟨list, pair, record, recordPayload, identity, parent, phase, children, empty, resultEq,
    Resolve.cell list _ listNoAlias listCell,
    resolve_preserved listAliases listRetained pairResolution,
    resolve_preserved listAliases listRetained recordResolution,
    resolve_preserved listAliases listRetained recordPayloadResolution,
    resolve_preserved listAliases listRetained identityResolution,
    resolve_preserved listAliases listRetained parentResolution,
    resolve_preserved listAliases listRetained phaseResolution,
    resolve_preserved listAliases listRetained childrenResolution,
    resolve_preserved listAliases listRetained emptyResolution,
    listCell, listRetained pair _ pairCell, listRetained record _ recordCell,
    listRetained recordPayload _ recordPayloadCell, listRetained identity _ identityCell,
    listRetained parent _ parentCell, listRetained phase _ phaseCell, listRetained children _ childrenCell,
    listRetained empty _ emptyCell, listAliases.trans (pairAliases.trans closureAliases), finalBound, ?_⟩
  intro address old read
  exact listRetained address old (pairRetained address old (closureRetained address old read))


/-- The actual Root ledger payload: zero, singleton record list and no outputs. -/
structure CheckedRootLedgerArguments (program : Program) where
  root : NodeId
  zero : NodeId
  outputs : NodeId
  outputsTag : Constructor
  list : CheckedRootList program
  payload : CheckedTuple program root none [zero, list.call, outputs]
  zeroShape : program zero = some (.integer 0)
  emptyOutputs : CheckedTuple program outputs (some outputsTag) []

/-- All Root ledger payload cells come from the checked nested constructors. -/
theorem root_ledger_arguments_return (program : Program) (checked : CheckedRootLedgerArguments program)
    (env : Environment) (start finish : Store) (result : Value)
    (bounded : BoundedLocations start) (evaluation : Eval program env checked.root start result finish) :
    ∃ ledgerPayload list pair record recordPayload identity parent phase children empty outputs,
      result = .location ledgerPayload ∧
      Resolve finish ledgerPayload ledgerPayload ∧ Resolve finish list list ∧ Resolve finish pair pair ∧
      Resolve finish record record ∧ Resolve finish recordPayload recordPayload ∧
      Resolve finish identity identity ∧ Resolve finish parent parent ∧ Resolve finish phase phase ∧
      Resolve finish children children ∧ Resolve finish empty empty ∧ Resolve finish outputs outputs ∧
      readCell finish ledgerPayload = some [.integer 0, .location list, .location outputs] ∧
      readCell finish list = some [.tag checked.list.moreTag, .location pair] ∧
      readCell finish pair = some [.location record, .location empty] ∧
      readCell finish record = some [.tag checked.list.argument.record.recordTag, .location recordPayload] ∧
      readCell finish recordPayload = some [.location identity, .location parent, .location phase, .location children] ∧
      readCell finish identity = some [.tag checked.list.argument.record.argument.identityTag] ∧
      readCell finish parent = some [.tag checked.list.argument.record.argument.parentTag] ∧
      readCell finish phase = some [.tag checked.list.argument.record.argument.phaseTag] ∧
      readCell finish children = some [.tag checked.list.argument.record.argument.childrenTag] ∧
      readCell finish empty = some [.tag checked.list.argument.emptyTag] ∧
      readCell finish outputs = some [.tag checked.outputsTag] ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  obtain ⟨queried, afterFields, afterAlloc, ledgerPayload, values, queryStep, fieldEvals,
    allocated, initialized, resultEq⟩ := checked_tuple_inversion checked.payload evaluation
  have queriedBound := query_preserves_bounded start queried .hostDefault .hostDefault bounded queryStep
  cases fieldEvals with
  | cons zeroEval rest =>
    obtain ⟨zeroValue, zeroState⟩ := CoreInitialization.integer_zero_inversion checked.zeroShape zeroEval
    cases zeroValue
    cases zeroState
    cases rest with
    | cons listEval rest =>
      obtain ⟨list, pair, record, recordPayload, identity, parent, phase, children, empty, listEq,
        listResolution, pairResolution, recordResolution, recordPayloadResolution, identityResolution,
        parentResolution, phaseResolution, childrenResolution, emptyResolution,
        listCell, pairCell, recordCell, recordPayloadCell, identityCell, parentCell, phaseCell, childrenCell,
        emptyCell, listAliases, listBound, listRetained⟩ :=
          root_list_return program checked.list _ queried _ _ queriedBound listEval
      cases rest with
      | cons outputsEval rest =>
        obtain ⟨outputs, outputsEq, outputsFresh, _, outputsCell, outputsAliases, outputsBound, outputsRetained⟩ :=
          checked_nullary_retains checked.emptyOutputs listBound outputsEval
        cases rest
        have alloc : allocate .hostDefault ([.integer 0, .location list, .location outputs] : List Value).length
            true afterFields = some (ledgerPayload, afterAlloc) := by simpa [listEq, outputsEq] using allocated
        have init : initializeStorage ledgerPayload ([.integer 0, .location list, .location outputs] : List Value).length
            [.integer 0, .location list, .location outputs] afterAlloc =
              some ([.integer 0, .location list, .location outputs], finish) := by
          simpa [storedFields, listEq, outputsEq] using initialized
        obtain ⟨payloadFresh, _, payloadCell, finalAliases, finalBound, finalRetained⟩ :=
          host_allocation_retains outputsBound alloc init
        have payloadNoAlias : readAlias finish ledgerPayload = none := by
          simpa [readAlias, finalAliases, payloadFresh] using bounded_fresh_no_alias afterFields outputsBound
        have outputsNoAlias : readAlias finish outputs = none := by
          simpa [readAlias, finalAliases, outputsAliases, outputsFresh] using bounded_fresh_no_alias _ listBound
        have queryAliases : queried.aliases = start.aliases := by
          simp [query] at queryStep
          subst queried
          rfl
        have queryRetained : ∀ address old, readCell start address = some old → readCell queried address = some old := by
          intro address old read
          simp [query] at queryStep
          subst queried
          simpa [readCell] using read
        have finalOutputs := finalRetained outputs _ outputsCell
        refine ⟨ledgerPayload, list, pair, record, recordPayload, identity, parent, phase, children, empty, outputs,
          resultEq, Resolve.cell ledgerPayload _ payloadNoAlias payloadCell,
          resolve_preserved finalAliases finalRetained (resolve_preserved outputsAliases outputsRetained listResolution),
          resolve_preserved finalAliases finalRetained (resolve_preserved outputsAliases outputsRetained pairResolution),
          resolve_preserved finalAliases finalRetained (resolve_preserved outputsAliases outputsRetained recordResolution),
          resolve_preserved finalAliases finalRetained (resolve_preserved outputsAliases outputsRetained recordPayloadResolution),
          resolve_preserved finalAliases finalRetained (resolve_preserved outputsAliases outputsRetained identityResolution),
          resolve_preserved finalAliases finalRetained (resolve_preserved outputsAliases outputsRetained parentResolution),
          resolve_preserved finalAliases finalRetained (resolve_preserved outputsAliases outputsRetained phaseResolution),
          resolve_preserved finalAliases finalRetained (resolve_preserved outputsAliases outputsRetained childrenResolution),
          resolve_preserved finalAliases finalRetained (resolve_preserved outputsAliases outputsRetained emptyResolution),
          Resolve.cell outputs _ outputsNoAlias finalOutputs,
          payloadCell, finalRetained list _ (outputsRetained list _ listCell),
          finalRetained pair _ (outputsRetained pair _ pairCell),
          finalRetained record _ (outputsRetained record _ recordCell),
          finalRetained recordPayload _ (outputsRetained recordPayload _ recordPayloadCell),
          finalRetained identity _ (outputsRetained identity _ identityCell),
          finalRetained parent _ (outputsRetained parent _ parentCell),
          finalRetained phase _ (outputsRetained phase _ phaseCell),
          finalRetained children _ (outputsRetained children _ childrenCell),
          finalRetained empty _ (outputsRetained empty _ emptyCell), finalOutputs,
          finalAliases.trans (outputsAliases.trans (listAliases.trans queryAliases)), finalBound, ?_⟩
        intro address old read
        exact finalRetained address old (outputsRetained address old (listRetained address old (queryRetained address old read)))


/-- The capture-free Ledger constructor around the Root ledger payload. -/
structure CheckedRootLedger (program : Program) where
  call : NodeId
  function : NodeId
  operand : NodeId
  ledgerTag : Constructor
  closure : CheckedClosure program function
  argument : CheckedRootLedgerArguments program
  value : CheckedTuple program closure.body (some ledgerTag) [operand]
  callShape : program call = some (.apply function argument.root)
  operandShape : program operand = some (.variable closure.parameter)
  operandFresh : closure.parameter ≠ value.contextBinder

/-- A normal return retains every field of the actual initialized Root ledger. -/
theorem root_ledger_return (program : Program) (checked : CheckedRootLedger program)
    (env : Environment) (start finish : Store) (result : Value)
    (bounded : BoundedLocations start) (evaluation : Eval program env checked.call start result finish) :
    ∃ ledger ledgerPayload list pair record recordPayload identity parent phase children empty outputs,
      result = .location ledger ∧
      Resolve finish ledger ledger ∧ Resolve finish ledgerPayload ledgerPayload ∧
      Resolve finish list list ∧ Resolve finish pair pair ∧ Resolve finish record record ∧
      Resolve finish recordPayload recordPayload ∧ Resolve finish identity identity ∧
      Resolve finish parent parent ∧ Resolve finish phase phase ∧ Resolve finish children children ∧
      Resolve finish empty empty ∧ Resolve finish outputs outputs ∧
      readCell finish ledger = some [.tag checked.ledgerTag, .location ledgerPayload] ∧
      readCell finish ledgerPayload = some [.integer 0, .location list, .location outputs] ∧
      readCell finish list = some [.tag checked.argument.list.moreTag, .location pair] ∧
      readCell finish pair = some [.location record, .location empty] ∧
      readCell finish record = some [.tag checked.argument.list.argument.record.recordTag, .location recordPayload] ∧
      readCell finish recordPayload = some [.location identity, .location parent, .location phase, .location children] ∧
      readCell finish identity = some [.tag checked.argument.list.argument.record.argument.identityTag] ∧
      readCell finish parent = some [.tag checked.argument.list.argument.record.argument.parentTag] ∧
      readCell finish phase = some [.tag checked.argument.list.argument.record.argument.phaseTag] ∧
      readCell finish children = some [.tag checked.argument.list.argument.record.argument.childrenTag] ∧
      readCell finish empty = some [.tag checked.argument.list.argument.emptyTag] ∧
      readCell finish outputs = some [.tag checked.argument.outputsTag] ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish := by
  obtain ⟨afterFunction, afterArgument, callable, argumentValue, parameter, body, captured,
    functionEval, target, argumentEval, bodyEval⟩ := apply_inversion checked.callShape evaluation
  obtain ⟨closureLocation, closureEq, closureFresh, _, closureCell, closureAliases, closureBound, _⟩ :=
    checked_closure_retains checked.closure bounded functionEval
  subst callable
  have closureNoAlias : readAlias afterFunction closureLocation = none := by
    simpa [readAlias, closureAliases, closureFresh] using bounded_fresh_no_alias start bounded
  have closureResolution : Resolve afterFunction closureLocation closureLocation :=
    Resolve.cell closureLocation [.closureCode checked.closure.closureNode] closureNoAlias closureCell
  obtain ⟨sameParameter, sameBody, sameCapture⟩ :=
    capture_free_function_target program afterFunction closureLocation closureLocation checked.closure.closureNode
      checked.closure.contextNode checked.closure.storageNode checked.closure.parameter checked.closure.body
      closureResolution closureCell checked.closure.closureShape target
  subst parameter
  subst body
  subst captured
  obtain ⟨ledgerPayload, list, pair, record, recordPayload, identity, parent, phase, children, empty, outputs,
    payloadEq, payloadResolution, listResolution, pairResolution, recordResolution, recordPayloadResolution,
    identityResolution, parentResolution, phaseResolution, childrenResolution, emptyResolution, outputsResolution,
    payloadCell, listCell, pairCell, recordCell, recordPayloadCell, identityCell, parentCell, phaseCell,
    childrenCell, emptyCell, outputsCell, payloadAliases, payloadBound, _⟩ :=
      root_ledger_arguments_return program checked.argument env afterFunction afterArgument argumentValue closureBound argumentEval
  subst argumentValue
  have operandBinding : CoreEval.lookup (extend [] checked.closure.parameter (.location ledgerPayload))
      checked.closure.parameter = some (.location ledgerPayload) := by simp [CoreEval.lookup, extend]
  obtain ⟨ledger, resultEq, ledgerFresh, _, ledgerCell, ledgerAliases, finalBound, retained⟩ :=
    checked_unary_constructor_retains checked.value checked.closure.parameter checked.operandShape
      checked.operandFresh operandBinding payloadBound bodyEval
  have ledgerNoAlias : readAlias finish ledger = none := by
    simpa [readAlias, ledgerAliases, ledgerFresh] using bounded_fresh_no_alias afterArgument payloadBound
  exact ⟨ledger, ledgerPayload, list, pair, record, recordPayload, identity, parent, phase, children, empty, outputs,
    resultEq, Resolve.cell ledger _ ledgerNoAlias ledgerCell,
    resolve_preserved ledgerAliases retained payloadResolution,
    resolve_preserved ledgerAliases retained listResolution,
    resolve_preserved ledgerAliases retained pairResolution,
    resolve_preserved ledgerAliases retained recordResolution,
    resolve_preserved ledgerAliases retained recordPayloadResolution,
    resolve_preserved ledgerAliases retained identityResolution,
    resolve_preserved ledgerAliases retained parentResolution,
    resolve_preserved ledgerAliases retained phaseResolution,
    resolve_preserved ledgerAliases retained childrenResolution,
    resolve_preserved ledgerAliases retained emptyResolution,
    resolve_preserved ledgerAliases retained outputsResolution,
    ledgerCell, retained ledgerPayload _ payloadCell, retained list _ listCell, retained pair _ pairCell,
    retained record _ recordCell, retained recordPayload _ recordPayloadCell, retained identity _ identityCell,
    retained parent _ parentCell, retained phase _ phaseCell, retained children _ childrenCell,
    retained empty _ emptyCell, retained outputs _ outputsCell,
    ledgerAliases.trans (payloadAliases.trans closureAliases), finalBound⟩


/-- Unit argument dispatch to the checked Root ledger constructor. -/
structure CheckedRootInitializer (program : Program) where
  body : NodeId
  scrutinee : NodeId
  parameter : Binder
  ledger : CheckedRootLedger program
  bodyShape : program body = some (.caseMatch scrutinee [(.unit, ledger.call)])
  scrutineeShape : program scrutinee = some (.variable parameter)

/-- Every normal Root initializer return contains the actual checked fields. -/
theorem root_initializer_return (program : Program) (checked : CheckedRootInitializer program)
    (env : Environment) (start finish : Store) (result : Value)
    (unitBinding : CoreEval.lookup env checked.parameter = some .unit)
    (bounded : BoundedLocations start)
    (evaluation : Eval program env checked.body start result finish) :
    ∃ ledger ledgerPayload list pair record recordPayload identity parent phase children empty outputs,
      result = .location ledger ∧
      Resolve finish ledger ledger ∧ Resolve finish ledgerPayload ledgerPayload ∧
      Resolve finish list list ∧ Resolve finish pair pair ∧ Resolve finish record record ∧
      Resolve finish recordPayload recordPayload ∧ Resolve finish identity identity ∧
      Resolve finish parent parent ∧ Resolve finish phase phase ∧ Resolve finish children children ∧
      Resolve finish empty empty ∧ Resolve finish outputs outputs ∧
      readCell finish ledger = some [.tag checked.ledger.ledgerTag, .location ledgerPayload] ∧
      readCell finish ledgerPayload = some [.integer 0, .location list, .location outputs] ∧
      readCell finish list = some [.tag checked.ledger.argument.list.moreTag, .location pair] ∧
      readCell finish pair = some [.location record, .location empty] ∧
      readCell finish record = some [.tag checked.ledger.argument.list.argument.record.recordTag, .location recordPayload] ∧
      readCell finish recordPayload = some [.location identity, .location parent, .location phase, .location children] ∧
      readCell finish identity = some [.tag checked.ledger.argument.list.argument.record.argument.identityTag] ∧
      readCell finish parent = some [.tag checked.ledger.argument.list.argument.record.argument.parentTag] ∧
      readCell finish phase = some [.tag checked.ledger.argument.list.argument.record.argument.phaseTag] ∧
      readCell finish children = some [.tag checked.ledger.argument.list.argument.record.argument.childrenTag] ∧
      readCell finish empty = some [.tag checked.ledger.argument.list.argument.emptyTag] ∧
      readCell finish outputs = some [.tag checked.ledger.argument.outputsTag] ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish := by
  obtain ⟨middle, value, body, bindings, scrutineeEval, chosen, bodyEval⟩ :=
    case_match_inversion checked.bodyShape evaluation
  obtain ⟨found, sameStore⟩ := variable_inversion checked.scrutineeShape scrutineeEval
  have sameValue : value = .unit := by simpa [unitBinding] using found.symm
  subst value
  subst middle
  cases chosen with
  | first pattern selected rest selectedBindings hit =>
    cases hit
    simpa using root_ledger_return program checked.ledger env start finish result bounded bodyEval
  | later pattern ignored rest selected selectedBindings miss next =>
    cases next

end Ash.NetworkLedger.CoreRootInitialization
