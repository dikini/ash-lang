import NetworkLedgerCoreValues

/- The constructor fragment for an ordinary worker initializer. This is a
   normal-return statement under the selected default provider, not a claim
   about an actual linked caller or current ledger. -/
namespace Ash.NetworkLedger.CoreInitialization

open Ash.NetworkLedger.CoreEval
open Ash.NetworkLedger.CoreRegion
open Ash.NetworkLedger.CoreValues

/-- The exact ordered worker ledger payload: counter, empty records, empty outputs. -/
structure CheckedWorkerArguments (program : Program) where
  root : NodeId
  zero : NodeId
  records : NodeId
  outputs : NodeId
  recordsTag : Constructor
  outputsTag : Constructor
  payload : CheckedTuple program root none [zero, records, outputs]
  zeroShape : program zero = some (.integer 0)
  emptyRecords : CheckedTuple program records (some recordsTag) []
  emptyOutputs : CheckedTuple program outputs (some outputsTag) []

/-- The checked integer literal evaluates without changing the store. -/
theorem integer_zero_inversion {program : Program} {node : NodeId} {env : Environment}
    {start finish : Store} {value : Value} (shape : program node = some (.integer 0))
    (evaluation : Eval program env node start value finish) :
    value = .integer 0 ∧ finish = start := by
  cases evaluation <;> simp_all

/-- Strict evaluation returns the literal zero and both actual empty constructors. -/
theorem worker_arguments_return (program : Program) (checked : CheckedWorkerArguments program)
    (env : Environment) (start finish : Store) (result : Value)
    (bounded : BoundedLocations start)
    (evaluation : Eval program env checked.root start result finish) :
    ∃ payload records outputs,
      result = .location payload ∧
      Resolve finish payload payload ∧ Resolve finish records records ∧ Resolve finish outputs outputs ∧
      readCell finish payload = some [.integer 0, .location records, .location outputs] ∧
      readCell finish records = some [.tag checked.recordsTag] ∧
      readCell finish outputs = some [.tag checked.outputsTag] ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  obtain ⟨queried, afterFields, afterAlloc, payload, values, queryStep, fieldEvals,
    allocated, initialized, resultEq⟩ := checked_tuple_inversion checked.payload evaluation
  have queriedBound := query_preserves_bounded start queried .hostDefault .hostDefault bounded queryStep
  cases fieldEvals with
  | cons zeroEval rest =>
    obtain ⟨zeroValue, zeroState⟩ := integer_zero_inversion checked.zeroShape zeroEval
    cases zeroValue
    cases zeroState
    cases rest with
    | cons recordsEval rest =>
      obtain ⟨records, recordsEq, recordsFresh, _, recordsCell, recordsAliases, recordsBound, recordsRetained⟩ :=
        checked_nullary_retains checked.emptyRecords queriedBound recordsEval
      cases rest with
      | cons outputsEval rest =>
        obtain ⟨outputs, outputsEq, outputsFresh, _, outputsCell, outputsAliases, outputsBound, outputsRetained⟩ :=
          checked_nullary_retains checked.emptyOutputs recordsBound outputsEval
        cases rest
        have alloc : allocate .hostDefault ([.integer 0, .location records, .location outputs] : List Value).length
            true afterFields = some (payload, afterAlloc) := by simpa [recordsEq, outputsEq] using allocated
        have init : initializeStorage payload ([.integer 0, .location records, .location outputs] : List Value).length
            [.integer 0, .location records, .location outputs] afterAlloc =
              some ([.integer 0, .location records, .location outputs], finish) := by
          simpa [storedFields, recordsEq, outputsEq] using initialized
        obtain ⟨payloadFresh, _, payloadCell, finalAliases, finalBound, finalRetained⟩ :=
          host_allocation_retains outputsBound alloc init
        have payloadNoAlias : readAlias finish payload = none := by
          simpa [readAlias, finalAliases, payloadFresh] using bounded_fresh_no_alias afterFields outputsBound
        have recordsNoAlias : readAlias finish records = none := by
          simpa [readAlias, finalAliases, outputsAliases, recordsAliases, recordsFresh] using
            bounded_fresh_no_alias queried queriedBound
        have outputsNoAlias : readAlias finish outputs = none := by
          simpa [readAlias, finalAliases, outputsAliases, outputsFresh] using
            bounded_fresh_no_alias _ recordsBound
        have queryAliases : queried.aliases = start.aliases := by
          simp [query] at queryStep
          subst queried
          rfl
        have queryRetained : ∀ address old, readCell start address = some old → readCell queried address = some old := by
          intro address old read
          simp [query] at queryStep
          subst queried
          simpa [readCell] using read
        have finalRecords := finalRetained records _ (outputsRetained records _ recordsCell)
        have finalOutputs := finalRetained outputs _ outputsCell
        refine ⟨payload, records, outputs, resultEq,
          Resolve.cell payload _ payloadNoAlias payloadCell,
          Resolve.cell records _ recordsNoAlias finalRecords,
          Resolve.cell outputs _ outputsNoAlias finalOutputs,
          payloadCell, finalRecords, finalOutputs,
          finalAliases.trans (outputsAliases.trans (recordsAliases.trans queryAliases)), finalBound, ?_⟩
        intro address old read
        exact finalRetained address old (outputsRetained address old
          (recordsRetained address old (queryRetained address old read)))

/-- The exact capture-free Ledger constructor call around the worker payload. -/
structure CheckedWorkerConstructor (program : Program) where
  call : NodeId
  function : NodeId
  operand : NodeId
  ledgerTag : Constructor
  closure : CheckedClosure program function
  argument : CheckedWorkerArguments program
  value : CheckedTuple program closure.body (some ledgerTag) [operand]
  callShape : program call = some (.apply function argument.root)
  operandShape : program operand = some (.variable closure.parameter)
  operandFresh : closure.parameter ≠ value.contextBinder

/-- A normal return retains the actual payload and both empty constructors. -/
theorem worker_constructor_return (program : Program) (checked : CheckedWorkerConstructor program)
    (env : Environment) (start finish : Store) (result : Value)
    (bounded : BoundedLocations start)
    (evaluation : Eval program env checked.call start result finish) :
    ∃ ledger payload records outputs,
      result = .location ledger ∧
      Resolve finish ledger ledger ∧ Resolve finish payload payload ∧
      Resolve finish records records ∧ Resolve finish outputs outputs ∧
      readCell finish ledger = some [.tag checked.ledgerTag, .location payload] ∧
      readCell finish payload = some [.integer 0, .location records, .location outputs] ∧
      readCell finish records = some [.tag checked.argument.recordsTag] ∧
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
  obtain ⟨payload, records, outputs, payloadEq, payloadResolution, recordsResolution, outputsResolution,
    payloadCell, recordsCell, outputsCell,
    payloadAliases, payloadBound, _⟩ :=
      worker_arguments_return program checked.argument env afterFunction afterArgument argumentValue
        closureBound argumentEval
  subst argumentValue
  have operandBinding : CoreEval.lookup (extend [] checked.closure.parameter (.location payload))
      checked.closure.parameter = some (.location payload) := by simp [CoreEval.lookup, extend]
  obtain ⟨ledger, resultEq, ledgerFresh, _, ledgerCell, ledgerAliases, finalBound, retained⟩ :=
    checked_unary_constructor_retains checked.value checked.closure.parameter checked.operandShape
      checked.operandFresh operandBinding payloadBound bodyEval
  have ledgerNoAlias : readAlias finish ledger = none := by
    simpa [readAlias, ledgerAliases, ledgerFresh] using bounded_fresh_no_alias afterArgument payloadBound
  exact ⟨ledger, payload, records, outputs, resultEq,
    Resolve.cell ledger _ ledgerNoAlias ledgerCell,
    resolve_preserved ledgerAliases retained payloadResolution,
    resolve_preserved ledgerAliases retained recordsResolution,
    resolve_preserved ledgerAliases retained outputsResolution, ledgerCell,
    retained payload _ payloadCell, retained records _ recordsCell, retained outputs _ outputsCell,
    ledgerAliases.trans (payloadAliases.trans closureAliases), finalBound⟩


/-- The initializer destructures its Unit argument and enters the checked call. -/
structure CheckedWorkerInitializer (program : Program) where
  body : NodeId
  scrutinee : NodeId
  parameter : Binder
  constructor : CheckedWorkerConstructor program
  bodyShape : program body = some (.caseMatch scrutinee [(.unit, constructor.call)])
  scrutineeShape : program scrutinee = some (.variable parameter)

/-- Every normal worker initializer return has exactly the checked initial fields. -/
theorem worker_initializer_return (program : Program) (checked : CheckedWorkerInitializer program)
    (env : Environment) (start finish : Store) (result : Value)
    (unitBinding : CoreEval.lookup env checked.parameter = some .unit)
    (bounded : BoundedLocations start)
    (evaluation : Eval program env checked.body start result finish) :
    ∃ ledger payload records outputs,
      result = .location ledger ∧
      Resolve finish ledger ledger ∧ Resolve finish payload payload ∧
      Resolve finish records records ∧ Resolve finish outputs outputs ∧
      readCell finish ledger = some [.tag checked.constructor.ledgerTag, .location payload] ∧
      readCell finish payload = some [.integer 0, .location records, .location outputs] ∧
      readCell finish records = some [.tag checked.constructor.argument.recordsTag] ∧
      readCell finish outputs = some [.tag checked.constructor.argument.outputsTag] ∧
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
    simpa using worker_constructor_return program checked.constructor env start finish result bounded bodyEval
  | later pattern ignored rest selected selectedBindings miss next =>
    cases next

end Ash.NetworkLedger.CoreInitialization
