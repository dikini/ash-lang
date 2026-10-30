import NetworkLedgerCoreRecordUpdate
import NetworkLedgerCoreIncrement
import NetworkLedgerCoreGenericInsert
import NetworkLedgerRegistrationCheck

/- Registration invokes the actual linked lookup before selecting its branch.
   The correspondence stays conditional on finite represented values, exact
   closures and the faithfully selected nonreentrant default provider. -/
namespace Ash.NetworkLedger.CoreRecordRegistration

open Ash.NetworkLedger
open Ash.NetworkLedger.CoreRegion
open Ash.NetworkLedger.CoreEval
open Ash.NetworkLedger.CoreValues
open Ash.NetworkLedger.CoreLookup
open Ash.NetworkLedger.CoreRecordLookup

/-- The actual stored lookup call returns the first matching whole Record. -/
theorem checked_record_lookup_call (c : Constructors) (program : Program) (absent present : Constructor)
    (checked : CheckedLookupBase c program absent present)
    (projection : RecordProjectionShape program checked.projection)
    (projectionFunctionName : projection.functionName = checked.projectionName)
    (projectionEntryName : projection.recordName = checked.entryName)
    (projectionCode : projection.code = checked.projectionCode)
    (call function argument wantedNode listNode : NodeId) (env : Environment)
    (start finish : Store) (result wanted list : Value) (queryId : Id) (key : Value → Id) (entries : List Value)
    (callName wantedName listName : Binder) (selfAddress selfResolved comparisonAddress comparisonResolved
      projectionAddress projectionResolved : Nat)
    (captureValues : List Value) (captureEnv : Environment)
    (pair : CheckedTuple program argument none [wantedNode, listNode])
    (callShape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable callName))
    (functionBinding : CoreEval.lookup env callName = some (.location selfAddress))
    (wantedShape : program wantedNode = some (.variable wantedName))
    (listShape : program listNode = some (.variable listName))
    (wantedFresh : wantedName ≠ pair.contextBinder) (listFresh : listName ≠ pair.contextBinder)
    (wantedBinding : CoreEval.lookup env wantedName = some wanted)
    (listBinding : CoreEval.lookup env listName = some list)
    (selfBinding : CoreEval.lookup captureEnv.reverse checked.functionName = some (.location selfAddress))
    (comparisonBinding : CoreEval.lookup captureEnv.reverse checked.comparisonName = some (.location comparisonAddress))
    (projectionBinding : CoreEval.lookup captureEnv.reverse checked.projectionName = some (.location projectionAddress))
    (captureBindings : CaptureBindings program checked.captureNodes captureValues captureEnv)
    (selfResolution : Resolve start selfAddress selfResolved)
    (selfCell : readCell start selfResolved = some (.closureCode checked.code :: captureValues))
    (comparisonResolution : Resolve start comparisonAddress comparisonResolved)
    (comparisonCell : readCell start comparisonResolved = some [.closureCode checked.comparator.code])
    (projectionResolution : Resolve start projectionAddress projectionResolved)
    (projectionCell : readCell start projectionResolved = some [.closureCode checked.projectionCode])
    (bounded : BoundedLocations start) (wantedRep : Ident c start wanted queryId)
    (listRep : Children c start list entries)
    (keys : RepresentedEntries c (RecordEntry projection.record) start key entries)
    (evaluation : Eval program env call start result finish) :
    LookupOutcome absent present start finish result (Ash.NetworkLedger.lookup key queryId entries) := by
  obtain ⟨afterArgument, payload, bodyEval, payloadResolution, payloadCell, argumentProgress,
    argumentAliases, argumentBound, argumentRetained⟩ :=
    checked_recursive_call program call function argument wantedNode listNode env start finish result wanted list
      callName wantedName listName selfAddress selfResolved checked.code checked.context checked.storage
      checked.parameter checked.body checked.captureNodes captureValues captureEnv pair callShape functionShape
      functionBinding selfResolution selfCell checked.closureShape captureBindings wantedShape listShape wantedFresh listFresh
      wantedBinding listBinding bounded evaluation
  have wantedAfter := ident_retained c start afterArgument wanted queryId argumentAliases argumentRetained wantedRep
  have listAfter := children_retained c start afterArgument list entries argumentAliases argumentRetained listRep
  have keysAfter := represented_entries_retained c (RecordEntry projection.record) start afterArgument key entries
    (record_entry_retained projection.record) argumentAliases argumentRetained keys
  have selfAfter := resolve_preserved argumentAliases argumentRetained selfResolution
  have selfCellAfter := argumentRetained selfResolved _ selfCell
  have comparisonAfter := resolve_preserved argumentAliases argumentRetained comparisonResolution
  have comparisonCellAfter := argumentRetained comparisonResolved _ comparisonCell
  have projectionAfter := resolve_preserved argumentAliases argumentRetained projectionResolution
  have projectionCellAfter := argumentRetained projectionResolved _ projectionCell
  obtain ⟨returned, lookupProgress, lookupAliases, finalBound, lookupRetained⟩ :=
    record_lookup_body_correct c program absent present checked projection projectionFunctionName projectionEntryName
      projectionCode captureValues captureEnv selfAddress selfResolved comparisonAddress comparisonResolved
      projectionAddress projectionResolved wanted queryId key entries selfBinding comparisonBinding projectionBinding
      captureBindings afterArgument finish payload payload list result payloadResolution payloadCell argumentBound wantedAfter
      listAfter keysAfter selfAfter selfCellAfter comparisonAfter comparisonCellAfter projectionAfter projectionCellAfter bodyEval
  have aliases : finish.aliases = start.aliases := lookupAliases.trans argumentAliases
  refine ⟨returned, ?_, aliases, finalBound, ?_⟩
  · omega
  · intro address old read
    exact lookupRetained address old (argumentRetained address old read)

/-- A populated constructor binds the exact stored payload. -/
theorem payload_binder_match (store : Store) (tag : Constructor) (address resolved : Nat)
    (payload : Value) (name : Binder)
    (resolution : Resolve store address resolved)
    (cell : readCell store resolved = some [.tag tag, payload])
    {result : Option Environment}
    (attempt : Attempt store (.constructor tag (some (.binder name))) (.location address) result) :
    result = some [(name, payload)] := by
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
    simp only [constructorFields, Option.some.injEq, Prod.mk.injEq] at view
    rcases view with ⟨_, rfl⟩
    cases inner
    rfl
  | constructorMissingPayload _ _ _ other stored otherResolution otherRead view =>
    have equal := resolved_fields_unique resolution otherResolution cell otherRead
    subst stored
    simp [constructorFields] at view

/-- A populated result cannot select a nullary branch. -/
theorem payload_nullary_misses (store : Store) (wanted actual : Constructor)
    (address resolved : Nat) (payload : Value)
    (resolution : Resolve store address resolved)
    (cell : readCell store resolved = some [.tag actual, payload])
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

/-- A lookup-result match selects missing or the exact original whole Record. -/
theorem lookup_result_selects (store : Store) (absent present : Constructor)
    (result : Value) (found : Option Value) (missingBody foundBody : NodeId) (name : Binder)
    (representation : LookupResult absent present store result found)
    {chosen : NodeId} {bindings : Environment}
    (selected : Selected store result [(.constructor absent none, missingBody),
      (.constructor present (some (.binder name)), foundBody)] chosen bindings) :
    match found with
    | none => chosen = missingBody ∧ bindings = []
    | some entry => chosen = foundBody ∧ bindings = [(name, entry)] := by
  cases representation with
  | absentResult address resolved resolution cell =>
    cases selected with
    | first _ _ _ actual hit =>
      have same := nullary_constructor_match store absent address resolved resolution cell hit
      cases same
      exact ⟨rfl, rfl⟩
    | later _ _ _ _ _ miss next =>
      have impossible := nullary_constructor_match store absent address resolved resolution cell miss
      contradiction
  | presentResult address resolved entry resolution cell =>
    cases selected with
    | first _ _ _ actual hit =>
      have impossible := payload_nullary_misses store absent present address resolved entry resolution cell hit
      contradiction
    | later _ _ _ _ _ miss next =>
      cases next with
      | first _ _ _ actual hit =>
        have same := payload_binder_match store present address resolved entry name resolution cell hit
        cases same
        exact ⟨rfl, rfl⟩
      | later _ _ _ _ _ _ impossible => cases impossible

/-- The registration match follows the actual lookup call's represented result. -/
theorem registration_lookup_branch (program : Program) (absent present : Constructor)
    (branch call missingBody foundBody : NodeId) (name : Binder) (env : Environment)
    (start finish : Store) (result : Value) (expected : Option Value)
    (branchShape : program branch = some (.caseMatch call
      [(.constructor absent none, missingBody), (.constructor present (some (.binder name)), foundBody)]))
    (lookupLaw : ∀ middle value, Eval program env call start value middle →
      LookupOutcome absent present start middle value expected)
    (evaluation : Eval program env branch start result finish) :
    ∃ middle,
      (match expected with
       | none => Eval program env missingBody middle result finish
       | some entry => Eval program (extend env name entry) foundBody middle result finish) ∧
      start.nextLocation < middle.nextLocation ∧ middle.aliases = start.aliases ∧
      BoundedLocations middle ∧
      (∀ address old, readCell start address = some old → readCell middle address = some old) := by
  obtain ⟨middle, value, chosen, bindings, lookupEval, selected, bodyEval⟩ :=
    case_match_inversion branchShape evaluation
  obtain ⟨representation, advances, aliases, middleBound, retained⟩ := lookupLaw middle value lookupEval
  have selectedFacts := lookup_result_selects middle absent present value expected missingBody foundBody name
    representation selected
  cases expected with
  | none =>
    rcases selectedFacts with ⟨rfl, rfl⟩
    exact ⟨middle, by simpa using bodyEval, advances, aliases, middleBound, retained⟩
  | some entry =>
    rcases selectedFacts with ⟨rfl, rfl⟩
    exact ⟨middle, by simpa [extend] using bodyEval, advances, aliases, middleBound, retained⟩

/-- A rejecting branch returns the original ledger value and the checked status. -/
theorem checked_rejected_result (program : Program) (root ledgerNode statusNode : NodeId)
    (rejected : Constructor) (env : Environment) (start finish : Store) (result ledger : Value)
    (ledgerName : Binder) (pair : CheckedTuple program root none [ledgerNode, statusNode])
    (status : CheckedTuple program statusNode (some rejected) [])
    (ledgerShape : program ledgerNode = some (.variable ledgerName))
    (ledgerFresh : ledgerName ≠ pair.contextBinder)
    (ledgerBinding : CoreEval.lookup env ledgerName = some ledger)
    (bounded : BoundedLocations start) (evaluation : Eval program env root start result finish) :
    ∃ statusAddress, Result finish result ledger (.location statusAddress) ∧
      Resolve finish statusAddress statusAddress ∧ readCell finish statusAddress = some [.tag rejected] ∧
      start.nextLocation < finish.nextLocation ∧ finish.aliases = start.aliases ∧
      BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  obtain ⟨queried, afterFields, afterAlloc, pairAddress, values, queryStep, fieldEvals,
    allocated, initialized, resultEq⟩ := checked_tuple_inversion pair evaluation
  obtain ⟨middle, actualLedger, actualStatus, ledgerEval, statusEval, sameValues⟩ :=
    pair_fields_inversion fieldEvals
  obtain ⟨actualBinding, sameStore⟩ := variable_inversion ledgerShape ledgerEval
  have ledgerBound : CoreEval.lookup (extend env pair.contextBinder .context) ledgerName = some ledger := by
    rw [lookup_extended_other env pair.contextBinder ledgerName ledgerFresh]
    exact ledgerBinding
  have ledgerEq : actualLedger = ledger := by simpa [ledgerBound] using actualBinding.symm
  subst actualLedger
  subst middle
  subst values
  have queryBound := query_preserves_bounded start queried .hostDefault .hostDefault bounded queryStep
  obtain ⟨statusAddress, statusEq, statusFresh, _, statusCell, statusAliases, statusBound, statusRetained⟩ :=
    checked_nullary_retains status queryBound statusEval
  subst actualStatus
  have allocatePair : allocate .hostDefault ([ledger, .location statusAddress] : List Value).length true afterFields =
      some (pairAddress, afterAlloc) := by simpa using allocated
  have initializePair : initializeStorage pairAddress ([ledger, .location statusAddress] : List Value).length
      [ledger, .location statusAddress] afterAlloc = some ([ledger, .location statusAddress], finish) := by
    simpa [storedFields] using initialized
  obtain ⟨pairFresh, _, pairCell, pairAliases, finalBound, pairRetained⟩ :=
    host_allocation_retains statusBound allocatePair initializePair
  have queryAliases : queried.aliases = start.aliases := by
    simp only [query, Option.some.injEq, Prod.mk.injEq] at queryStep
    rcases queryStep with ⟨_, rfl⟩
    rfl
  have aliases : finish.aliases = start.aliases := pairAliases.trans (statusAliases.trans queryAliases)
  have finalStatus := pairRetained statusAddress _ statusCell
  have statusNoAlias : readAlias finish statusAddress = none := by
    simpa [readAlias, pairAliases, statusAliases, statusFresh] using bounded_fresh_no_alias queried queryBound
  have pairNoAlias : readAlias finish pairAddress = none := by
    simpa [readAlias, pairAliases, pairFresh] using bounded_fresh_no_alias afterFields statusBound
  have resultRep : Result finish result ledger (.location statusAddress) := by
    rw [resultEq]
    exact Result.pair pairAddress pairAddress ledger (.location statusAddress)
      (Resolve.cell pairAddress [ledger, .location statusAddress] pairNoAlias pairCell) pairCell
  have progress : start.nextLocation < finish.nextLocation := by
    have statusLive := finalBound.2.1 statusAddress _ (readCell_member finish statusAddress _ finalStatus)
    have queryNext : queried.nextLocation = start.nextLocation := by
      simp only [query, Option.some.injEq, Prod.mk.injEq] at queryStep
      rcases queryStep with ⟨_, rfl⟩
      rfl
    rw [statusFresh, queryNext] at statusLive
    exact statusLive
  refine ⟨statusAddress, resultRep,
    Resolve.cell statusAddress [.tag rejected] statusNoAlias finalStatus, finalStatus,
    progress, aliases, finalBound, ?_⟩
  intro address old read
  exact pairRetained address old (statusRetained address old (query_preserves_cell queryStep read))

/-- A missing lookup takes the actual rejection branch and returns the original ledger. -/
theorem registration_missing_branch (program : Program) (absent present rejected : Constructor)
    (branch call missingBody foundBody ledgerNode statusNode : NodeId) (name ledgerName : Binder)
    (env : Environment) (start finish : Store) (result ledger : Value)
    (branchShape : program branch = some (.caseMatch call
      [(.constructor absent none, missingBody), (.constructor present (some (.binder name)), foundBody)]))
    (lookupLaw : ∀ middle value, Eval program env call start value middle →
      LookupOutcome absent present start middle value none)
    (pair : CheckedTuple program missingBody none [ledgerNode, statusNode])
    (status : CheckedTuple program statusNode (some rejected) [])
    (ledgerShape : program ledgerNode = some (.variable ledgerName))
    (ledgerFresh : ledgerName ≠ pair.contextBinder)
    (ledgerBinding : CoreEval.lookup env ledgerName = some ledger)
    (evaluation : Eval program env branch start result finish) :
    ∃ statusAddress, Result finish result ledger (.location statusAddress) ∧
      Resolve finish statusAddress statusAddress ∧ readCell finish statusAddress = some [.tag rejected] ∧
      start.nextLocation < finish.nextLocation ∧ finish.aliases = start.aliases ∧
      BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  obtain ⟨middle, missingEval, lookupProgress, lookupAliases, lookupBound, lookupRetained⟩ :=
    registration_lookup_branch program absent present branch call missingBody foundBody name env start finish result none
      branchShape lookupLaw evaluation
  obtain ⟨statusAddress, resultRep, statusResolution, statusCell, rejectProgress, rejectAliases,
    finalBound, rejectRetained⟩ :=
    checked_rejected_result program missingBody ledgerNode statusNode rejected env middle finish result ledger
      ledgerName pair status ledgerShape ledgerFresh ledgerBinding lookupBound missingEval
  refine ⟨statusAddress, resultRep, statusResolution, statusCell,
    Nat.lt_trans lookupProgress rejectProgress, rejectAliases.trans lookupAliases, finalBound, ?_⟩
  intro address old read
  exact rejectRetained address old (lookupRetained address old read)

/-- A represented Closed phase selects its exact first branch. -/
theorem closed_phase_selects (store : Store) (closed openTag : Constructor)
    (address resolved : Nat) (closedBody openBody : NodeId)
    (resolution : Resolve store address resolved)
    (cell : readCell store resolved = some [.tag closed])
    {chosen : NodeId} {bindings : Environment}
    (selected : Selected store (.location address)
      [(.constructor closed none, closedBody), (.constructor openTag none, openBody)] chosen bindings) :
    chosen = closedBody ∧ bindings = [] := by
  cases selected with
  | first _ _ _ actual hit =>
    have same := nullary_constructor_match store closed address resolved resolution cell hit
    cases same
    exact ⟨rfl, rfl⟩
  | later _ _ _ _ _ miss next =>
    have impossible := nullary_constructor_match store closed address resolved resolution cell miss
    contradiction

/-- The actual Closed phase returns the original ledger and Rejected. -/
theorem registration_closed_branch (program : Program) (closed openTag rejected : Constructor)
    (branch phaseNode closedBody openBody ledgerNode statusNode : NodeId) (phaseName ledgerName : Binder)
    (env : Environment) (start finish : Store) (result ledger : Value) (phaseAddress phaseResolved : Nat)
    (branchShape : program branch = some (.caseMatch phaseNode
      [(.constructor closed none, closedBody), (.constructor openTag none, openBody)]))
    (phaseShape : program phaseNode = some (.variable phaseName))
    (phaseBinding : CoreEval.lookup env phaseName = some (.location phaseAddress))
    (phaseResolution : Resolve start phaseAddress phaseResolved)
    (phaseCell : readCell start phaseResolved = some [.tag closed])
    (pair : CheckedTuple program closedBody none [ledgerNode, statusNode])
    (status : CheckedTuple program statusNode (some rejected) [])
    (ledgerShape : program ledgerNode = some (.variable ledgerName))
    (ledgerFresh : ledgerName ≠ pair.contextBinder)
    (ledgerBinding : CoreEval.lookup env ledgerName = some ledger)
    (bounded : BoundedLocations start) (evaluation : Eval program env branch start result finish) :
    ∃ statusAddress, Result finish result ledger (.location statusAddress) ∧
      Resolve finish statusAddress statusAddress ∧ readCell finish statusAddress = some [.tag rejected] ∧
      start.nextLocation < finish.nextLocation ∧ finish.aliases = start.aliases ∧
      BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  obtain ⟨middle, value, chosen, bindings, phaseEval, selected, bodyEval⟩ :=
    case_match_inversion branchShape evaluation
  obtain ⟨actualBinding, sameStore⟩ := variable_inversion phaseShape phaseEval
  have phaseEq : value = .location phaseAddress := by simpa [phaseBinding] using actualBinding.symm
  subst value
  subst middle
  obtain ⟨sameBody, sameBindings⟩ := closed_phase_selects start closed openTag phaseAddress phaseResolved
    closedBody openBody phaseResolution phaseCell selected
  subst chosen
  subst bindings
  exact checked_rejected_result program closedBody ledgerNode statusNode rejected env start finish result ledger
    ledgerName pair status ledgerShape ledgerFresh ledgerBinding bounded (by simpa using bodyEval)

/-- The actual stored update call returns the finite first-match replacement. -/
theorem checked_record_update_call (c : Constructors) (program : Program)
    (checked : Ash.NetworkLedger.CoreRecordUpdate.CheckedRecordUpdate c program)
    (projection : RecordProjectionShape program checked.projection)
    (projectionFunctionName : projection.functionName = checked.projectionName)
    (projectionEntryName : projection.recordName = checked.entryName)
    (projectionCode : projection.code = checked.projectionCode)
    (call function argument wantedNode replacementNode listNode : NodeId) (env : Environment)
    (start finish : Store) (result wanted replacement list : Value) (queryId : Id) (key : Value → Id) (entries : List Value)
    (callName wantedName replacementName listName : Binder) (selfAddress selfResolved comparisonAddress comparisonResolved
      projectionAddress projectionResolved : Nat)
    (captureValues : List Value) (captureEnv : Environment)
    (triple : CheckedTuple program argument none [wantedNode, replacementNode, listNode])
    (callShape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable callName))
    (functionBinding : CoreEval.lookup env callName = some (.location selfAddress))
    (wantedShape : program wantedNode = some (.variable wantedName))
    (replacementShape : program replacementNode = some (.variable replacementName))
    (listShape : program listNode = some (.variable listName))
    (wantedFresh : wantedName ≠ triple.contextBinder) (replacementFresh : replacementName ≠ triple.contextBinder)
    (listFresh : listName ≠ triple.contextBinder)
    (wantedBinding : CoreEval.lookup env wantedName = some wanted)
    (replacementBinding : CoreEval.lookup env replacementName = some replacement)
    (listBinding : CoreEval.lookup env listName = some list)
    (selfBinding : CoreEval.lookup captureEnv.reverse checked.functionName = some (.location selfAddress))
    (comparisonBinding : CoreEval.lookup captureEnv.reverse checked.comparisonName = some (.location comparisonAddress))
    (projectionBinding : CoreEval.lookup captureEnv.reverse checked.projectionName = some (.location projectionAddress))
    (captureBindings : CaptureBindings program checked.captureNodes captureValues captureEnv)
    (selfResolution : Resolve start selfAddress selfResolved)
    (selfCell : readCell start selfResolved = some (.closureCode checked.code :: captureValues))
    (comparisonResolution : Resolve start comparisonAddress comparisonResolved)
    (comparisonCell : readCell start comparisonResolved = some [.closureCode checked.comparator.code])
    (projectionResolution : Resolve start projectionAddress projectionResolved)
    (projectionCell : readCell start projectionResolved = some [.closureCode checked.projectionCode])
    (bounded : BoundedLocations start) (wantedRep : Ident c start wanted queryId)
    (listRep : Children c start list entries)
    (keys : RepresentedEntries c (RecordEntry projection.record) start key entries)
    (evaluation : Eval program env call start result finish) :
    Ash.NetworkLedger.CoreInsert.InsertOutcome c start finish result
      (Ash.NetworkLedger.update key queryId replacement entries) := by
  obtain ⟨afterArgument, payload, bodyEval, payloadResolution, payloadCell, argumentProgress,
    argumentAliases, argumentBound, argumentRetained⟩ :=
    Ash.NetworkLedger.CoreRecordUpdate.checked_update_recursive_call program call function argument wantedNode replacementNode
      listNode env start finish result wanted replacement list callName wantedName replacementName listName
      selfAddress selfResolved checked.code checked.context checked.storage checked.parameter checked.body
      checked.captureNodes captureValues captureEnv triple callShape functionShape functionBinding selfResolution selfCell
      checked.closureShape captureBindings wantedShape replacementShape listShape wantedFresh replacementFresh listFresh
      wantedBinding replacementBinding listBinding bounded evaluation
  have wantedAfter := ident_retained c start afterArgument wanted queryId argumentAliases argumentRetained wantedRep
  have listAfter := children_retained c start afterArgument list entries argumentAliases argumentRetained listRep
  have keysAfter := represented_entries_retained c (RecordEntry projection.record) start afterArgument key entries
    (record_entry_retained projection.record) argumentAliases argumentRetained keys
  have selfAfter := resolve_preserved argumentAliases argumentRetained selfResolution
  have selfCellAfter := argumentRetained selfResolved _ selfCell
  have comparisonAfter := resolve_preserved argumentAliases argumentRetained comparisonResolution
  have comparisonCellAfter := argumentRetained comparisonResolved _ comparisonCell
  have projectionAfter := resolve_preserved argumentAliases argumentRetained projectionResolution
  have projectionCellAfter := argumentRetained projectionResolved _ projectionCell
  obtain ⟨returned, updateProgress, updateAliases, finalBound, updateRetained⟩ :=
    Ash.NetworkLedger.CoreRecordUpdate.record_update_body_correct c program checked projection projectionFunctionName
      projectionEntryName projectionCode captureValues captureEnv selfAddress selfResolved comparisonAddress comparisonResolved
      projectionAddress projectionResolved wanted replacement queryId key entries selfBinding comparisonBinding projectionBinding
      captureBindings afterArgument finish payload payload list result payloadResolution payloadCell argumentBound wantedAfter
      listAfter keysAfter selfAfter selfCellAfter comparisonAfter comparisonCellAfter projectionAfter projectionCellAfter bodyEval
  have aliases : finish.aliases = start.aliases := updateAliases.trans argumentAliases
  refine ⟨returned, ?_, aliases, finalBound, ?_⟩
  · omega
  · intro address old read
    exact updateRetained address old (argumentRetained address old read)

/-- A stored append call preserves the whole finite spine and appends one value. -/
theorem checked_spine_append_call (c : Constructors) (program : Program)
    (checked : Ash.NetworkLedger.CoreInsert.CheckedInsert c program)
    (call function argument newNode listNode : NodeId) (env : Environment)
    (start finish : Store) (result newEntry list : Value) (newAddress : Nat) (entries : List Value)
    (callName newName listName : Binder) (selfAddress selfResolved : Nat)
    (captureValues : List Value) (captureEnv : Environment)
    (pair : CheckedTuple program argument none [newNode, listNode])
    (callShape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable callName))
    (functionBinding : CoreEval.lookup env callName = some (.location selfAddress))
    (newShape : program newNode = some (.variable newName))
    (listShape : program listNode = some (.variable listName))
    (newFresh : newName ≠ pair.contextBinder) (listFresh : listName ≠ pair.contextBinder)
    (newBinding : CoreEval.lookup env newName = some newEntry)
    (listBinding : CoreEval.lookup env listName = some list)
    (newLocation : newEntry = .location newAddress)
    (selfBinding : CoreEval.lookup captureEnv.reverse checked.functionName = some (.location selfAddress))
    (captureBindings : CaptureBindings program checked.captureNodes captureValues captureEnv)
    (selfResolution : Resolve start selfAddress selfResolved)
    (selfCell : readCell start selfResolved = some (.closureCode checked.code :: captureValues))
    (bounded : BoundedLocations start) (listRep : Children c start list entries)
    (located : Ash.NetworkLedger.CoreGenericInsert.LocatedEntries entries)
    (evaluation : Eval program env call start result finish) :
    Ash.NetworkLedger.CoreInsert.InsertOutcome c start finish result (entries ++ [newEntry]) := by
  obtain ⟨afterArgument, payload, bodyEval, payloadResolution, payloadCell, argumentProgress,
    argumentAliases, argumentBound, argumentRetained⟩ :=
    checked_recursive_call program call function argument newNode listNode env start finish result newEntry list
      callName newName listName selfAddress selfResolved checked.code checked.context checked.storage
      checked.parameter checked.body checked.captureNodes captureValues captureEnv pair callShape functionShape
      functionBinding selfResolution selfCell checked.closureShape captureBindings newShape listShape newFresh listFresh
      newBinding listBinding bounded evaluation
  have listAfter := children_retained c start afterArgument list entries argumentAliases argumentRetained listRep
  have selfAfter := resolve_preserved argumentAliases argumentRetained selfResolution
  have selfCellAfter := argumentRetained selfResolved _ selfCell
  obtain ⟨returned, appendProgress, appendAliases, finalBound, appendRetained⟩ :=
    Ash.NetworkLedger.CoreGenericInsert.insertion_body_located c program checked captureValues captureEnv
      selfAddress selfResolved newEntry newAddress newLocation entries selfBinding captureBindings
      afterArgument finish payload payload list result payloadResolution payloadCell argumentBound listAfter located
      selfAfter selfCellAfter bodyEval
  have aliases : finish.aliases = start.aliases := appendAliases.trans argumentAliases
  refine ⟨returned, ?_, aliases, finalBound, ?_⟩
  · omega
  · intro address old read
    exact appendRetained address old (argumentRetained address old read)

/-- An append whose first argument is an actual allocating constructor expression. -/
theorem checked_spine_append_expression (c : Constructors) (program : Program)
    (checked : Ash.NetworkLedger.CoreInsert.CheckedInsert c program)
    (R : Store → Value → Prop)
    (relationRetained : ∀ before after value, after.aliases = before.aliases →
      (∀ address old, readCell before address = some old → readCell after address = some old) →
      R before value → R after value)
    (call function argument newNode listNode : NodeId) (env : Environment)
    (start finish : Store) (result list : Value) (entries : List Value)
    (callName listName : Binder) (selfAddress selfResolved : Nat)
    (captureValues : List Value) (captureEnv : Environment)
    (pair : CheckedTuple program argument none [newNode, listNode])
    (callShape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable callName))
    (functionBinding : CoreEval.lookup env callName = some (.location selfAddress))
    (listShape : program listNode = some (.variable listName))
    (listFresh : listName ≠ pair.contextBinder)
    (listBinding : CoreEval.lookup env listName = some list)
    (newLaw : ∀ before after value,
      BoundedLocations before →
      Eval program (extend env pair.contextBinder .context) newNode before value after →
      (∃ address, value = .location address) ∧ R after value ∧
      before.nextLocation ≤ after.nextLocation ∧
      after.aliases = before.aliases ∧ BoundedLocations after ∧
      (∀ address old, readCell before address = some old → readCell after address = some old))
    (selfBinding : CoreEval.lookup captureEnv.reverse checked.functionName = some (.location selfAddress))
    (captureBindings : CaptureBindings program checked.captureNodes captureValues captureEnv)
    (selfResolution : Resolve start selfAddress selfResolved)
    (selfCell : readCell start selfResolved = some (.closureCode checked.code :: captureValues))
    (bounded : BoundedLocations start) (listRep : Children c start list entries)
    (located : Ash.NetworkLedger.CoreGenericInsert.LocatedEntries entries)
    (evaluation : Eval program env call start result finish) :
    ∃ newEntry, R finish newEntry ∧
      Ash.NetworkLedger.CoreInsert.InsertOutcome c start finish result (entries ++ [newEntry]) := by
  obtain ⟨afterFunction, afterArgument, callable, argumentValue, actualParameter, actualBody, captured,
    functionEval, target, argumentEval, bodyEval⟩ := apply_inversion callShape evaluation
  obtain ⟨actualFunction, functionState⟩ := variable_inversion functionShape functionEval
  have sameFunction : callable = .location selfAddress := by simpa [functionBinding] using actualFunction.symm
  subst callable
  subst afterFunction
  obtain ⟨sameParameter, sameBody, sameCapture⟩ :=
    captured_target program start selfAddress selfResolved checked.code checked.context checked.storage checked.parameter
      checked.body checked.captureNodes captureValues captureEnv selfResolution selfCell checked.closureShape captureBindings target
  subst actualParameter
  subst actualBody
  subst captured
  obtain ⟨queried, afterFields, afterAlloc, location, values, queryStep, fieldEvals,
    allocated, initialized, resultEq⟩ := checked_tuple_inversion pair argumentEval
  obtain ⟨middle, newEntry, actualList, newEval, listEval, sameValues⟩ := pair_fields_inversion fieldEvals
  have queryBound := query_preserves_bounded start queried .hostDefault .hostDefault bounded queryStep
  obtain ⟨⟨newAddress, newLocation⟩, newRep, newProgress, newAliases, newBound, newRetained⟩ := newLaw queried middle newEntry queryBound newEval
  obtain ⟨actualListBinding, listStore⟩ := variable_inversion listShape listEval
  have listBound : CoreEval.lookup (extend env pair.contextBinder .context) listName = some list := by
    rw [lookup_extended_other env pair.contextBinder listName listFresh]
    exact listBinding
  have listEq : actualList = list := by simpa [listBound] using actualListBinding.symm
  subst actualList
  subst afterFields
  subst values
  have allocatePair : allocate .hostDefault ([newEntry, list] : List Value).length true middle =
      some (location, afterAlloc) := by simpa using allocated
  have initializePair : initializeStorage location ([newEntry, list] : List Value).length
      [newEntry, list] afterAlloc = some ([newEntry, list], afterArgument) := by simpa [storedFields] using initialized
  obtain ⟨fresh, advances, pairCell, pairAliases, argumentBound, pairRetained⟩ :=
    host_allocation_retains newBound allocatePair initializePair
  have queryAliases : queried.aliases = start.aliases := by
    simp only [query, Option.some.injEq, Prod.mk.injEq] at queryStep
    rcases queryStep with ⟨_, rfl⟩
    rfl
  have argumentAliases : afterArgument.aliases = start.aliases := pairAliases.trans (newAliases.trans queryAliases)
  have argumentRetained : ∀ address old, readCell start address = some old → readCell afterArgument address = some old := by
    intro address old read
    exact pairRetained address old (newRetained address old (query_preserves_cell queryStep read))
  have payloadNoAlias : readAlias afterArgument location = none := by
    simpa [readAlias, pairAliases, fresh] using bounded_fresh_no_alias middle newBound
  have payloadResolution : Resolve afterArgument location location :=
    Resolve.cell location [newEntry, list] payloadNoAlias pairCell
  have listAfter := children_retained c start afterArgument list entries argumentAliases argumentRetained listRep
  have selfAfter := resolve_preserved argumentAliases argumentRetained selfResolution
  have selfCellAfter := argumentRetained selfResolved _ selfCell
  have newAfter := relationRetained middle afterArgument newEntry pairAliases pairRetained newRep
  subst argumentValue
  obtain ⟨returned, appendProgress, appendAliases, finalBound, appendRetained⟩ :=
    Ash.NetworkLedger.CoreGenericInsert.insertion_body_located c program checked captureValues captureEnv
      selfAddress selfResolved newEntry newAddress newLocation entries selfBinding captureBindings
      afterArgument finish location location list result payloadResolution pairCell argumentBound listAfter located
      selfAfter selfCellAfter bodyEval
  have aliases : finish.aliases = start.aliases := appendAliases.trans argumentAliases
  have finalRep := relationRetained afterArgument finish newEntry appendAliases appendRetained newAfter
  have progress : start.nextLocation < finish.nextLocation := by
    have queryNext : queried.nextLocation = start.nextLocation := by
      simp only [query, Option.some.injEq, Prod.mk.injEq] at queryStep
      rcases queryStep with ⟨_, rfl⟩
      rfl
    omega
  refine ⟨newEntry, finalRep, returned, progress, aliases, finalBound, ?_⟩
  intro address old read
  exact appendRetained address old (argumentRetained address old read)


/-- The actual Child constructor retains the exact identifier and destination fields. -/
def ChildEntry (tag : Constructor) (store : Store) (value child destination : Value) : Prop :=
  ∃ address payload, value = .location address ∧
    Resolve store address address ∧ readCell store address = some [.tag tag, .location payload] ∧
    Resolve store payload payload ∧ readCell store payload = some [child, destination]

theorem child_entry_retained (tag : Constructor) (before after : Store)
    (entry child destination : Value) (aliases : after.aliases = before.aliases)
    (cells : ∀ location old, readCell before location = some old → readCell after location = some old)
    (entryRep : ChildEntry tag before entry child destination) :
    ChildEntry tag after entry child destination := by
  obtain ⟨address, payload, same, resolution, cell, payloadResolution, fields⟩ := entryRep
  exact ⟨address, payload, same, resolve_preserved aliases cells resolution, cells address _ cell,
    resolve_preserved aliases cells payloadResolution, cells payload _ fields⟩

theorem checked_child_constructor (program : Program)
    (call function argument childNode destinationNode operand : NodeId) (tag : Constructor)
    (closure : CheckedClosure program function)
    (pair : CheckedTuple program argument none [childNode, destinationNode])
    (constructor : CheckedTuple program closure.body (some tag) [operand])
    (env : Environment) (start finish : Store) (result child destination : Value)
    (childName destinationName : Binder)
    (callShape : program call = some (.apply function argument))
    (childShape : program childNode = some (.variable childName))
    (destinationShape : program destinationNode = some (.variable destinationName))
    (childFresh : childName ≠ pair.contextBinder) (destinationFresh : destinationName ≠ pair.contextBinder)
    (childBinding : CoreEval.lookup env childName = some child)
    (destinationBinding : CoreEval.lookup env destinationName = some destination)
    (operandShape : program operand = some (.variable closure.parameter))
    (operandFresh : closure.parameter ≠ constructor.contextBinder)
    (bounded : BoundedLocations start) (evaluation : Eval program env call start result finish) :
    (∃ address, result = .location address) ∧ ChildEntry tag finish result child destination ∧
      start.nextLocation ≤ finish.nextLocation ∧ finish.aliases = start.aliases ∧
      BoundedLocations finish ∧
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
    checked_variable_pair_retains pair childName destinationName childShape destinationShape childFresh destinationFresh
      childBinding destinationBinding closureBound argumentEval
  subst argumentValue
  have operandBinding : CoreEval.lookup (extend [] closure.parameter (.location payload)) closure.parameter =
      some (.location payload) := by simp [CoreEval.lookup, extend]
  obtain ⟨address, resultEq, addressFresh, _, cell, resultAliases, finalBound, resultRetained⟩ :=
    checked_unary_constructor_retains constructor closure.parameter operandShape operandFresh operandBinding
      payloadBound bodyEval
  have aliases : finish.aliases = start.aliases := resultAliases.trans (payloadAliases.trans closureAliases)
  have retained : ∀ location old, readCell start location = some old → readCell finish location = some old := by
    intro location old read
    exact resultRetained location old (payloadRetained location old (closureRetained location old read))
  have noAlias : readAlias finish address = none := by
    simpa [readAlias, resultAliases, addressFresh] using bounded_fresh_no_alias afterArgument payloadBound
  have payloadNoAlias : readAlias finish payload = none := by
    simpa [readAlias, resultAliases, payloadAliases, payloadFresh] using bounded_fresh_no_alias afterFunction closureBound
  have finalPayload := resultRetained payload _ payloadCell
  have progress : start.nextLocation ≤ finish.nextLocation := by
    have live := finalBound.2.1 closureLocation _
      (readCell_member finish closureLocation _ (resultRetained closureLocation _ (payloadRetained closureLocation _ closureCell)))
    rw [closureFresh] at live
    omega
  exact ⟨⟨address, resultEq⟩, ⟨address, payload, resultEq,
    Resolve.cell address [.tag tag, .location payload] noAlias cell, cell,
    Resolve.cell payload [child, destination] payloadNoAlias finalPayload, finalPayload⟩,
    progress, aliases, finalBound, retained⟩

/-- The real nested Child construction is evaluated before the stored append. -/
theorem checked_append_child_call (c : Constructors) (program : Program)
    (checked : Ash.NetworkLedger.CoreInsert.CheckedInsert c program)
    (call function argument childCall listNode childFunction childArguments childNode destinationNode operand : NodeId)
    (childTag : Constructor) (env : Environment) (start finish : Store)
    (result list child destination : Value) (entries : List Value)
    (callName listName childName destinationName : Binder) (selfAddress selfResolved : Nat)
    (captureValues : List Value) (captureEnv : Environment)
    (outerPair : CheckedTuple program argument none [childCall, listNode])
    (closure : CheckedClosure program childFunction)
    (childPair : CheckedTuple program childArguments none [childNode, destinationNode])
    (constructor : CheckedTuple program closure.body (some childTag) [operand])
    (callShape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable callName))
    (functionBinding : CoreEval.lookup env callName = some (.location selfAddress))
    (listShape : program listNode = some (.variable listName))
    (listFresh : listName ≠ outerPair.contextBinder)
    (listBinding : CoreEval.lookup env listName = some list)
    (childCallShape : program childCall = some (.apply childFunction childArguments))
    (childShape : program childNode = some (.variable childName))
    (destinationShape : program destinationNode = some (.variable destinationName))
    (childOuterFresh : childName ≠ outerPair.contextBinder)
    (destinationOuterFresh : destinationName ≠ outerPair.contextBinder)
    (childFresh : childName ≠ childPair.contextBinder)
    (destinationFresh : destinationName ≠ childPair.contextBinder)
    (childBinding : CoreEval.lookup env childName = some child)
    (destinationBinding : CoreEval.lookup env destinationName = some destination)
    (operandShape : program operand = some (.variable closure.parameter))
    (operandFresh : closure.parameter ≠ constructor.contextBinder)
    (selfBinding : CoreEval.lookup captureEnv.reverse checked.functionName = some (.location selfAddress))
    (captureBindings : CaptureBindings program checked.captureNodes captureValues captureEnv)
    (selfResolution : Resolve start selfAddress selfResolved)
    (selfCell : readCell start selfResolved = some (.closureCode checked.code :: captureValues))
    (bounded : BoundedLocations start) (listRep : Children c start list entries)
    (located : Ash.NetworkLedger.CoreGenericInsert.LocatedEntries entries)
    (evaluation : Eval program env call start result finish) :
    ∃ newEntry, ChildEntry childTag finish newEntry child destination ∧
      Ash.NetworkLedger.CoreInsert.InsertOutcome c start finish result (entries ++ [newEntry]) := by
  apply checked_spine_append_expression c program checked (fun state entry => ChildEntry childTag state entry child destination)
    (fun before after entry aliases cells rep => child_entry_retained childTag before after entry child destination aliases cells rep)
    call function argument childCall listNode env start finish result list entries callName listName selfAddress selfResolved
    captureValues captureEnv outerPair callShape functionShape functionBinding listShape listFresh listBinding
  · intro before after value beforeBound constructorEval
    have childBound : CoreEval.lookup (extend env outerPair.contextBinder .context) childName = some child := by
      rw [lookup_extended_other env outerPair.contextBinder childName childOuterFresh]
      exact childBinding
    have destinationBound : CoreEval.lookup (extend env outerPair.contextBinder .context) destinationName = some destination := by
      rw [lookup_extended_other env outerPair.contextBinder destinationName destinationOuterFresh]
      exact destinationBinding
    exact checked_child_constructor program childCall childFunction childArguments childNode destinationNode operand childTag
      closure childPair constructor _ before after value child destination childName destinationName childCallShape childShape
      destinationShape childFresh destinationFresh childBound destinationBound operandShape operandFresh beforeBound constructorEval
  · exact selfBinding
  · exact captureBindings
  · exact selfResolution
  · exact selfCell
  · exact bounded
  · exact listRep
  · exact located
  · exact evaluation

/-- The checked successful branch evaluates the four real initializers in order. -/
theorem registration_commit_steps (program : Program) (env : Environment)
    (first second third fourth resultNode workNode replacementNode updateNode outputNode : NodeId)
    (workName replacementName remainingName outgoingName : Binder)
    (start finish : Store) (result : Value)
    (firstShape : program first = some (.bind workName workNode second))
    (secondShape : program second = some (.bind replacementName replacementNode third))
    (thirdShape : program third = some (.bind remainingName updateNode fourth))
    (fourthShape : program fourth = some (.bind outgoingName outputNode resultNode))
    (evaluation : Eval program env first start result finish) :
    ∃ afterWork afterReplacement afterUpdate afterOutput work replacement remaining outgoing,
      Eval program env workNode start work afterWork ∧
      Eval program (extend env workName work) replacementNode afterWork replacement afterReplacement ∧
      Eval program (extend (extend env workName work) replacementName replacement)
        updateNode afterReplacement remaining afterUpdate ∧
      Eval program (extend (extend (extend env workName work) replacementName replacement) remainingName remaining)
        outputNode afterUpdate outgoing afterOutput ∧
      Eval program (extend (extend (extend (extend env workName work) replacementName replacement)
        remainingName remaining) outgoingName outgoing) resultNode afterOutput result finish := by
  obtain ⟨afterWork, work, workEval, rest⟩ := bind_inversion firstShape evaluation
  obtain ⟨afterReplacement, replacement, replacementEval, rest⟩ := bind_inversion secondShape rest
  obtain ⟨afterUpdate, remaining, updateEval, rest⟩ := bind_inversion thirdShape rest
  obtain ⟨afterOutput, outgoing, outputEval, resultEval⟩ := bind_inversion fourthShape rest
  exact ⟨afterWork, afterReplacement, afterUpdate, afterOutput, work, replacement, remaining, outgoing,
    workEval, replacementEval, updateEval, outputEval, resultEval⟩

/-- An actual Open phase selects the second checked branch. -/
theorem open_phase_selects (store : Store) (closed openTag : Constructor)
    (address resolved : Nat) (closedBody openBody : NodeId) (different : openTag ≠ closed)
    (resolution : Resolve store address resolved)
    (cell : readCell store resolved = some [.tag openTag])
    {chosen : NodeId} {bindings : Environment}
    (selected : Selected store (.location address)
      [(.constructor closed none, closedBody), (.constructor openTag none, openBody)] chosen bindings) :
    chosen = openBody ∧ bindings = [] := by
  cases selected with
  | first _ _ _ _ hit =>
    have impossible := different_nullary_constructor_misses store closed openTag address resolved different resolution cell hit
    contradiction
  | later _ _ _ _ _ miss next =>
    cases next with
    | first _ _ _ _ hit =>
      have same := nullary_constructor_match store openTag address resolved resolution cell hit
      cases same
      exact ⟨rfl, rfl⟩
    | later _ _ _ _ _ _ impossible => cases impossible

/-- A represented Open phase evaluates the actual checked successful branch. -/
theorem registration_open_branch (program : Program) (closed openTag : Constructor)
    (branch phaseNode closedBody openBody : NodeId) (phaseName : Binder) (env : Environment)
    (start finish : Store) (result : Value) (phaseAddress phaseResolved : Nat)
    (different : openTag ≠ closed)
    (branchShape : program branch = some (.caseMatch phaseNode
      [(.constructor closed none, closedBody), (.constructor openTag none, openBody)]))
    (phaseShape : program phaseNode = some (.variable phaseName))
    (phaseBinding : CoreEval.lookup env phaseName = some (.location phaseAddress))
    (phaseResolution : Resolve start phaseAddress phaseResolved)
    (phaseCell : readCell start phaseResolved = some [.tag openTag])
    (evaluation : Eval program env branch start result finish) :
    Eval program env openBody start result finish := by
  obtain ⟨middle, value, chosen, bindings, phaseEval, selected, bodyEval⟩ :=
    case_match_inversion branchShape evaluation
  obtain ⟨actualBinding, sameStore⟩ := variable_inversion phaseShape phaseEval
  have phaseEq : value = .location phaseAddress := by simpa [phaseBinding] using actualBinding.symm
  subst value
  subst middle
  obtain ⟨sameBody, sameBindings⟩ := open_phase_selects start closed openTag phaseAddress phaseResolved
    closedBody openBody different phaseResolution phaseCell selected
  subst chosen
  subst bindings
  simpa using bodyEval

/-- A checked nominal constructor keeps its exact ordered payload fields. -/
def NominalFields (tag : Constructor) (store : Store) (value : Value) (fields : List Value) : Prop :=
  ∃ address resolved payload tuple,
    value = .location address ∧
    Resolve store address resolved ∧ readCell store resolved = some [.tag tag, .location payload] ∧
    Resolve store payload tuple ∧ readCell store tuple = some fields

/-- The same constructor fields remain readable when old cells and aliases are retained. -/
theorem nominal_fields_retained (tag : Constructor) (before after : Store)
    (value : Value) (fields : List Value) (aliases : after.aliases = before.aliases)
    (cells : ∀ location old, readCell before location = some old → readCell after location = some old)
    (rep : NominalFields tag before value fields) : NominalFields tag after value fields := by
  obtain ⟨address, resolved, payload, tuple, same, resolution, cell, payloadResolution, payloadCell⟩ := rep
  exact ⟨address, resolved, payload, tuple, same, resolve_preserved aliases cells resolution,
    cells resolved _ cell, resolve_preserved aliases cells payloadResolution, cells tuple _ payloadCell⟩

/-- A checked constructor wraps the exact payload produced by its argument. -/
theorem checked_nominal_from_payload (program : Program)
    (call function argument operand : NodeId) (tag : Constructor)
    (closure : CheckedClosure program function)
    (constructor : CheckedTuple program closure.body (some tag) [operand])
    (env : Environment) (start finish : Store) (result : Value) (fields : List Value)
    (callShape : program call = some (.apply function argument))
    (operandShape : program operand = some (.variable closure.parameter))
    (operandFresh : closure.parameter ≠ constructor.contextBinder)
    (payloadLaw : ∀ before after value, BoundedLocations before →
      Eval program env argument before value after →
      ∃ payload, value = .location payload ∧ Resolve after payload payload ∧
        readCell after payload = some fields ∧
        after.aliases = before.aliases ∧ BoundedLocations after ∧
        (∀ address old, readCell before address = some old → readCell after address = some old))
    (bounded : BoundedLocations start) (evaluation : Eval program env call start result finish) :
    (∃ address, result = .location address) ∧ NominalFields tag finish result fields ∧
      start.nextLocation ≤ finish.nextLocation ∧ finish.aliases = start.aliases ∧
      BoundedLocations finish ∧
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
  obtain ⟨payload, payloadEq, payloadResolution, payloadCell, payloadAliases, payloadBound, payloadRetained⟩ :=
    payloadLaw afterFunction afterArgument argumentValue closureBound argumentEval
  subst argumentValue
  have operandBinding : CoreEval.lookup (extend [] closure.parameter (.location payload)) closure.parameter =
      some (.location payload) := by simp [CoreEval.lookup, extend]
  obtain ⟨address, resultEq, addressFresh, _, cell, resultAliases, finalBound, resultRetained⟩ :=
    checked_unary_constructor_retains constructor closure.parameter operandShape operandFresh operandBinding
      payloadBound bodyEval
  have aliases : finish.aliases = start.aliases := resultAliases.trans (payloadAliases.trans closureAliases)
  have retained : ∀ location old, readCell start location = some old → readCell finish location = some old := by
    intro location old read
    exact resultRetained location old (payloadRetained location old (closureRetained location old read))
  have noAlias : readAlias finish address = none := by
    simpa [readAlias, resultAliases, addressFresh] using bounded_fresh_no_alias afterArgument payloadBound
  have progress : start.nextLocation ≤ finish.nextLocation := by
    have live := finalBound.2.1 closureLocation _
      (readCell_member finish closureLocation _ (resultRetained closureLocation _ (payloadRetained closureLocation _ closureCell)))
    rw [closureFresh] at live
    omega
  exact ⟨⟨address, resultEq⟩, ⟨address, address, payload, payload, resultEq,
    Resolve.cell address [.tag tag, .location payload] noAlias cell, cell,
    resolve_preserved resultAliases resultRetained payloadResolution, resultRetained payload _ payloadCell⟩,
    progress, aliases, finalBound, retained⟩

/-- The Ledger payload evaluates Add first and then the actual records and outputs. -/
theorem checked_successor_arguments (program : Program) (buffers : Ash.NetworkLedger.CoreIncrement.Buffers)
    (increment : Ash.NetworkLedger.CoreIncrement.CheckedIncrement program buffers)
    (root remainingNode outgoingNode : NodeId) (env : Environment) (start finish : Store)
    (result remaining outgoing : Value) (counter : Int) (remainingName outgoingName : Binder)
    (tuple : CheckedTuple program root none [increment.root, remainingNode, outgoingNode])
    (remainingShape : program remainingNode = some (.variable remainingName))
    (outgoingShape : program outgoingNode = some (.variable outgoingName))
    (counterFresh : increment.counterBinder ≠ tuple.contextBinder)
    (remainingFresh : remainingName ≠ tuple.contextBinder) (outgoingFresh : outgoingName ≠ tuple.contextBinder)
    (counterBinding : CoreEval.lookup env increment.counterBinder = some (.integer counter))
    (remainingBinding : CoreEval.lookup env remainingName = some remaining)
    (outgoingBinding : CoreEval.lookup env outgoingName = some outgoing)
    (nonnegative : 0 ≤ counter) (bounded : BoundedLocations start)
    (evaluation : Eval program env root start result finish) :
    ∃ payload, result = .location payload ∧ Resolve finish payload payload ∧
      readCell finish payload = some [.integer (counter + 1), remaining, outgoing] ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  obtain ⟨queried, afterFields, afterAlloc, payload, values, queryStep, fieldEvals,
    allocated, initialized, resultEq⟩ := checked_tuple_inversion tuple evaluation
  have queryBound := query_preserves_bounded start queried .hostDefault .hostDefault bounded queryStep
  have counterBound : CoreEval.lookup (extend env tuple.contextBinder .context) increment.counterBinder =
      some (.integer counter) := by
    rw [lookup_extended_other env tuple.contextBinder increment.counterBinder counterFresh]
    exact counterBinding
  have remainingBound : CoreEval.lookup (extend env tuple.contextBinder .context) remainingName = some remaining := by
    rw [lookup_extended_other env tuple.contextBinder remainingName remainingFresh]
    exact remainingBinding
  have outgoingBound : CoreEval.lookup (extend env tuple.contextBinder .context) outgoingName = some outgoing := by
    rw [lookup_extended_other env tuple.contextBinder outgoingName outgoingFresh]
    exact outgoingBinding
  cases fieldEvals with
  | cons incrementEval rest =>
    obtain ⟨incrementEq, _, _, incrementAliases, incrementBound, incrementRetained⟩ :=
      Ash.NetworkLedger.CoreIncrement.checked_increment_from_eval program buffers increment _ queried _ _ counter
        counterBound nonnegative queryBound incrementEval
    cases rest with
    | cons remainingEval rest =>
      obtain ⟨remainingActual, remainingState⟩ := variable_inversion remainingShape remainingEval
      have remainingEq : _ := Option.some.inj (remainingActual.symm.trans remainingBound)
      subst remainingState
      cases rest with
      | cons outgoingEval rest =>
        obtain ⟨outgoingActual, outgoingState⟩ := variable_inversion outgoingShape outgoingEval
        have outgoingEq : _ := Option.some.inj (outgoingActual.symm.trans outgoingBound)
        subst outgoingState
        cases rest
        have alloc : allocate .hostDefault ([.integer (counter + 1), remaining, outgoing] : List Value).length
            true afterFields = some (payload, afterAlloc) := by simpa [incrementEq, remainingEq, outgoingEq] using allocated
        have init : initializeStorage payload ([.integer (counter + 1), remaining, outgoing] : List Value).length
            [.integer (counter + 1), remaining, outgoing] afterAlloc =
              some ([.integer (counter + 1), remaining, outgoing], finish) := by
          simpa [storedFields, incrementEq, remainingEq, outgoingEq] using initialized
        obtain ⟨fresh, _, cell, finalAliases, finalBound, finalRetained⟩ :=
          host_allocation_retains incrementBound alloc init
        have noAlias : readAlias finish payload = none := by
          simpa [readAlias, finalAliases, fresh] using bounded_fresh_no_alias afterFields incrementBound
        have queryAliases : queried.aliases = start.aliases := by
          simp only [query, Option.some.injEq, Prod.mk.injEq] at queryStep
          rcases queryStep with ⟨_, rfl⟩
          rfl
        refine ⟨payload, resultEq, Resolve.cell payload _ noAlias cell, cell,
          finalAliases.trans (incrementAliases.trans queryAliases), finalBound, ?_⟩
        intro address old read
        exact finalRetained address old (incrementRetained address old (query_preserves_cell queryStep read))

/-- Normal Ledger construction returns the checked successor counter and exact list operands. -/
theorem checked_successor_ledger (program : Program) (buffers : Ash.NetworkLedger.CoreIncrement.Buffers)
    (increment : Ash.NetworkLedger.CoreIncrement.CheckedIncrement program buffers)
    (call function argument remainingNode outgoingNode operand : NodeId) (ledgerTag : Constructor)
    (closure : CheckedClosure program function)
    (constructor : CheckedTuple program closure.body (some ledgerTag) [operand])
    (tuple : CheckedTuple program argument none [increment.root, remainingNode, outgoingNode])
    (env : Environment) (start finish : Store) (result remaining outgoing : Value)
    (counter : Int) (remainingName outgoingName : Binder)
    (callShape : program call = some (.apply function argument))
    (operandShape : program operand = some (.variable closure.parameter))
    (operandFresh : closure.parameter ≠ constructor.contextBinder)
    (remainingShape : program remainingNode = some (.variable remainingName))
    (outgoingShape : program outgoingNode = some (.variable outgoingName))
    (counterFresh : increment.counterBinder ≠ tuple.contextBinder)
    (remainingFresh : remainingName ≠ tuple.contextBinder) (outgoingFresh : outgoingName ≠ tuple.contextBinder)
    (counterBinding : CoreEval.lookup env increment.counterBinder = some (.integer counter))
    (remainingBinding : CoreEval.lookup env remainingName = some remaining)
    (outgoingBinding : CoreEval.lookup env outgoingName = some outgoing)
    (nonnegative : 0 ≤ counter) (bounded : BoundedLocations start)
    (evaluation : Eval program env call start result finish) :
    (∃ address, result = .location address) ∧
      NominalFields ledgerTag finish result [.integer (counter + 1), remaining, outgoing] ∧
      start.nextLocation ≤ finish.nextLocation ∧ finish.aliases = start.aliases ∧
      BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  apply checked_nominal_from_payload program call function argument operand ledgerTag closure constructor env start finish
    result [.integer (counter + 1), remaining, outgoing] callShape operandShape operandFresh
  · intro before after value beforeBound argumentEval
    exact checked_successor_arguments program buffers increment argument remainingNode outgoingNode env before after value
      remaining outgoing counter remainingName outgoingName tuple remainingShape outgoingShape counterFresh remainingFresh
      outgoingFresh counterBinding remainingBinding outgoingBinding nonnegative beforeBound argumentEval
  · exact bounded
  · exact evaluation

/-- The actual Registered constructor retains the exact issued identity. -/
theorem checked_registered_status (program : Program)
    (call function childNode operand : NodeId) (tag : Constructor)
    (closure : CheckedClosure program function)
    (constructor : CheckedTuple program closure.body (some tag) [operand])
    (env : Environment) (start finish : Store) (result child : Value) (childName : Binder)
    (callShape : program call = some (.apply function childNode))
    (childShape : program childNode = some (.variable childName))
    (childBinding : CoreEval.lookup env childName = some child)
    (operandShape : program operand = some (.variable closure.parameter))
    (operandFresh : closure.parameter ≠ constructor.contextBinder)
    (bounded : BoundedLocations start) (evaluation : Eval program env call start result finish) :
    ∃ address, result = .location address ∧ Resolve finish address address ∧
      readCell finish address = some [.tag tag, child] ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ location old, readCell start location = some old → readCell finish location = some old) := by
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
  obtain ⟨actualBinding, sameStore⟩ := variable_inversion childShape argumentEval
  have childEq : argumentValue = child := by simpa [childBinding] using actualBinding.symm
  subst argumentValue
  subst afterArgument
  have operandBinding : CoreEval.lookup (extend [] closure.parameter child) closure.parameter = some child := by
    simp [CoreEval.lookup, extend]
  obtain ⟨address, resultEq, addressFresh, _, cell, resultAliases, finalBound, resultRetained⟩ :=
    checked_unary_constructor_retains constructor closure.parameter operandShape operandFresh operandBinding
      closureBound bodyEval
  have noAlias : readAlias finish address = none := by
    simpa [readAlias, resultAliases, addressFresh] using bounded_fresh_no_alias afterFunction closureBound
  refine ⟨address, resultEq, Resolve.cell address [.tag tag, child] noAlias cell, cell,
    resultAliases.trans closureAliases, finalBound, ?_⟩
  intro location old read
  exact resultRetained location old (closureRetained location old read)

/-- The returned pair contains the actual successor Ledger and Registered identity. -/
theorem checked_success_pair (program : Program) (root ledgerNode statusNode : NodeId)
    (ledgerTag registeredTag : Constructor) (env : Environment) (start finish : Store)
    (result remaining outgoing child : Value) (counter : Int)
    (pair : CheckedTuple program root none [ledgerNode, statusNode])
    (ledgerLaw : ∀ before after value, BoundedLocations before →
      Eval program (extend env pair.contextBinder .context) ledgerNode before value after →
      NominalFields ledgerTag after value [.integer (counter + 1), remaining, outgoing] ∧
      after.aliases = before.aliases ∧ BoundedLocations after ∧
      (∀ address old, readCell before address = some old → readCell after address = some old))
    (statusLaw : ∀ before after value, BoundedLocations before →
      Eval program (extend env pair.contextBinder .context) statusNode before value after →
      (∃ address, value = .location address ∧ Resolve after address address ∧
        readCell after address = some [.tag registeredTag, child]) ∧
      after.aliases = before.aliases ∧ BoundedLocations after ∧
      (∀ address old, readCell before address = some old → readCell after address = some old))
    (bounded : BoundedLocations start) (evaluation : Eval program env root start result finish) :
    ∃ ledger status statusAddress, Result finish result ledger status ∧
      NominalFields ledgerTag finish ledger [.integer (counter + 1), remaining, outgoing] ∧
      status = .location statusAddress ∧ Resolve finish statusAddress statusAddress ∧
      readCell finish statusAddress = some [.tag registeredTag, child] ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  obtain ⟨queried, afterFields, afterAlloc, pairAddress, values, queryStep, fieldEvals,
    allocated, initialized, resultEq⟩ := checked_tuple_inversion pair evaluation
  obtain ⟨middle, ledger, status, ledgerEval, statusEval, sameValues⟩ := pair_fields_inversion fieldEvals
  have queryBound := query_preserves_bounded start queried .hostDefault .hostDefault bounded queryStep
  obtain ⟨ledgerRep, ledgerAliases, ledgerBound, ledgerRetained⟩ := ledgerLaw queried middle ledger queryBound ledgerEval
  obtain ⟨⟨statusAddress, statusEq, statusResolution, statusCell⟩, statusAliases, statusBound, statusRetained⟩ :=
    statusLaw middle afterFields status ledgerBound statusEval
  subst values
  have alloc : allocate .hostDefault ([ledger, status] : List Value).length true afterFields = some (pairAddress, afterAlloc) := by
    simpa using allocated
  have init : initializeStorage pairAddress ([ledger, status] : List Value).length [ledger, status] afterAlloc =
      some ([ledger, status], finish) := by simpa [storedFields] using initialized
  obtain ⟨fresh, _, pairCell, pairAliases, finalBound, pairRetained⟩ :=
    host_allocation_retains statusBound alloc init
  have pairNoAlias : readAlias finish pairAddress = none := by
    simpa [readAlias, pairAliases, fresh] using bounded_fresh_no_alias afterFields statusBound
  have resultRep : Result finish result ledger status := by
    rw [resultEq]
    exact Result.pair pairAddress pairAddress ledger status (Resolve.cell pairAddress _ pairNoAlias pairCell) pairCell
  have finalLedger := nominal_fields_retained ledgerTag middle finish ledger _
    (pairAliases.trans statusAliases)
    (fun address old read => pairRetained address old (statusRetained address old read)) ledgerRep
  have queryAliases : queried.aliases = start.aliases := by
    simp only [query, Option.some.injEq, Prod.mk.injEq] at queryStep
    rcases queryStep with ⟨_, rfl⟩
    rfl
  refine ⟨ledger, status, statusAddress, resultRep, finalLedger, statusEq,
    resolve_preserved pairAliases pairRetained statusResolution, pairRetained statusAddress _ statusCell,
    pairAliases.trans (statusAliases.trans (ledgerAliases.trans queryAliases)), finalBound, ?_⟩
  intro address old read
  exact pairRetained address old (statusRetained address old (ledgerRetained address old (query_preserves_cell queryStep read)))

/-- The checked Work payload is the newly issued nonnegative allocator identity. -/
theorem work_identity_from_fields (c : Constructors) (store : Store) (value : Value)
    (allocator : Nat) (serial : Int)
    (rep : ChildEntry c.work store value (.integer (Int.ofNat allocator)) (.integer serial)) :
    Ident c store value (.work allocator serial) := by
  obtain ⟨address, payload, same, resolution, cell, payloadResolution, fields⟩ := rep
  subst value
  exact Ident.work address address payload payload allocator serial resolution cell payloadResolution fields

/-- The exact Child payload is the standard whole-entry representation. -/
theorem child_from_fields (c : Constructors) (store : Store) (value child destination : Value)
    (rep : ChildEntry c.child store value child destination) : Entry c store value child destination := by
  obtain ⟨address, payload, same, resolution, cell, payloadResolution, fields⟩ := rep
  subst value
  exact Entry.child address address payload payload child destination resolution cell payloadResolution fields

/-- Exact checked nodes and binders of the successful returned pair. -/
structure CheckedSuccessFields (program : Program) (buffers : Ash.NetworkLedger.CoreIncrement.Buffers) where
  root : NodeId
  ledgerCall : NodeId
  ledgerFunction : NodeId
  ledgerArgument : NodeId
  ledgerOperand : NodeId
  remainingNode : NodeId
  outgoingNode : NodeId
  statusCall : NodeId
  statusFunction : NodeId
  childNode : NodeId
  statusOperand : NodeId
  ledgerTag : Constructor
  registeredTag : Constructor
  remainingName : Binder
  outgoingName : Binder
  childName : Binder
  increment : Ash.NetworkLedger.CoreIncrement.CheckedIncrement program buffers
  pair : CheckedTuple program root none [ledgerCall, statusCall]
  ledgerClosure : CheckedClosure program ledgerFunction
  ledgerConstructor : CheckedTuple program ledgerClosure.body (some ledgerTag) [ledgerOperand]
  ledgerArguments : CheckedTuple program ledgerArgument none [increment.root, remainingNode, outgoingNode]
  statusClosure : CheckedClosure program statusFunction
  statusConstructor : CheckedTuple program statusClosure.body (some registeredTag) [statusOperand]
  ledgerCallShape : program ledgerCall = some (.apply ledgerFunction ledgerArgument)
  ledgerOperandShape : program ledgerOperand = some (.variable ledgerClosure.parameter)
  ledgerOperandFresh : ledgerClosure.parameter ≠ ledgerConstructor.contextBinder
  remainingShape : program remainingNode = some (.variable remainingName)
  outgoingShape : program outgoingNode = some (.variable outgoingName)
  counterArgumentFresh : increment.counterBinder ≠ ledgerArguments.contextBinder
  remainingArgumentFresh : remainingName ≠ ledgerArguments.contextBinder
  outgoingArgumentFresh : outgoingName ≠ ledgerArguments.contextBinder
  counterPairFresh : increment.counterBinder ≠ pair.contextBinder
  remainingPairFresh : remainingName ≠ pair.contextBinder
  outgoingPairFresh : outgoingName ≠ pair.contextBinder
  childPairFresh : childName ≠ pair.contextBinder
  statusCallShape : program statusCall = some (.apply statusFunction childNode)
  childShape : program childNode = some (.variable childName)
  statusOperandShape : program statusOperand = some (.variable statusClosure.parameter)
  statusOperandFresh : statusClosure.parameter ≠ statusConstructor.contextBinder

/-- The checked returned pair evaluates Add, Ledger and Registered in actual field order. -/
theorem checked_success_fields (program : Program) (buffers : Ash.NetworkLedger.CoreIncrement.Buffers)
    (checked : CheckedSuccessFields program buffers) (env : Environment) (start finish : Store)
    (result remaining outgoing child : Value) (counter : Int)
    (counterBinding : CoreEval.lookup env checked.increment.counterBinder = some (.integer counter))
    (remainingBinding : CoreEval.lookup env checked.remainingName = some remaining)
    (outgoingBinding : CoreEval.lookup env checked.outgoingName = some outgoing)
    (childBinding : CoreEval.lookup env checked.childName = some child)
    (nonnegative : 0 ≤ counter) (bounded : BoundedLocations start)
    (evaluation : Eval program env checked.root start result finish) :
    ∃ ledger status statusAddress, Result finish result ledger status ∧
      NominalFields checked.ledgerTag finish ledger [.integer (counter + 1), remaining, outgoing] ∧
      status = .location statusAddress ∧ Resolve finish statusAddress statusAddress ∧
      readCell finish statusAddress = some [.tag checked.registeredTag, child] ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  apply checked_success_pair program checked.root checked.ledgerCall checked.statusCall
    checked.ledgerTag checked.registeredTag env start finish result remaining outgoing child counter checked.pair
  · intro before after value beforeBound ledgerEval
    have counterBound : CoreEval.lookup (extend env checked.pair.contextBinder .context) checked.increment.counterBinder =
        some (.integer counter) := by
      rw [lookup_extended_other env checked.pair.contextBinder checked.increment.counterBinder checked.counterPairFresh]
      exact counterBinding
    have remainingBound : CoreEval.lookup (extend env checked.pair.contextBinder .context) checked.remainingName = some remaining := by
      rw [lookup_extended_other env checked.pair.contextBinder checked.remainingName checked.remainingPairFresh]
      exact remainingBinding
    have outgoingBound : CoreEval.lookup (extend env checked.pair.contextBinder .context) checked.outgoingName = some outgoing := by
      rw [lookup_extended_other env checked.pair.contextBinder checked.outgoingName checked.outgoingPairFresh]
      exact outgoingBinding
    obtain ⟨_, representation, _, aliases, finalBound, retained⟩ :=
      checked_successor_ledger program buffers checked.increment checked.ledgerCall checked.ledgerFunction
        checked.ledgerArgument checked.remainingNode checked.outgoingNode checked.ledgerOperand checked.ledgerTag
        checked.ledgerClosure checked.ledgerConstructor checked.ledgerArguments _ before after value remaining outgoing counter
        checked.remainingName checked.outgoingName checked.ledgerCallShape checked.ledgerOperandShape checked.ledgerOperandFresh
        checked.remainingShape checked.outgoingShape checked.counterArgumentFresh checked.remainingArgumentFresh
        checked.outgoingArgumentFresh counterBound remainingBound outgoingBound nonnegative beforeBound ledgerEval
    exact ⟨representation, aliases, finalBound, retained⟩
  · intro before after value beforeBound statusEval
    have childBound : CoreEval.lookup (extend env checked.pair.contextBinder .context) checked.childName = some child := by
      rw [lookup_extended_other env checked.pair.contextBinder checked.childName checked.childPairFresh]
      exact childBinding
    obtain ⟨address, same, resolution, cell, aliases, finalBound, retained⟩ :=
      checked_registered_status program checked.statusCall checked.statusFunction checked.childNode checked.statusOperand
        checked.registeredTag checked.statusClosure checked.statusConstructor _ before after value child checked.childName
        checked.statusCallShape checked.childShape childBound checked.statusOperandShape checked.statusOperandFresh beforeBound statusEval
    exact ⟨⟨address, same, resolution, cell⟩, aliases, finalBound, retained⟩
  · exact bounded
  · exact evaluation

/-- WorkOut arguments evaluate the nested Parent between the ID and destination. -/
theorem checked_workout_arguments (program : Program)
    (root childNode parentCall destinationNode payloadNode parentFunction parentArguments ownerNode wantedNode parentOperand : NodeId)
    (parentTag : Constructor) (env : Environment) (start finish : Store)
    (result child owner wanted destination bytes : Value) (childName ownerName wantedName destinationName bytesName : Binder)
    (tuple : CheckedTuple program root none [childNode, parentCall, destinationNode, payloadNode])
    (parentClosure : CheckedClosure program parentFunction)
    (parentPair : CheckedTuple program parentArguments none [ownerNode, wantedNode])
    (parentConstructor : CheckedTuple program parentClosure.body (some parentTag) [parentOperand])
    (childShape : program childNode = some (.variable childName))
    (parentShape : program parentCall = some (.apply parentFunction parentArguments))
    (ownerShape : program ownerNode = some (.variable ownerName))
    (wantedShape : program wantedNode = some (.variable wantedName))
    (destinationShape : program destinationNode = some (.variable destinationName))
    (bytesShape : program payloadNode = some (.variable bytesName))
    (childFresh : childName ≠ tuple.contextBinder) (ownerFresh : ownerName ≠ tuple.contextBinder)
    (wantedFresh : wantedName ≠ tuple.contextBinder) (destinationFresh : destinationName ≠ tuple.contextBinder)
    (bytesFresh : bytesName ≠ tuple.contextBinder)
    (ownerParentFresh : ownerName ≠ parentPair.contextBinder) (wantedParentFresh : wantedName ≠ parentPair.contextBinder)
    (childBinding : CoreEval.lookup env childName = some child)
    (ownerBinding : CoreEval.lookup env ownerName = some owner)
    (wantedBinding : CoreEval.lookup env wantedName = some wanted)
    (destinationBinding : CoreEval.lookup env destinationName = some destination)
    (bytesBinding : CoreEval.lookup env bytesName = some bytes)
    (parentOperandShape : program parentOperand = some (.variable parentClosure.parameter))
    (parentOperandFresh : parentClosure.parameter ≠ parentConstructor.contextBinder)
    (bounded : BoundedLocations start) (evaluation : Eval program env root start result finish) :
    ∃ payload parent, result = .location payload ∧ Resolve finish payload payload ∧
      readCell finish payload = some [child, parent, destination, bytes] ∧
      ChildEntry parentTag finish parent owner wanted ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  obtain ⟨queried, afterFields, afterAlloc, payload, values, queryStep, fieldEvals,
    allocated, initialized, resultEq⟩ := checked_tuple_inversion tuple evaluation
  have queryBound := query_preserves_bounded start queried .hostDefault .hostDefault bounded queryStep
  have childBound : CoreEval.lookup (extend env tuple.contextBinder .context) childName = some child := by
    rw [lookup_extended_other env tuple.contextBinder childName childFresh]; exact childBinding
  have ownerBound : CoreEval.lookup (extend env tuple.contextBinder .context) ownerName = some owner := by
    rw [lookup_extended_other env tuple.contextBinder ownerName ownerFresh]; exact ownerBinding
  have wantedBound : CoreEval.lookup (extend env tuple.contextBinder .context) wantedName = some wanted := by
    rw [lookup_extended_other env tuple.contextBinder wantedName wantedFresh]; exact wantedBinding
  have destinationBound : CoreEval.lookup (extend env tuple.contextBinder .context) destinationName = some destination := by
    rw [lookup_extended_other env tuple.contextBinder destinationName destinationFresh]; exact destinationBinding
  have bytesBound : CoreEval.lookup (extend env tuple.contextBinder .context) bytesName = some bytes := by
    rw [lookup_extended_other env tuple.contextBinder bytesName bytesFresh]; exact bytesBinding
  cases fieldEvals with
  | cons childEval rest =>
    obtain ⟨actualChild, childState⟩ := variable_inversion childShape childEval
    have childEq : _ := Option.some.inj (actualChild.symm.trans childBound)
    rw [childState] at rest
    cases rest with
    | cons parentEval rest =>
      obtain ⟨⟨parentAddress, parentEq⟩, parentRep, _, parentAliases, parentBound, parentRetained⟩ :=
        checked_child_constructor program parentCall parentFunction parentArguments ownerNode wantedNode parentOperand parentTag
          parentClosure parentPair parentConstructor _ queried _ _ owner wanted ownerName wantedName parentShape ownerShape
          wantedShape ownerParentFresh wantedParentFresh ownerBound wantedBound parentOperandShape parentOperandFresh queryBound parentEval
      rw [parentEq] at parentRep
      cases rest with
      | cons destinationEval rest =>
        obtain ⟨actualDestination, destinationState⟩ := variable_inversion destinationShape destinationEval
        have destinationEq : _ := Option.some.inj (actualDestination.symm.trans destinationBound)
        subst destinationState
        cases rest with
        | cons bytesEval rest =>
          obtain ⟨actualBytes, bytesState⟩ := variable_inversion bytesShape bytesEval
          have bytesEq : _ := Option.some.inj (actualBytes.symm.trans bytesBound)
          subst bytesState
          cases rest
          have alloc : allocate .hostDefault ([child, .location parentAddress, destination, bytes] : List Value).length true afterFields =
              some (payload, afterAlloc) := by simpa [childEq, destinationEq, bytesEq] using allocated
          have init : initializeStorage payload ([child, .location parentAddress, destination, bytes] : List Value).length
              [child, .location parentAddress, destination, bytes] afterAlloc = some ([child, .location parentAddress, destination, bytes], finish) := by
            simpa [storedFields, childEq, parentEq, destinationEq, bytesEq] using initialized
          obtain ⟨fresh, _, cell, finalAliases, finalBound, finalRetained⟩ :=
            host_allocation_retains parentBound alloc init
          have noAlias : readAlias finish payload = none := by
            simpa [readAlias, finalAliases, fresh] using bounded_fresh_no_alias afterFields parentBound
          have finalParent := child_entry_retained parentTag _ finish _ owner wanted finalAliases finalRetained parentRep
          have queryAliases : queried.aliases = start.aliases := by
            simp only [query, Option.some.injEq, Prod.mk.injEq] at queryStep
            rcases queryStep with ⟨_, rfl⟩
            rfl
          refine ⟨payload, .location parentAddress, resultEq, Resolve.cell payload _ noAlias cell, cell, finalParent,
            finalAliases.trans (parentAliases.trans queryAliases), finalBound, ?_⟩
          intro address old read
          exact finalRetained address old (parentRetained address old (query_preserves_cell queryStep read))

/-- A dependent payload remains represented through its checked nominal wrapper. -/
theorem checked_nominal_with_payload (program : Program)
    (call function argument operand : NodeId) (tag : Constructor)
    (closure : CheckedClosure program function)
    (constructor : CheckedTuple program closure.body (some tag) [operand])
    (env : Environment) (start finish : Store) (result : Value) (R : Store → List Value → Prop)
    (relationRetained : ∀ before after fields, after.aliases = before.aliases →
      (∀ address old, readCell before address = some old → readCell after address = some old) →
      R before fields → R after fields)
    (callShape : program call = some (.apply function argument))
    (operandShape : program operand = some (.variable closure.parameter))
    (operandFresh : closure.parameter ≠ constructor.contextBinder)
    (payloadLaw : ∀ before after value, before.aliases = start.aliases →
      (∀ address old, readCell start address = some old → readCell before address = some old) →
      BoundedLocations before → Eval program env argument before value after →
      ∃ payload fields, value = .location payload ∧ Resolve after payload payload ∧
        readCell after payload = some fields ∧ R after fields ∧
        after.aliases = before.aliases ∧ BoundedLocations after ∧
        (∀ address old, readCell before address = some old → readCell after address = some old))
    (bounded : BoundedLocations start) (evaluation : Eval program env call start result finish) :
    (∃ address, result = .location address) ∧
      (∃ fields, NominalFields tag finish result fields ∧ R finish fields) ∧
      start.nextLocation ≤ finish.nextLocation ∧ finish.aliases = start.aliases ∧
      BoundedLocations finish ∧
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
  obtain ⟨payload, fields, payloadEq, payloadResolution, payloadCell, payloadRep, payloadAliases, payloadBound, payloadRetained⟩ :=
    payloadLaw afterFunction afterArgument argumentValue closureAliases closureRetained closureBound argumentEval
  subst argumentValue
  have operandBinding : CoreEval.lookup (extend [] closure.parameter (.location payload)) closure.parameter =
      some (.location payload) := by simp [CoreEval.lookup, extend]
  obtain ⟨address, resultEq, addressFresh, _, cell, resultAliases, finalBound, resultRetained⟩ :=
    checked_unary_constructor_retains constructor closure.parameter operandShape operandFresh operandBinding
      payloadBound bodyEval
  have aliases : finish.aliases = start.aliases := resultAliases.trans (payloadAliases.trans closureAliases)
  have retained : ∀ location old, readCell start location = some old → readCell finish location = some old := by
    intro location old read
    exact resultRetained location old (payloadRetained location old (closureRetained location old read))
  have noAlias : readAlias finish address = none := by
    simpa [readAlias, resultAliases, addressFresh] using bounded_fresh_no_alias afterArgument payloadBound
  have progress : start.nextLocation ≤ finish.nextLocation := by
    have live := finalBound.2.1 closureLocation _
      (readCell_member finish closureLocation _ (resultRetained closureLocation _ (payloadRetained closureLocation _ closureCell)))
    rw [closureFresh] at live
    omega
  exact ⟨⟨address, resultEq⟩, ⟨fields, ⟨address, address, payload, payload, resultEq,
    Resolve.cell address [.tag tag, .location payload] noAlias cell, cell,
    resolve_preserved resultAliases resultRetained payloadResolution, resultRetained payload _ payloadCell⟩,
    relationRetained afterArgument finish fields resultAliases resultRetained payloadRep⟩,
    progress, aliases, finalBound, retained⟩

/-- Exact WorkOut fields and its constructed Parent, retained as a whole value. -/
def WorkOutEntry (workOutTag parentTag : Constructor) (store : Store)
    (value child owner wanted destination bytes : Value) : Prop :=
  ∃ parent, NominalFields workOutTag store value [child, parent, destination, bytes] ∧
    ChildEntry parentTag store parent owner wanted

theorem workout_entry_retained (workOutTag parentTag : Constructor) (before after : Store)
    (value child owner wanted destination bytes : Value) (aliases : after.aliases = before.aliases)
    (cells : ∀ address old, readCell before address = some old → readCell after address = some old)
    (rep : WorkOutEntry workOutTag parentTag before value child owner wanted destination bytes) :
    WorkOutEntry workOutTag parentTag after value child owner wanted destination bytes := by
  obtain ⟨parent, output, parentRep⟩ := rep
  exact ⟨parent, nominal_fields_retained workOutTag before after value _ aliases cells output,
    child_entry_retained parentTag before after parent owner wanted aliases cells parentRep⟩

/-- The actual WorkOut call evaluates and retains its nested Parent. -/
theorem checked_workout_constructor (program : Program)
    (call function root childNode parentCall destinationNode payloadNode parentFunction parentArguments ownerNode wantedNode
      parentOperand operand : NodeId) (workOutTag parentTag : Constructor)
    (closure : CheckedClosure program function)
    (constructor : CheckedTuple program closure.body (some workOutTag) [operand])
    (tuple : CheckedTuple program root none [childNode, parentCall, destinationNode, payloadNode])
    (parentClosure : CheckedClosure program parentFunction)
    (parentPair : CheckedTuple program parentArguments none [ownerNode, wantedNode])
    (parentConstructor : CheckedTuple program parentClosure.body (some parentTag) [parentOperand])
    (env : Environment) (start finish : Store) (result child owner wanted destination bytes : Value)
    (childName ownerName wantedName destinationName bytesName : Binder)
    (callShape : program call = some (.apply function root))
    (operandShape : program operand = some (.variable closure.parameter))
    (operandFresh : closure.parameter ≠ constructor.contextBinder)
    (childShape : program childNode = some (.variable childName))
    (parentShape : program parentCall = some (.apply parentFunction parentArguments))
    (ownerShape : program ownerNode = some (.variable ownerName))
    (wantedShape : program wantedNode = some (.variable wantedName))
    (destinationShape : program destinationNode = some (.variable destinationName))
    (bytesShape : program payloadNode = some (.variable bytesName))
    (childFresh : childName ≠ tuple.contextBinder) (ownerFresh : ownerName ≠ tuple.contextBinder)
    (wantedFresh : wantedName ≠ tuple.contextBinder) (destinationFresh : destinationName ≠ tuple.contextBinder)
    (bytesFresh : bytesName ≠ tuple.contextBinder)
    (ownerParentFresh : ownerName ≠ parentPair.contextBinder) (wantedParentFresh : wantedName ≠ parentPair.contextBinder)
    (childBinding : CoreEval.lookup env childName = some child)
    (ownerBinding : CoreEval.lookup env ownerName = some owner)
    (wantedBinding : CoreEval.lookup env wantedName = some wanted)
    (destinationBinding : CoreEval.lookup env destinationName = some destination)
    (bytesBinding : CoreEval.lookup env bytesName = some bytes)
    (parentOperandShape : program parentOperand = some (.variable parentClosure.parameter))
    (parentOperandFresh : parentClosure.parameter ≠ parentConstructor.contextBinder)
    (bounded : BoundedLocations start) (evaluation : Eval program env call start result finish) :
    (∃ address, result = .location address) ∧
      WorkOutEntry workOutTag parentTag finish result child owner wanted destination bytes ∧
      start.nextLocation ≤ finish.nextLocation ∧ finish.aliases = start.aliases ∧
      BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  have relationRetained : ∀ before after fields, after.aliases = before.aliases →
      (∀ address old, readCell before address = some old → readCell after address = some old) →
      (∃ parent, fields = [child, parent, destination, bytes] ∧ ChildEntry parentTag before parent owner wanted) →
      (∃ parent, fields = [child, parent, destination, bytes] ∧ ChildEntry parentTag after parent owner wanted) := by
    intro before after fields aliases cells rep
    obtain ⟨parent, same, parentRep⟩ := rep
    exact ⟨parent, same, child_entry_retained parentTag before after parent owner wanted aliases cells parentRep⟩
  obtain ⟨located, ⟨fields, output, parent, same, parentRep⟩, progress, aliases, finalBound, retained⟩ :=
    checked_nominal_with_payload program call function root operand workOutTag closure constructor env start finish result
      (fun state fields => ∃ parent, fields = [child, parent, destination, bytes] ∧ ChildEntry parentTag state parent owner wanted)
      relationRetained callShape operandShape operandFresh (by
        intro before after value _ _ beforeBound argumentEval
        obtain ⟨payload, parent, same, resolution, cell, parentRep, aliases, afterBound, retained⟩ :=
          checked_workout_arguments program root childNode parentCall destinationNode payloadNode parentFunction parentArguments
            ownerNode wantedNode parentOperand parentTag env before after value child owner wanted destination bytes childName ownerName
            wantedName destinationName bytesName tuple parentClosure parentPair parentConstructor childShape parentShape ownerShape
            wantedShape destinationShape bytesShape childFresh ownerFresh wantedFresh destinationFresh bytesFresh ownerParentFresh
            wantedParentFresh childBinding ownerBinding wantedBinding destinationBinding bytesBinding parentOperandShape
            parentOperandFresh beforeBound argumentEval
        exact ⟨payload, [child, parent, destination, bytes], same, resolution, cell, ⟨parent, rfl, parentRep⟩,
          aliases, afterBound, retained⟩) bounded evaluation
  subst fields
  exact ⟨located, ⟨parent, output, parentRep⟩, progress, aliases, finalBound, retained⟩

/-- The real WorkOut expression is evaluated before the stored output append. -/
theorem checked_append_workout_call (c : Constructors) (program : Program)
    (checked : Ash.NetworkLedger.CoreInsert.CheckedInsert c program)
    (call function argument outputCall listNode outputFunction outputArgument childNode parentCall destinationNode payloadNode
      parentFunction parentArguments ownerNode wantedNode parentOperand outputOperand : NodeId)
    (workOutTag parentTag : Constructor) (env : Environment) (start finish : Store)
    (result list child owner wanted destination bytes : Value) (entries : List Value)
    (callName listName childName ownerName wantedName destinationName bytesName : Binder)
    (selfAddress selfResolved : Nat) (captureValues : List Value) (captureEnv : Environment)
    (outerPair : CheckedTuple program argument none [outputCall, listNode])
    (outputClosure : CheckedClosure program outputFunction)
    (outputConstructor : CheckedTuple program outputClosure.body (some workOutTag) [outputOperand])
    (outputTuple : CheckedTuple program outputArgument none [childNode, parentCall, destinationNode, payloadNode])
    (parentClosure : CheckedClosure program parentFunction)
    (parentPair : CheckedTuple program parentArguments none [ownerNode, wantedNode])
    (parentConstructor : CheckedTuple program parentClosure.body (some parentTag) [parentOperand])
    (callShape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable callName))
    (functionBinding : CoreEval.lookup env callName = some (.location selfAddress))
    (listShape : program listNode = some (.variable listName)) (listFresh : listName ≠ outerPair.contextBinder)
    (listBinding : CoreEval.lookup env listName = some list)
    (outputShape : program outputCall = some (.apply outputFunction outputArgument))
    (outputOperandShape : program outputOperand = some (.variable outputClosure.parameter))
    (outputOperandFresh : outputClosure.parameter ≠ outputConstructor.contextBinder)
    (childShape : program childNode = some (.variable childName))
    (parentShape : program parentCall = some (.apply parentFunction parentArguments))
    (ownerShape : program ownerNode = some (.variable ownerName))
    (wantedShape : program wantedNode = some (.variable wantedName))
    (destinationShape : program destinationNode = some (.variable destinationName))
    (bytesShape : program payloadNode = some (.variable bytesName))
    (childOuterFresh : childName ≠ outerPair.contextBinder) (ownerOuterFresh : ownerName ≠ outerPair.contextBinder)
    (wantedOuterFresh : wantedName ≠ outerPair.contextBinder) (destinationOuterFresh : destinationName ≠ outerPair.contextBinder)
    (bytesOuterFresh : bytesName ≠ outerPair.contextBinder)
    (childFresh : childName ≠ outputTuple.contextBinder) (ownerFresh : ownerName ≠ outputTuple.contextBinder)
    (wantedFresh : wantedName ≠ outputTuple.contextBinder) (destinationFresh : destinationName ≠ outputTuple.contextBinder)
    (bytesFresh : bytesName ≠ outputTuple.contextBinder)
    (ownerParentFresh : ownerName ≠ parentPair.contextBinder) (wantedParentFresh : wantedName ≠ parentPair.contextBinder)
    (childBinding : CoreEval.lookup env childName = some child) (ownerBinding : CoreEval.lookup env ownerName = some owner)
    (wantedBinding : CoreEval.lookup env wantedName = some wanted) (destinationBinding : CoreEval.lookup env destinationName = some destination)
    (bytesBinding : CoreEval.lookup env bytesName = some bytes)
    (parentOperandShape : program parentOperand = some (.variable parentClosure.parameter))
    (parentOperandFresh : parentClosure.parameter ≠ parentConstructor.contextBinder)
    (selfBinding : CoreEval.lookup captureEnv.reverse checked.functionName = some (.location selfAddress))
    (captureBindings : CaptureBindings program checked.captureNodes captureValues captureEnv)
    (selfResolution : Resolve start selfAddress selfResolved)
    (selfCell : readCell start selfResolved = some (.closureCode checked.code :: captureValues))
    (bounded : BoundedLocations start) (listRep : Children c start list entries)
    (located : Ash.NetworkLedger.CoreGenericInsert.LocatedEntries entries)
    (evaluation : Eval program env call start result finish) :
    ∃ newEntry, WorkOutEntry workOutTag parentTag finish newEntry child owner wanted destination bytes ∧
      Ash.NetworkLedger.CoreInsert.InsertOutcome c start finish result (entries ++ [newEntry]) := by
  apply checked_spine_append_expression c program checked
    (fun state entry => WorkOutEntry workOutTag parentTag state entry child owner wanted destination bytes)
    (fun before after entry aliases cells rep => workout_entry_retained workOutTag parentTag before after entry
      child owner wanted destination bytes aliases cells rep)
    call function argument outputCall listNode env start finish result list entries callName listName selfAddress selfResolved
    captureValues captureEnv outerPair callShape functionShape functionBinding listShape listFresh listBinding
  · intro before after value beforeBound outputEval
    have childBound : CoreEval.lookup (extend env outerPair.contextBinder .context) childName = some child := by
      rw [lookup_extended_other env outerPair.contextBinder childName childOuterFresh]; exact childBinding
    have ownerBound : CoreEval.lookup (extend env outerPair.contextBinder .context) ownerName = some owner := by
      rw [lookup_extended_other env outerPair.contextBinder ownerName ownerOuterFresh]; exact ownerBinding
    have wantedBound : CoreEval.lookup (extend env outerPair.contextBinder .context) wantedName = some wanted := by
      rw [lookup_extended_other env outerPair.contextBinder wantedName wantedOuterFresh]; exact wantedBinding
    have destinationBound : CoreEval.lookup (extend env outerPair.contextBinder .context) destinationName = some destination := by
      rw [lookup_extended_other env outerPair.contextBinder destinationName destinationOuterFresh]; exact destinationBinding
    have bytesBound : CoreEval.lookup (extend env outerPair.contextBinder .context) bytesName = some bytes := by
      rw [lookup_extended_other env outerPair.contextBinder bytesName bytesOuterFresh]; exact bytesBinding
    exact checked_workout_constructor program outputCall outputFunction outputArgument childNode parentCall destinationNode payloadNode
      parentFunction parentArguments ownerNode wantedNode parentOperand outputOperand workOutTag parentTag outputClosure outputConstructor
      outputTuple parentClosure parentPair parentConstructor _ before after value child owner wanted destination bytes childName ownerName
      wantedName destinationName bytesName outputShape outputOperandShape outputOperandFresh childShape parentShape ownerShape wantedShape
      destinationShape bytesShape childFresh ownerFresh wantedFresh destinationFresh bytesFresh ownerParentFresh wantedParentFresh
      childBound ownerBound wantedBound destinationBound bytesBound parentOperandShape parentOperandFresh beforeBound outputEval
  · exact selfBinding
  · exact captureBindings
  · exact selfResolution
  · exact selfCell
  · exact bounded
  · exact listRep
  · exact located
  · exact evaluation

/-- A replacement Record preserves the selected fields and appends the whole new Child. -/
def ReplacementPayload (c : Constructors) (openTag : Constructor) (store : Store)
    (fields : List Value) (wanted parent child destination : Value) (entries : List Value) : Prop :=
  ∃ phase appended newEntry, fields = [wanted, parent, .location phase, appended] ∧
    Resolve store phase phase ∧ readCell store phase = some [.tag openTag] ∧
    Children c store appended (entries ++ [newEntry]) ∧ ChildEntry c.child store newEntry child destination

theorem replacement_payload_retained (c : Constructors) (openTag : Constructor) (before after : Store)
    (fields : List Value) (wanted parent child destination : Value) (entries : List Value)
    (aliases : after.aliases = before.aliases)
    (cells : ∀ address old, readCell before address = some old → readCell after address = some old)
    (rep : ReplacementPayload c openTag before fields wanted parent child destination entries) :
    ReplacementPayload c openTag after fields wanted parent child destination entries := by
  obtain ⟨phase, appended, newEntry, same, phaseResolution, phaseCell, listRep, childRep⟩ := rep
  exact ⟨phase, appended, newEntry, same, resolve_preserved aliases cells phaseResolution,
    cells phase _ phaseCell, children_retained c before after appended _ aliases cells listRep,
    child_entry_retained c.child before after newEntry child destination aliases cells childRep⟩

/-- Record fields execute wanted, parent, Open, then the actual child append. -/
theorem checked_replacement_arguments (c : Constructors) (program : Program)
    (root wantedNode parentNode openNode appendNode : NodeId) (openTag : Constructor) (env : Environment)
    (start finish : Store) (result wanted parent child destination : Value) (entries : List Value)
    (wantedName parentName : Binder)
    (tuple : CheckedTuple program root none [wantedNode, parentNode, openNode, appendNode])
    (openTuple : CheckedTuple program openNode (some openTag) [])
    (wantedShape : program wantedNode = some (.variable wantedName))
    (parentShape : program parentNode = some (.variable parentName))
    (wantedFresh : wantedName ≠ tuple.contextBinder) (parentFresh : parentName ≠ tuple.contextBinder)
    (wantedBinding : CoreEval.lookup env wantedName = some wanted)
    (parentBinding : CoreEval.lookup env parentName = some parent)
    (appendLaw : ∀ before after value, before.aliases = start.aliases →
      (∀ address old, readCell start address = some old → readCell before address = some old) →
      BoundedLocations before → Eval program (extend env tuple.contextBinder .context) appendNode before value after →
      ∃ newEntry, ChildEntry c.child after newEntry child destination ∧
        Ash.NetworkLedger.CoreInsert.InsertOutcome c before after value (entries ++ [newEntry]))
    (bounded : BoundedLocations start) (evaluation : Eval program env root start result finish) :
    ∃ payload fields, result = .location payload ∧ Resolve finish payload payload ∧
      readCell finish payload = some fields ∧ ReplacementPayload c openTag finish fields wanted parent child destination entries ∧
      finish.aliases = start.aliases ∧ BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  obtain ⟨queried, afterFields, afterAlloc, payload, values, queryStep, fieldEvals,
    allocated, initialized, resultEq⟩ := checked_tuple_inversion tuple evaluation
  have queryBound := query_preserves_bounded start queried .hostDefault .hostDefault bounded queryStep
  have wantedBound : CoreEval.lookup (extend env tuple.contextBinder .context) wantedName = some wanted := by
    rw [lookup_extended_other env tuple.contextBinder wantedName wantedFresh]; exact wantedBinding
  have parentBound : CoreEval.lookup (extend env tuple.contextBinder .context) parentName = some parent := by
    rw [lookup_extended_other env tuple.contextBinder parentName parentFresh]; exact parentBinding
  have queryAliases : queried.aliases = start.aliases := by
    simp only [query, Option.some.injEq, Prod.mk.injEq] at queryStep
    rcases queryStep with ⟨_, rfl⟩
    rfl
  cases fieldEvals with
  | cons wantedEval rest =>
    obtain ⟨actualWanted, wantedState⟩ := variable_inversion wantedShape wantedEval
    have wantedEq : _ := Option.some.inj (actualWanted.symm.trans wantedBound)
    rw [wantedState] at rest
    cases rest with
    | cons parentEval rest =>
      obtain ⟨actualParent, parentState⟩ := variable_inversion parentShape parentEval
      have parentEq : _ := Option.some.inj (actualParent.symm.trans parentBound)
      rw [parentState] at rest
      cases rest with
      | cons openEval rest =>
        obtain ⟨phase, phaseEq, phaseFresh, _, phaseCell, phaseAliases, phaseBound, phaseRetained⟩ :=
          checked_nullary_retains openTuple queryBound openEval
        cases rest with
        | cons appendEval rest =>
          obtain ⟨newEntry, childRep, listRep, _, appendAliases, appendBound, appendRetained⟩ :=
            appendLaw _ _ _ (phaseAliases.trans queryAliases)
              (fun address old read => phaseRetained address old (query_preserves_cell queryStep read)) phaseBound appendEval
          cases rest
          obtain ⟨appendedAddress, appendedEq⟩ := children_is_location c afterFields _ _ listRep
          rw [appendedEq] at listRep
          have alloc : allocate .hostDefault ([wanted, parent, .location phase, .location appendedAddress] : List Value).length true afterFields =
              some (payload, afterAlloc) := by simpa [wantedEq, parentEq, phaseEq] using allocated
          have init : initializeStorage payload ([wanted, parent, .location phase, .location appendedAddress] : List Value).length
              [wanted, parent, .location phase, .location appendedAddress] afterAlloc = some ([wanted, parent, .location phase, .location appendedAddress], finish) := by
            simpa [storedFields, wantedEq, parentEq, phaseEq, appendedEq] using initialized
          obtain ⟨fresh, _, cell, finalAliases, finalBound, finalRetained⟩ :=
            host_allocation_retains appendBound alloc init
          have noAlias : readAlias finish payload = none := by
            simpa [readAlias, finalAliases, fresh] using bounded_fresh_no_alias afterFields appendBound
          have phaseNoAlias : readAlias finish phase = none := by
            simpa [readAlias, finalAliases, appendAliases, phaseAliases, phaseFresh] using bounded_fresh_no_alias queried queryBound
          have finalPhase := finalRetained phase _ (appendRetained phase _ phaseCell)
          refine ⟨payload, _, resultEq, Resolve.cell payload _ noAlias cell, cell,
            ⟨phase, .location appendedAddress, newEntry, rfl, Resolve.cell phase [.tag openTag] phaseNoAlias finalPhase, finalPhase,
              children_retained c afterFields finish _ _ finalAliases finalRetained listRep,
              child_entry_retained c.child afterFields finish newEntry child destination finalAliases finalRetained childRep⟩,
            finalAliases.trans (appendAliases.trans (phaseAliases.trans queryAliases)), finalBound, ?_⟩
          intro address old read
          exact finalRetained address old (appendRetained address old (phaseRetained address old (query_preserves_cell queryStep read)))

/-- Whole replacement Record with its exact selected key, parent and appended children. -/
def ReplacementEntry (c : Constructors) (recordTag openTag : Constructor) (store : Store)
    (value wanted parent child destination : Value) (entries : List Value) : Prop :=
  ∃ fields, NominalFields recordTag store value fields ∧
    ReplacementPayload c openTag store fields wanted parent child destination entries

theorem replacement_entry_retained (c : Constructors) (recordTag openTag : Constructor)
    (before after : Store) (value wanted parent child destination : Value) (entries : List Value)
    (aliases : after.aliases = before.aliases)
    (cells : ∀ address old, readCell before address = some old → readCell after address = some old)
    (rep : ReplacementEntry c recordTag openTag before value wanted parent child destination entries) :
    ReplacementEntry c recordTag openTag after value wanted parent child destination entries := by
  obtain ⟨fields, nominal, payload⟩ := rep
  exact ⟨fields, nominal_fields_retained recordTag before after value fields aliases cells nominal,
    replacement_payload_retained c openTag before after fields wanted parent child destination entries aliases cells payload⟩

/-- The actual Record constructor wraps the checked Open and child-append fields. -/
theorem checked_replacement_record (c : Constructors) (program : Program)
    (call function argument wantedNode parentNode openNode appendNode operand : NodeId)
    (recordTag openTag : Constructor) (closure : CheckedClosure program function)
    (constructor : CheckedTuple program closure.body (some recordTag) [operand])
    (tuple : CheckedTuple program argument none [wantedNode, parentNode, openNode, appendNode])
    (openTuple : CheckedTuple program openNode (some openTag) [])
    (env : Environment) (start finish : Store) (result wanted parent child destination : Value) (entries : List Value)
    (wantedName parentName : Binder)
    (callShape : program call = some (.apply function argument))
    (operandShape : program operand = some (.variable closure.parameter))
    (operandFresh : closure.parameter ≠ constructor.contextBinder)
    (wantedShape : program wantedNode = some (.variable wantedName))
    (parentShape : program parentNode = some (.variable parentName))
    (wantedFresh : wantedName ≠ tuple.contextBinder) (parentFresh : parentName ≠ tuple.contextBinder)
    (wantedBinding : CoreEval.lookup env wantedName = some wanted)
    (parentBinding : CoreEval.lookup env parentName = some parent)
    (appendLaw : ∀ before after value, before.aliases = start.aliases →
      (∀ address old, readCell start address = some old → readCell before address = some old) →
      BoundedLocations before → Eval program (extend env tuple.contextBinder .context) appendNode before value after →
      ∃ newEntry, ChildEntry c.child after newEntry child destination ∧
        Ash.NetworkLedger.CoreInsert.InsertOutcome c before after value (entries ++ [newEntry]))
    (bounded : BoundedLocations start) (evaluation : Eval program env call start result finish) :
    (∃ address, result = .location address) ∧
      ReplacementEntry c recordTag openTag finish result wanted parent child destination entries ∧
      start.nextLocation ≤ finish.nextLocation ∧ finish.aliases = start.aliases ∧
      BoundedLocations finish ∧
      (∀ address old, readCell start address = some old → readCell finish address = some old) := by
  obtain ⟨located, ⟨fields, nominal, payload⟩, progress, aliases, finalBound, retained⟩ :=
    checked_nominal_with_payload program call function argument operand recordTag closure constructor env start finish result
      (fun state fields => ReplacementPayload c openTag state fields wanted parent child destination entries)
      (fun before after fields same cells rep => replacement_payload_retained c openTag before after fields
        wanted parent child destination entries same cells rep)
      callShape operandShape operandFresh (by
        intro before after value beforeAliases beforeRetained beforeBound argumentEval
        exact checked_replacement_arguments c program argument wantedNode parentNode openNode appendNode openTag env before after
          value wanted parent child destination entries wantedName parentName tuple openTuple wantedShape parentShape wantedFresh
          parentFresh wantedBinding parentBinding (by
            intro middle final appended middleAliases middleRetained middleBound appendEval
            exact appendLaw middle final appended (middleAliases.trans beforeAliases)
              (fun address old read => middleRetained address old (beforeRetained address old read)) middleBound appendEval)
          beforeBound argumentEval) bounded evaluation
  exact ⟨located, ⟨fields, nominal, payload⟩, progress, aliases, finalBound, retained⟩

/-- Decoding preserves the lookup of an ordered finite list when the exact keys agree. -/
theorem decode_lookup {A B : Type} (keyA : A → Id) (keyB : B → Id) (decode : A → B)
    (wanted : Id) (entries : List A) (keys : ∀ entry ∈ entries, keyA entry = keyB (decode entry)) :
    (Ash.NetworkLedger.lookup keyA wanted entries).map decode =
      Ash.NetworkLedger.lookup keyB wanted (entries.map decode) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    have headKey := keys entry (by simp)
    have tailKeys : ∀ item ∈ entries, keyA item = keyB (decode item) := by
      intro item member
      exact keys item (by simp [member])
    simp only [Ash.NetworkLedger.lookup, List.map_cons]
    rw [headKey]
    split <;> simp_all

/-- Decoding preserves first-match update and its original whole-entry order. -/
theorem decode_update {A B : Type} (keyA : A → Id) (keyB : B → Id) (decode : A → B)
    (wanted : Id) (replacement : A) (entries : List A)
    (keys : ∀ entry ∈ entries, keyA entry = keyB (decode entry)) :
    (Ash.NetworkLedger.update keyA wanted replacement entries).map decode =
      Ash.NetworkLedger.update keyB wanted (decode replacement) (entries.map decode) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    have headKey := keys entry (by simp)
    have tailKeys : ∀ item ∈ entries, keyA item = keyB (decode item) := by
      intro item member
      exact keys item (by simp [member])
    simp only [Ash.NetworkLedger.update, List.map_cons]
    rw [headKey]
    split <;> simp_all

/-- The normal allocation frame keeps the checked caller's old cells and aliases. -/
def CommitFrame (start current : Store) : Prop :=
  current.aliases = start.aliases ∧ BoundedLocations current ∧
    (∀ address old, readCell start address = some old → readCell current address = some old)

theorem commit_frame_trans (start middle finish : Store)
    (first : CommitFrame start middle) (second : CommitFrame middle finish) : CommitFrame start finish := by
  exact ⟨second.1.trans first.1, second.2.1,
    fun address old read => second.2.2 address old (first.2.2 address old read)⟩

/-- Distinct checked binders expose the actual values to the returned fields. -/
theorem commit_result_bindings (env : Environment)
    (counterName workName replacementName remainingName outgoingName : Binder)
    (work replacement remaining outgoing : Value) (counter : Int)
    (counterBinding : CoreEval.lookup env counterName = some (.integer counter))
    (counterWork : counterName ≠ workName) (counterReplacement : counterName ≠ replacementName)
    (counterRemaining : counterName ≠ remainingName) (counterOutgoing : counterName ≠ outgoingName)
    (workReplacement : workName ≠ replacementName) (workRemaining : workName ≠ remainingName)
    (workOutgoing : workName ≠ outgoingName) (remainingOutgoing : remainingName ≠ outgoingName) :
    let resultEnv := extend (extend (extend (extend env workName work) replacementName replacement)
      remainingName remaining) outgoingName outgoing
    CoreEval.lookup resultEnv counterName = some (.integer counter) ∧
    CoreEval.lookup resultEnv remainingName = some remaining ∧
    CoreEval.lookup resultEnv outgoingName = some outgoing ∧
    CoreEval.lookup resultEnv workName = some work := by
  dsimp
  constructor
  · simpa [CoreEval.lookup, extend, Ne.symm counterWork, Ne.symm counterReplacement,
      Ne.symm counterRemaining, Ne.symm counterOutgoing] using counterBinding
  constructor
  · simp [CoreEval.lookup, extend, Ne.symm remainingOutgoing]
  constructor
  · simp [CoreEval.lookup, extend]
  · simp [CoreEval.lookup, extend, Ne.symm workReplacement, Ne.symm workRemaining, Ne.symm workOutgoing]

/-- The checked Work initializer returns the represented fresh-serial candidate. -/
theorem checked_work_initializer (c : Constructors) (program : Program)
    (call function argument ownerNode counterNode operand : NodeId)
    (closure : CheckedClosure program function)
    (pair : CheckedTuple program argument none [ownerNode, counterNode])
    (constructor : CheckedTuple program closure.body (some c.work) [operand])
    (env : Environment) (start finish : Store) (result : Value)
    (owner : Nat) (counter : Int) (ownerName counterName : Binder)
    (callShape : program call = some (.apply function argument))
    (ownerShape : program ownerNode = some (.variable ownerName))
    (counterShape : program counterNode = some (.variable counterName))
    (ownerFresh : ownerName ≠ pair.contextBinder) (counterFresh : counterName ≠ pair.contextBinder)
    (ownerBinding : CoreEval.lookup env ownerName = some (.integer (Int.ofNat owner)))
    (counterBinding : CoreEval.lookup env counterName = some (.integer counter))
    (operandShape : program operand = some (.variable closure.parameter))
    (operandFresh : closure.parameter ≠ constructor.contextBinder)
    (bounded : BoundedLocations start) (evaluation : Eval program env call start result finish) :
    Ident c finish result (.work owner counter) ∧ CommitFrame start finish := by
  obtain ⟨_, representation, _, aliases, finalBound, retained⟩ :=
    checked_child_constructor program call function argument ownerNode counterNode operand c.work closure pair constructor
      env start finish result (.integer (Int.ofNat owner)) (.integer counter) ownerName counterName callShape ownerShape
      counterShape ownerFresh counterFresh ownerBinding counterBinding operandShape operandFresh bounded evaluation
  exact ⟨work_identity_from_fields c finish result owner counter representation, aliases, finalBound, retained⟩

/-- Reopen the checked update helper in a retained caller frame and execute its actual call. -/
theorem checked_commit_update (c : Constructors) (program : Program)
    (checked : Ash.NetworkLedger.CoreRecordUpdate.CheckedRecordUpdate c program)
    (projection : RecordProjectionShape program checked.projection)
    (projectionFunctionName : projection.functionName = checked.projectionName)
    (projectionEntryName : projection.recordName = checked.entryName)
    (projectionCode : projection.code = checked.projectionCode)
    (call function argument wantedNode replacementNode listNode : NodeId) (env : Environment)
    (initial before after : Store) (result wanted replacement list : Value) (queryId : Id) (key : Value → Id) (entries : List Value)
    (callName wantedName replacementName listName : Binder) (selfAddress selfResolved comparisonAddress comparisonResolved
      projectionAddress projectionResolved : Nat) (captureValues : List Value) (captureEnv : Environment)
    (triple : CheckedTuple program argument none [wantedNode, replacementNode, listNode])
    (callShape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable callName))
    (functionBinding : CoreEval.lookup env callName = some (.location selfAddress))
    (wantedShape : program wantedNode = some (.variable wantedName))
    (replacementShape : program replacementNode = some (.variable replacementName))
    (listShape : program listNode = some (.variable listName))
    (wantedFresh : wantedName ≠ triple.contextBinder) (replacementFresh : replacementName ≠ triple.contextBinder)
    (listFresh : listName ≠ triple.contextBinder)
    (wantedBinding : CoreEval.lookup env wantedName = some wanted)
    (replacementBinding : CoreEval.lookup env replacementName = some replacement)
    (listBinding : CoreEval.lookup env listName = some list)
    (selfBinding : CoreEval.lookup captureEnv.reverse checked.functionName = some (.location selfAddress))
    (comparisonBinding : CoreEval.lookup captureEnv.reverse checked.comparisonName = some (.location comparisonAddress))
    (projectionBinding : CoreEval.lookup captureEnv.reverse checked.projectionName = some (.location projectionAddress))
    (captureBindings : CaptureBindings program checked.captureNodes captureValues captureEnv)
    (selfResolution : Resolve initial selfAddress selfResolved)
    (selfCell : readCell initial selfResolved = some (.closureCode checked.code :: captureValues))
    (comparisonResolution : Resolve initial comparisonAddress comparisonResolved)
    (comparisonCell : readCell initial comparisonResolved = some [.closureCode checked.comparator.code])
    (projectionResolution : Resolve initial projectionAddress projectionResolved)
    (projectionCell : readCell initial projectionResolved = some [.closureCode checked.projectionCode])
    (wantedRep : Ident c initial wanted queryId) (listRep : Children c initial list entries)
    (keys : RepresentedEntries c (RecordEntry projection.record) initial key entries)
    (frame : CommitFrame initial before) (evaluation : Eval program env call before result after) :
    Children c after result (Ash.NetworkLedger.update key queryId replacement entries) ∧ CommitFrame before after := by
  obtain ⟨returned, _, aliases, finalBound, retained⟩ :=
    checked_record_update_call c program checked projection projectionFunctionName projectionEntryName projectionCode
      call function argument wantedNode replacementNode listNode env before after result wanted replacement list queryId key entries
      callName wantedName replacementName listName selfAddress selfResolved comparisonAddress comparisonResolved projectionAddress projectionResolved
      captureValues captureEnv triple callShape functionShape functionBinding wantedShape replacementShape listShape wantedFresh replacementFresh
      listFresh wantedBinding replacementBinding listBinding selfBinding comparisonBinding projectionBinding captureBindings
      (resolve_preserved frame.1 frame.2.2 selfResolution) (frame.2.2 selfResolved _ selfCell)
      (resolve_preserved frame.1 frame.2.2 comparisonResolution) (frame.2.2 comparisonResolved _ comparisonCell)
      (resolve_preserved frame.1 frame.2.2 projectionResolution) (frame.2.2 projectionResolved _ projectionCell)
      frame.2.1 (ident_retained c initial before wanted queryId frame.1 frame.2.2 wantedRep)
      (children_retained c initial before list entries frame.1 frame.2.2 listRep)
      (represented_entries_retained c (RecordEntry projection.record) initial before key entries
        (record_entry_retained projection.record) frame.1 frame.2.2 keys) evaluation
  exact ⟨returned, aliases, finalBound, retained⟩

/-- The checked four-bind commit composes the actual helper outputs and returned pair. -/
theorem registration_commit_composed (ids recordsList outputsList : Constructors)
    (program : Program) (buffers : Ash.NetworkLedger.CoreIncrement.Buffers)
    (checkedResult : CheckedSuccessFields program buffers)
    (first second third fourth workNode replacementNode updateNode outputNode : NodeId)
    (workName replacementName remainingName outgoingName : Binder)
    (recordTag openTag workOutTag parentTag : Constructor)
    (env : Environment) (start finish : Store) (result wanted parent destination bytes : Value)
    (owner : Nat) (counter : Int) (wantedId : Id) (key : Value → Id)
    (children records outputs : List Value)
    (firstShape : program first = some (.bind workName workNode second))
    (secondShape : program second = some (.bind replacementName replacementNode third))
    (thirdShape : program third = some (.bind remainingName updateNode fourth))
    (fourthShape : program fourth = some (.bind outgoingName outputNode checkedResult.root))
    (nonnegative : 0 ≤ counter) (bounded : BoundedLocations start)
    (workFunction workArgument workOwnerNode workCounterNode workOperand : NodeId)
    (workOwnerName : Binder)
    (workClosure : CheckedClosure program workFunction)
    (workPair : CheckedTuple program workArgument none [workOwnerNode, workCounterNode])
    (workConstructor : CheckedTuple program workClosure.body (some ids.work) [workOperand])
    (workCallShape : program workNode = some (.apply workFunction workArgument))
    (workOwnerShape : program workOwnerNode = some (.variable workOwnerName))
    (workCounterShape : program workCounterNode = some (.variable checkedResult.increment.counterBinder))
    (workOwnerFresh : workOwnerName ≠ workPair.contextBinder)
    (workCounterFresh : checkedResult.increment.counterBinder ≠ workPair.contextBinder)
    (workOwnerBinding : CoreEval.lookup env workOwnerName = some (.integer (Int.ofNat owner)))
    (workOperandShape : program workOperand = some (.variable workClosure.parameter))
    (workOperandFresh : workClosure.parameter ≠ workConstructor.contextBinder)
    (childChecked : Ash.NetworkLedger.CoreInsert.CheckedInsert ids program)
    (replacementFunction replacementArgument replacementWantedNode replacementParentNode replacementOpenNode
      childAppendNode replacementOperand childFunction childArgument childCall childListNode childConstructorFunction childConstructorArgument
      childIdNode childDestinationNode childOperand : NodeId)
    (replacementWantedName replacementParentName childCallName childListName childIdName childDestinationName : Binder)
    (childSelfAddress childSelfResolved : Nat) (childCaptureValues : List Value) (childCaptureEnv : Environment)
    (replacementClosure : CheckedClosure program replacementFunction)
    (replacementConstructor : CheckedTuple program replacementClosure.body (some recordTag) [replacementOperand])
    (replacementTuple : CheckedTuple program replacementArgument none
      [replacementWantedNode, replacementParentNode, replacementOpenNode, childAppendNode])
    (replacementOpenTuple : CheckedTuple program replacementOpenNode (some openTag) [])
    (childOuterPair : CheckedTuple program childArgument none [childCall, childListNode])
    (childClosure : CheckedClosure program childConstructorFunction)
    (childPair : CheckedTuple program childConstructorArgument none [childIdNode, childDestinationNode])
    (childConstructor : CheckedTuple program childClosure.body (some ids.child) [childOperand])
    (replacementCallShape : program replacementNode = some (.apply replacementFunction replacementArgument))
    (replacementOperandShape : program replacementOperand = some (.variable replacementClosure.parameter))
    (replacementOperandFresh : replacementClosure.parameter ≠ replacementConstructor.contextBinder)
    (replacementWantedShape : program replacementWantedNode = some (.variable replacementWantedName))
    (replacementParentShape : program replacementParentNode = some (.variable replacementParentName))
    (replacementWantedFresh : replacementWantedName ≠ replacementTuple.contextBinder)
    (replacementParentFresh : replacementParentName ≠ replacementTuple.contextBinder)
    (childAppendShape : program childAppendNode = some (.apply childFunction childArgument))
    (childFunctionShape : program childFunction = some (.variable childCallName))
    (childListShape : program childListNode = some (.variable childListName))
    (childListFresh : childListName ≠ childOuterPair.contextBinder)
    (childCallShape : program childCall = some (.apply childConstructorFunction childConstructorArgument))
    (childIdShape : program childIdNode = some (.variable childIdName))
    (childDestinationShape : program childDestinationNode = some (.variable childDestinationName))
    (childIdOuterFresh : childIdName ≠ childOuterPair.contextBinder)
    (childDestinationOuterFresh : childDestinationName ≠ childOuterPair.contextBinder)
    (childIdFresh : childIdName ≠ childPair.contextBinder)
    (childDestinationFresh : childDestinationName ≠ childPair.contextBinder)
    (childOperandShape : program childOperand = some (.variable childClosure.parameter))
    (childOperandFresh : childClosure.parameter ≠ childConstructor.contextBinder)
    (childList : Value)
    (replacementBindings : ∀ work,
      let replacementEnv := extend env workName work
      CoreEval.lookup replacementEnv replacementWantedName = some wanted ∧
      CoreEval.lookup replacementEnv replacementParentName = some parent)
    (childBindings : ∀ work,
      let appendEnv := extend (extend env workName work) replacementTuple.contextBinder .context
      CoreEval.lookup appendEnv childCallName = some (.location childSelfAddress) ∧
      CoreEval.lookup appendEnv childListName = some childList ∧
      CoreEval.lookup appendEnv childIdName = some work ∧
      CoreEval.lookup appendEnv childDestinationName = some destination)
    (childSelfBinding : CoreEval.lookup childCaptureEnv.reverse childChecked.functionName = some (.location childSelfAddress))
    (childCaptureBindings : CaptureBindings program childChecked.captureNodes childCaptureValues childCaptureEnv)
    (childSelfResolution : Resolve start childSelfAddress childSelfResolved)
    (childSelfCell : readCell start childSelfResolved = some (.closureCode childChecked.code :: childCaptureValues))
    (childListRep : Children ids start childList children)
    (childLocated : Ash.NetworkLedger.CoreGenericInsert.LocatedEntries children)
    (updateChecked : Ash.NetworkLedger.CoreRecordUpdate.CheckedRecordUpdate recordsList program)
    (updateProjection : RecordProjectionShape program updateChecked.projection)
    (updateProjectionName : updateProjection.functionName = updateChecked.projectionName)
    (updateEntryName : updateProjection.recordName = updateChecked.entryName)
    (updateProjectionCode : updateProjection.code = updateChecked.projectionCode)
    (updateFunction updateArgument updateWantedNode updateReplacementNode updateListNode : NodeId)
    (updateCallName updateWantedName updateReplacementName updateListName : Binder)
    (updateSelfAddress updateSelfResolved updateComparisonAddress updateComparisonResolved
      updateProjectionAddress updateProjectionResolved : Nat)
    (updateCaptureValues : List Value) (updateCaptureEnv : Environment)
    (updateTriple : CheckedTuple program updateArgument none [updateWantedNode, updateReplacementNode, updateListNode])
    (updateCallShape : program updateNode = some (.apply updateFunction updateArgument))
    (updateFunctionShape : program updateFunction = some (.variable updateCallName))
    (updateWantedShape : program updateWantedNode = some (.variable updateWantedName))
    (updateReplacementShape : program updateReplacementNode = some (.variable updateReplacementName))
    (updateListShape : program updateListNode = some (.variable updateListName))
    (updateWantedFresh : updateWantedName ≠ updateTriple.contextBinder)
    (updateReplacementFresh : updateReplacementName ≠ updateTriple.contextBinder)
    (updateListFresh : updateListName ≠ updateTriple.contextBinder)
    (updateList : Value)
    (updateBindings : ∀ work replacement,
      let updateEnv := extend (extend env workName work) replacementName replacement
      CoreEval.lookup updateEnv updateCallName = some (.location updateSelfAddress) ∧
      CoreEval.lookup updateEnv updateWantedName = some wanted ∧
      CoreEval.lookup updateEnv updateReplacementName = some replacement ∧
      CoreEval.lookup updateEnv updateListName = some updateList)
    (updateSelfBinding : CoreEval.lookup updateCaptureEnv.reverse updateChecked.functionName = some (.location updateSelfAddress))
    (updateComparisonBinding : CoreEval.lookup updateCaptureEnv.reverse updateChecked.comparisonName = some (.location updateComparisonAddress))
    (updateProjectionBinding : CoreEval.lookup updateCaptureEnv.reverse updateChecked.projectionName = some (.location updateProjectionAddress))
    (updateCaptureBindings : CaptureBindings program updateChecked.captureNodes updateCaptureValues updateCaptureEnv)
    (updateSelfResolution : Resolve start updateSelfAddress updateSelfResolved)
    (updateSelfCell : readCell start updateSelfResolved = some (.closureCode updateChecked.code :: updateCaptureValues))
    (updateComparisonResolution : Resolve start updateComparisonAddress updateComparisonResolved)
    (updateComparisonCell : readCell start updateComparisonResolved = some [.closureCode updateChecked.comparator.code])
    (updateProjectionResolution : Resolve start updateProjectionAddress updateProjectionResolved)
    (updateProjectionCell : readCell start updateProjectionResolved = some [.closureCode updateChecked.projectionCode])
    (updateWantedRep : Ident recordsList start wanted wantedId)
    (updateListRep : Children recordsList start updateList records)
    (updateKeys : RepresentedEntries recordsList (RecordEntry updateProjection.record) start key records)
    (outputChecked : Ash.NetworkLedger.CoreInsert.CheckedInsert outputsList program)
    (outputFunction outputArgument outputCall outputListNode outputConstructorFunction outputConstructorArgument
      outputChildNode outputParentCall outputDestinationNode outputPayloadNode outputParentFunction outputParentArguments
      outputOwnerNode outputWantedNode outputParentOperand outputOperand : NodeId)
    (outputCallName outputListName outputChildName outputOwnerName outputWantedName outputDestinationName outputBytesName : Binder)
    (outputSelfAddress outputSelfResolved : Nat) (outputCaptureValues : List Value) (outputCaptureEnv : Environment)
    (outputOuterPair : CheckedTuple program outputArgument none [outputCall, outputListNode])
    (outputClosure : CheckedClosure program outputConstructorFunction)
    (outputConstructor : CheckedTuple program outputClosure.body (some workOutTag) [outputOperand])
    (outputTuple : CheckedTuple program outputConstructorArgument none [outputChildNode, outputParentCall, outputDestinationNode, outputPayloadNode])
    (outputParentClosure : CheckedClosure program outputParentFunction)
    (outputParentPair : CheckedTuple program outputParentArguments none [outputOwnerNode, outputWantedNode])
    (outputParentConstructor : CheckedTuple program outputParentClosure.body (some parentTag) [outputParentOperand])
    (outputCallShape : program outputNode = some (.apply outputFunction outputArgument))
    (outputFunctionShape : program outputFunction = some (.variable outputCallName))
    (outputListShape : program outputListNode = some (.variable outputListName))
    (outputListFresh : outputListName ≠ outputOuterPair.contextBinder)
    (outputShape : program outputCall = some (.apply outputConstructorFunction outputConstructorArgument))
    (outputOperandShape : program outputOperand = some (.variable outputClosure.parameter))
    (outputOperandFresh : outputClosure.parameter ≠ outputConstructor.contextBinder)
    (outputChildShape : program outputChildNode = some (.variable outputChildName))
    (outputParentShape : program outputParentCall = some (.apply outputParentFunction outputParentArguments))
    (outputOwnerShape : program outputOwnerNode = some (.variable outputOwnerName))
    (outputWantedShape : program outputWantedNode = some (.variable outputWantedName))
    (outputDestinationShape : program outputDestinationNode = some (.variable outputDestinationName))
    (outputBytesShape : program outputPayloadNode = some (.variable outputBytesName))
    (outputChildOuterFresh : outputChildName ≠ outputOuterPair.contextBinder)
    (outputOwnerOuterFresh : outputOwnerName ≠ outputOuterPair.contextBinder)
    (outputWantedOuterFresh : outputWantedName ≠ outputOuterPair.contextBinder)
    (outputDestinationOuterFresh : outputDestinationName ≠ outputOuterPair.contextBinder)
    (outputBytesOuterFresh : outputBytesName ≠ outputOuterPair.contextBinder)
    (outputChildFresh : outputChildName ≠ outputTuple.contextBinder)
    (outputOwnerFresh : outputOwnerName ≠ outputTuple.contextBinder)
    (outputWantedFresh : outputWantedName ≠ outputTuple.contextBinder)
    (outputDestinationFresh : outputDestinationName ≠ outputTuple.contextBinder)
    (outputBytesFresh : outputBytesName ≠ outputTuple.contextBinder)
    (outputOwnerParentFresh : outputOwnerName ≠ outputParentPair.contextBinder)
    (outputWantedParentFresh : outputWantedName ≠ outputParentPair.contextBinder)
    (outputParentOperandShape : program outputParentOperand = some (.variable outputParentClosure.parameter))
    (outputParentOperandFresh : outputParentClosure.parameter ≠ outputParentConstructor.contextBinder)
    (outputList : Value)
    (outputBindings : ∀ work replacement remaining,
      let outputEnv := extend (extend (extend env workName work) replacementName replacement) remainingName remaining
      CoreEval.lookup outputEnv outputCallName = some (.location outputSelfAddress) ∧
      CoreEval.lookup outputEnv outputListName = some outputList ∧
      CoreEval.lookup outputEnv outputChildName = some work ∧
      CoreEval.lookup outputEnv outputOwnerName = some (.integer (Int.ofNat owner)) ∧
      CoreEval.lookup outputEnv outputWantedName = some wanted ∧
      CoreEval.lookup outputEnv outputDestinationName = some destination ∧
      CoreEval.lookup outputEnv outputBytesName = some bytes)
    (outputSelfBinding : CoreEval.lookup outputCaptureEnv.reverse outputChecked.functionName = some (.location outputSelfAddress))
    (outputCaptureBindings : CaptureBindings program outputChecked.captureNodes outputCaptureValues outputCaptureEnv)
    (outputSelfResolution : Resolve start outputSelfAddress outputSelfResolved)
    (outputSelfCell : readCell start outputSelfResolved = some (.closureCode outputChecked.code :: outputCaptureValues))
    (outputListRep : Children outputsList start outputList outputs)
    (outputLocated : Ash.NetworkLedger.CoreGenericInsert.LocatedEntries outputs)
    (counterBinding : CoreEval.lookup env checkedResult.increment.counterBinder = some (.integer counter))
    (remainingBinder : checkedResult.remainingName = remainingName)
    (outgoingBinder : checkedResult.outgoingName = outgoingName)
    (childBinder : checkedResult.childName = workName)
    (counterWork : checkedResult.increment.counterBinder ≠ workName)
    (counterReplacement : checkedResult.increment.counterBinder ≠ replacementName)
    (counterRemaining : checkedResult.increment.counterBinder ≠ remainingName)
    (counterOutgoing : checkedResult.increment.counterBinder ≠ outgoingName)
    (workReplacement : workName ≠ replacementName) (workRemaining : workName ≠ remainingName)
    (workOutgoing : workName ≠ outgoingName) (remainingOutgoing : remainingName ≠ outgoingName)
    (evaluation : Eval program env first start result finish) :
    ∃ work replacement remaining outgoing output ledger status statusAddress,
      Ident ids finish work (.work owner counter) ∧
      ReplacementEntry ids recordTag openTag finish replacement wanted parent work destination children ∧
      Children recordsList finish remaining (Ash.NetworkLedger.update key wantedId replacement records) ∧
      WorkOutEntry workOutTag parentTag finish output work (.integer (Int.ofNat owner)) wanted destination bytes ∧
      Children outputsList finish outgoing (outputs ++ [output]) ∧
      Result finish result ledger status ∧
      NominalFields checkedResult.ledgerTag finish ledger [.integer (counter + 1), remaining, outgoing] ∧
      status = .location statusAddress ∧ Resolve finish statusAddress statusAddress ∧
      readCell finish statusAddress = some [.tag checkedResult.registeredTag, work] ∧ CommitFrame start finish := by
  obtain ⟨afterWork, afterReplacement, afterUpdate, afterOutput, work, replacement, remaining, outgoing,
    workEval, replacementEval, updateEval, outputEval, resultEval⟩ :=
    registration_commit_steps program env first second third fourth checkedResult.root workNode replacementNode updateNode outputNode
      workName replacementName remainingName outgoingName start finish result firstShape secondShape thirdShape fourthShape evaluation
  obtain ⟨workRep, workFrame⟩ := checked_work_initializer ids program workNode workFunction workArgument
    workOwnerNode workCounterNode workOperand workClosure workPair workConstructor env start afterWork work owner counter
    workOwnerName checkedResult.increment.counterBinder workCallShape workOwnerShape workCounterShape workOwnerFresh
    workCounterFresh workOwnerBinding counterBinding workOperandShape workOperandFresh bounded workEval
  obtain ⟨replacementWantedBinding, replacementParentBinding⟩ := replacementBindings work
  obtain ⟨childFunctionBinding, childListBinding, childIdBinding, childDestinationBinding⟩ := childBindings work
  obtain ⟨_, replacementRep, _, replacementAliases, replacementBound, replacementRetained⟩ :=
    checked_replacement_record ids program replacementNode replacementFunction replacementArgument replacementWantedNode
      replacementParentNode replacementOpenNode childAppendNode replacementOperand recordTag openTag replacementClosure
      replacementConstructor replacementTuple replacementOpenTuple _ afterWork afterReplacement replacement wanted parent work destination
      children replacementWantedName replacementParentName replacementCallShape replacementOperandShape replacementOperandFresh
      replacementWantedShape replacementParentShape replacementWantedFresh replacementParentFresh replacementWantedBinding
      replacementParentBinding (by
        intro before after value beforeAliases beforeRetained beforeBound appendEval
        have childFrame : CommitFrame start before := commit_frame_trans start afterWork before workFrame
          ⟨beforeAliases, beforeBound, beforeRetained⟩
        exact checked_append_child_call ids program childChecked childAppendNode childFunction childArgument childCall childListNode
          childConstructorFunction childConstructorArgument childIdNode childDestinationNode childOperand ids.child _ before after value
          childList work destination children childCallName childListName childIdName childDestinationName childSelfAddress childSelfResolved
          childCaptureValues childCaptureEnv childOuterPair childClosure childPair childConstructor childAppendShape childFunctionShape
          childFunctionBinding childListShape childListFresh childListBinding childCallShape childIdShape childDestinationShape
          childIdOuterFresh childDestinationOuterFresh childIdFresh childDestinationFresh childIdBinding childDestinationBinding
          childOperandShape childOperandFresh childSelfBinding childCaptureBindings
          (resolve_preserved childFrame.1 childFrame.2.2 childSelfResolution) (childFrame.2.2 childSelfResolved _ childSelfCell)
          beforeBound (children_retained ids start before childList children childFrame.1 childFrame.2.2 childListRep)
          childLocated appendEval) workFrame.2.1 replacementEval
  have replacementFrame : CommitFrame afterWork afterReplacement :=
    ⟨replacementAliases, replacementBound, replacementRetained⟩
  have workAfterReplacement := ident_retained ids afterWork afterReplacement work (.work owner counter)
    replacementFrame.1 replacementFrame.2.2 workRep
  have replacementTotal := commit_frame_trans start afterWork afterReplacement workFrame replacementFrame
  obtain ⟨updateFunctionBinding, updateWantedBinding, updateReplacementBinding, updateListBinding⟩ :=
    updateBindings work replacement
  obtain ⟨recordRep, updateFrame⟩ := checked_commit_update recordsList program updateChecked updateProjection
    updateProjectionName updateEntryName updateProjectionCode updateNode updateFunction updateArgument updateWantedNode
    updateReplacementNode updateListNode _ start afterReplacement afterUpdate remaining wanted replacement updateList wantedId key records
    updateCallName updateWantedName updateReplacementName updateListName updateSelfAddress updateSelfResolved updateComparisonAddress
    updateComparisonResolved updateProjectionAddress updateProjectionResolved updateCaptureValues updateCaptureEnv updateTriple
    updateCallShape updateFunctionShape updateFunctionBinding updateWantedShape updateReplacementShape updateListShape updateWantedFresh
    updateReplacementFresh updateListFresh updateWantedBinding updateReplacementBinding updateListBinding updateSelfBinding
    updateComparisonBinding updateProjectionBinding updateCaptureBindings updateSelfResolution updateSelfCell updateComparisonResolution
    updateComparisonCell updateProjectionResolution updateProjectionCell updateWantedRep updateListRep updateKeys replacementTotal updateEval
  have workAfterUpdate := ident_retained ids afterReplacement afterUpdate work (.work owner counter)
    updateFrame.1 updateFrame.2.2 workAfterReplacement
  have replacementAfterUpdate := replacement_entry_retained ids recordTag openTag afterReplacement afterUpdate
    replacement wanted parent work destination children updateFrame.1 updateFrame.2.2 replacementRep
  have updateTotal := commit_frame_trans start afterReplacement afterUpdate replacementTotal updateFrame
  obtain ⟨outputFunctionBinding, outputListBinding, outputChildBinding, outputOwnerBinding, outputWantedBinding,
    outputDestinationBinding, outputBytesBinding⟩ := outputBindings work replacement remaining
  obtain ⟨output, outputRep, outputsRep, _, outputAliases, outputBound, outputRetained⟩ :=
    checked_append_workout_call outputsList program outputChecked outputNode outputFunction outputArgument outputCall outputListNode
      outputConstructorFunction outputConstructorArgument outputChildNode outputParentCall outputDestinationNode outputPayloadNode
      outputParentFunction outputParentArguments outputOwnerNode outputWantedNode outputParentOperand outputOperand workOutTag parentTag
      _ afterUpdate afterOutput outgoing outputList work (.integer (Int.ofNat owner)) wanted destination bytes outputs outputCallName
      outputListName outputChildName outputOwnerName outputWantedName outputDestinationName outputBytesName outputSelfAddress outputSelfResolved
      outputCaptureValues outputCaptureEnv outputOuterPair outputClosure outputConstructor outputTuple outputParentClosure outputParentPair
      outputParentConstructor outputCallShape outputFunctionShape outputFunctionBinding outputListShape outputListFresh outputListBinding
      outputShape outputOperandShape outputOperandFresh outputChildShape outputParentShape outputOwnerShape outputWantedShape
      outputDestinationShape outputBytesShape outputChildOuterFresh outputOwnerOuterFresh outputWantedOuterFresh outputDestinationOuterFresh
      outputBytesOuterFresh outputChildFresh outputOwnerFresh outputWantedFresh outputDestinationFresh outputBytesFresh outputOwnerParentFresh
      outputWantedParentFresh outputChildBinding outputOwnerBinding outputWantedBinding outputDestinationBinding outputBytesBinding
      outputParentOperandShape outputParentOperandFresh outputSelfBinding outputCaptureBindings
      (resolve_preserved updateTotal.1 updateTotal.2.2 outputSelfResolution) (updateTotal.2.2 outputSelfResolved _ outputSelfCell)
      updateTotal.2.1 (children_retained outputsList start afterUpdate outputList outputs updateTotal.1 updateTotal.2.2 outputListRep)
      outputLocated outputEval
  have outputFrame : CommitFrame afterUpdate afterOutput := ⟨outputAliases, outputBound, outputRetained⟩
  have workAfterOutput := ident_retained ids afterUpdate afterOutput work (.work owner counter)
    outputFrame.1 outputFrame.2.2 workAfterUpdate
  have replacementAfterOutput := replacement_entry_retained ids recordTag openTag afterUpdate afterOutput
    replacement wanted parent work destination children outputFrame.1 outputFrame.2.2 replacementAfterUpdate
  have recordsAfterOutput := children_retained recordsList afterUpdate afterOutput remaining _
    outputFrame.1 outputFrame.2.2 recordRep
  have outputTotal := commit_frame_trans start afterUpdate afterOutput updateTotal outputFrame
  obtain ⟨counterBound, remainingBound, outgoingBound, childBound⟩ :=
    commit_result_bindings env checkedResult.increment.counterBinder workName replacementName remainingName outgoingName
      work replacement remaining outgoing counter counterBinding counterWork counterReplacement counterRemaining counterOutgoing
      workReplacement workRemaining workOutgoing remainingOutgoing
  have remainingBinding : CoreEval.lookup (extend (extend (extend (extend env workName work) replacementName replacement)
      remainingName remaining) outgoingName outgoing) checkedResult.remainingName = some remaining := by
    rw [remainingBinder]; exact remainingBound
  have outgoingBinding : CoreEval.lookup (extend (extend (extend (extend env workName work) replacementName replacement)
      remainingName remaining) outgoingName outgoing) checkedResult.outgoingName = some outgoing := by
    rw [outgoingBinder]; exact outgoingBound
  have childBinding : CoreEval.lookup (extend (extend (extend (extend env workName work) replacementName replacement)
      remainingName remaining) outgoingName outgoing) checkedResult.childName = some work := by
    rw [childBinder]; exact childBound
  obtain ⟨ledger, status, statusAddress, resultRep, ledgerRep, statusEq, statusResolution, statusCell,
    resultAliases, resultBound, resultRetained⟩ :=
    checked_success_fields program buffers checkedResult _ afterOutput finish result remaining outgoing work counter
      counterBound remainingBinding outgoingBinding childBinding nonnegative outputFrame.2.1 resultEval
  have finalFrame : CommitFrame afterOutput finish := ⟨resultAliases, resultBound, resultRetained⟩
  refine ⟨work, replacement, remaining, outgoing, output, ledger, status, statusAddress,
    ident_retained ids afterOutput finish work (.work owner counter) resultAliases resultRetained workAfterOutput,
    replacement_entry_retained ids recordTag openTag afterOutput finish replacement wanted parent work destination children
      resultAliases resultRetained replacementAfterOutput,
    children_retained recordsList afterOutput finish remaining _ resultAliases resultRetained recordsAfterOutput,
    workout_entry_retained workOutTag parentTag afterOutput finish output work (.integer (Int.ofNat owner)) wanted destination bytes
      resultAliases resultRetained outputRep,
    children_retained outputsList afterOutput finish outgoing _ resultAliases resultRetained outputsRep,
    resultRep, ledgerRep, statusEq, statusResolution, statusCell,
    commit_frame_trans start afterOutput finish outputTotal finalFrame⟩

/-- Decoded returned fields implement the existing open registration transition. -/
theorem decoded_open_registration (owner : Nat) (counter : Int) (wanted : Id) (destination : Nat)
    (payload : List UInt8) (key : Value → Id) (recordDecode : Value → Ash.NetworkLedger.Record)
    (outputDecode : Value → Ash.NetworkLedger.Output) (records outputs : List Value)
    (found replacement newOutput : Value)
    (keys : ∀ entry ∈ records, key entry = (recordDecode entry).id)
    (lookupResult : Ash.NetworkLedger.lookup key wanted records = some found)
    (isOpen : (recordDecode found).phase = .open)
    (replacementFields : recordDecode replacement =
      { recordDecode found with children :=
        Ash.NetworkLedger.insert ⟨.work owner counter, destination⟩ (recordDecode found).children })
    (outputFields : outputDecode newOutput =
      .work (.work owner counter) ⟨owner, wanted⟩ destination payload) :
    (⟨owner, counter + 1,
       (Ash.NetworkLedger.update key wanted replacement records).map recordDecode,
       (outputs ++ [newOutput]).map outputDecode⟩, .registered (.work owner counter)) =
      Ash.NetworkLedger.register ⟨owner, counter, records.map recordDecode, outputs.map outputDecode⟩
        wanted destination payload := by
  have foundDecoded := decode_lookup key Ash.NetworkLedger.Record.id recordDecode wanted records keys
  have updatedDecoded := decode_update key Ash.NetworkLedger.Record.id recordDecode wanted replacement records keys
  simp only [lookupResult, Option.map_some] at foundDecoded
  rw [updatedDecoded, replacementFields]
  simp [Ash.NetworkLedger.register, ← foundDecoded, isOpen, outputFields]

/-- Missing lookup preserves the decoded ledger and returns Rejected. -/
theorem decoded_missing_registration (owner : Nat) (counter : Int) (wanted : Id) (destination : Nat)
    (payload : List UInt8) (key : Value → Id) (recordDecode : Value → Ash.NetworkLedger.Record)
    (outputDecode : Value → Ash.NetworkLedger.Output) (records outputs : List Value)
    (keys : ∀ entry ∈ records, key entry = (recordDecode entry).id)
    (lookupResult : Ash.NetworkLedger.lookup key wanted records = none) :
    Ash.NetworkLedger.register ⟨owner, counter, records.map recordDecode, outputs.map outputDecode⟩
      wanted destination payload =
      (⟨owner, counter, records.map recordDecode, outputs.map outputDecode⟩, .rejected) := by
  have foundDecoded := decode_lookup key Ash.NetworkLedger.Record.id recordDecode wanted records keys
  simp only [lookupResult, Option.map_none] at foundDecoded
  simp [Ash.NetworkLedger.register, ← foundDecoded]

/-- A found Closed record preserves the decoded ledger and returns Rejected. -/
theorem decoded_closed_registration (owner : Nat) (counter : Int) (wanted : Id) (destination : Nat)
    (payload : List UInt8) (key : Value → Id) (recordDecode : Value → Ash.NetworkLedger.Record)
    (outputDecode : Value → Ash.NetworkLedger.Output) (records outputs : List Value) (found : Value)
    (keys : ∀ entry ∈ records, key entry = (recordDecode entry).id)
    (lookupResult : Ash.NetworkLedger.lookup key wanted records = some found)
    (isClosed : (recordDecode found).phase = .closed) :
    Ash.NetworkLedger.register ⟨owner, counter, records.map recordDecode, outputs.map outputDecode⟩
      wanted destination payload =
      (⟨owner, counter, records.map recordDecode, outputs.map outputDecode⟩, .rejected) := by
  have foundDecoded := decode_lookup key Ash.NetworkLedger.Record.id recordDecode wanted records keys
  simp only [lookupResult, Option.map_some] at foundDecoded
  simp [Ash.NetworkLedger.register, ← foundDecoded, isClosed]

/-- Finite actual entries correspond in order to finite semantic entries. -/
inductive RelatedValues {A : Type} (rel : Value → A → Prop) : List Value → List A → Prop where
  | nil : RelatedValues rel [] []
  | cons {value semantic values semantics} (head : rel value semantic)
      (tail : RelatedValues rel values semantics) :
      RelatedValues rel (value :: values) (semantic :: semantics)

theorem related_values_snoc {A : Type} (rel : Value → A → Prop)
    (values : List Value) (semantics : List A) (value : Value) (semantic : A)
    (prior : RelatedValues rel values semantics) (last : rel value semantic) :
    RelatedValues rel (values ++ [value]) (semantics ++ [semantic]) := by
  induction prior with
  | nil => exact .cons last .nil
  | cons head _ ih => exact .cons head ih

/-- A Child semantic value keeps its original ID cell and exact destination. -/
def DecodedChild (c : Constructors) (store : Store) (value : Value) (child : Ash.NetworkLedger.Child) : Prop :=
  ∃ key, Entry c store value key (.integer (Int.ofNat child.destination)) ∧ Ident c store key child.id

theorem decoded_child_retained (c : Constructors) (before after : Store)
    (value : Value) (child : Ash.NetworkLedger.Child) (aliases : after.aliases = before.aliases)
    (cells : ∀ address old, readCell before address = some old → readCell after address = some old)
    (rep : DecodedChild c before value child) : DecodedChild c after value child := by
  obtain ⟨key, entry, ident⟩ := rep
  exact ⟨key, entry_retained c before after value key (.integer (Int.ofNat child.destination)) aliases cells entry,
    ident_retained c before after key child.id aliases cells ident⟩

theorem decoded_children_retained (c : Constructors) (before after : Store)
    (values : List Value) (children : List Ash.NetworkLedger.Child) (aliases : after.aliases = before.aliases)
    (cells : ∀ address old, readCell before address = some old → readCell after address = some old)
    (rep : RelatedValues (DecodedChild c before) values children) :
    RelatedValues (DecodedChild c after) values children := by
  induction rep with
  | nil => exact .nil
  | cons head _ ih => exact .cons (decoded_child_retained c before after _ _ aliases cells head) ih

/-- A represented parent is either the exact nullary absence or the two-field address. -/
def DecodedParent (c : Constructors) (noParent parentTag : Constructor) (store : Store)
    (value : Value) (parent : Option Address) : Prop :=
  match parent with
  | none => ∃ address resolved, value = .location address ∧ Resolve store address resolved ∧
      readCell store resolved = some [.tag noParent]
  | some address => ∃ key, NominalFields parentTag store value [.integer (Int.ofNat address.worker), key] ∧
      Ident c store key address.id

/-- A represented phase is the exact checked Open or Closed constructor. -/
def DecodedPhase (openTag closedTag : Constructor) (store : Store) (value : Value) (phase : Phase) : Prop :=
  ∃ address resolved, value = .location address ∧ Resolve store address resolved ∧
    readCell store resolved = some [.tag (if phase = .open then openTag else closedTag)]

/-- The semantic Record contains the exact key, parent, phase and finite child sequence. -/
def DecodedRecord (c : Constructors) (recordTag noParent parentTag openTag closedTag : Constructor)
    (store : Store) (value : Value) (record : Ash.NetworkLedger.Record) : Prop :=
  ∃ key parent phase childList entries,
    NominalFields recordTag store value [key, parent, phase, childList] ∧
    Ident c store key record.id ∧ DecodedParent c noParent parentTag store parent record.parent ∧
    DecodedPhase openTag closedTag store phase record.phase ∧ Children c store childList entries ∧
    RelatedValues (DecodedChild c store) entries record.children

/-- Actual replacement fields decode to the old Record with the new whole Child appended. -/
theorem replacement_record_decodes (c : Constructors) (recordTag noParent parentTag openTag closedTag : Constructor)
    (store : Store) (value wanted parent work : Value) (owner : Nat) (counter : Int) (destination : Nat)
    (entries : List Value) (record : Ash.NetworkLedger.Record)
    (replacement : ReplacementEntry c recordTag openTag store value wanted parent work
      (.integer (Int.ofNat destination)) entries)
    (wantedRep : Ident c store wanted record.id)
    (parentRep : DecodedParent c noParent parentTag store parent record.parent)
    (oldChildren : RelatedValues (DecodedChild c store) entries record.children)
    (workRep : Ident c store work (.work owner counter)) :
    DecodedRecord c recordTag noParent parentTag openTag closedTag store value
      ({ record with phase := Phase.open, children := Ash.NetworkLedger.insert ⟨.work owner counter, destination⟩ record.children }) := by
  obtain ⟨fields, nominal, phase, appended, newEntry, same, phaseResolution, phaseCell, listRep, childRep⟩ := replacement
  subst fields
  have newChild : DecodedChild c store newEntry ⟨.work owner counter, destination⟩ :=
    ⟨work, child_from_fields c store newEntry work (.integer (Int.ofNat destination)) childRep, workRep⟩
  refine ⟨wanted, parent, .location phase, appended, entries ++ [newEntry], nominal, wantedRep, parentRep, ?_, listRep, ?_⟩
  · exact ⟨phase, phase, rfl, phaseResolution, by simpa using phaseCell⟩
  · simpa [Ash.NetworkLedger.insert] using
      related_values_snoc (DecodedChild c store) entries record.children newEntry ⟨.work owner counter, destination⟩ oldChildren newChild

/-- Output decoding preserves each whole Work or Ack envelope. -/
def DecodedOutput (c : Constructors) (noParent parentTag workOutTag ackOutTag : Constructor)
    (bytesRep : Value → List UInt8 → Prop) (store : Store) (value : Value) (output : Output) : Prop :=
  match output with
  | .work child parent destination payload =>
      ∃ childValue wantedValue bytes,
        WorkOutEntry workOutTag parentTag store value childValue (.integer (Int.ofNat parent.worker))
          wantedValue (.integer (Int.ofNat destination)) bytes ∧
        Ident c store childValue child ∧ Ident c store wantedValue parent.id ∧ bytesRep bytes payload
  | .ack parent child =>
      ∃ parentValue childValue,
        NominalFields ackOutTag store value [parentValue, childValue] ∧
        DecodedParent c noParent parentTag store parentValue (some parent) ∧ Ident c store childValue child

/-- The checked WorkOut payload is the semantic work envelope. -/
theorem workout_decodes (c : Constructors) (noParent parentTag workOutTag ackOutTag : Constructor)
    (bytesRep : Value → List UInt8 → Prop) (store : Store)
    (value work wanted bytes : Value) (owner : Nat) (counter : Int) (wantedId : Id)
    (destination : Nat) (payload : List UInt8)
    (output : WorkOutEntry workOutTag parentTag store value work (.integer (Int.ofNat owner))
      wanted (.integer (Int.ofNat destination)) bytes)
    (workRep : Ident c store work (.work owner counter)) (wantedRep : Ident c store wanted wantedId)
    (bytesMeaning : bytesRep bytes payload) :
    DecodedOutput c noParent parentTag workOutTag ackOutTag bytesRep store value
      (.work (.work owner counter) ⟨owner, wantedId⟩ destination payload) := by
  exact ⟨work, wanted, bytes, output, workRep, wantedRep, bytesMeaning⟩

/-- Lookup selects corresponding first matches in related finite records. -/
theorem related_values_lookup {A : Type} (rel : Value → A → Prop)
    (keyValue : Value → Id) (keySemantic : A → Id) (wanted : Id)
    (values : List Value) (semantics : List A) (related : RelatedValues rel values semantics)
    (keys : ∀ value ∈ values, ∀ semantic, rel value semantic → keyValue value = keySemantic semantic) :
    match Ash.NetworkLedger.lookup keyValue wanted values, Ash.NetworkLedger.lookup keySemantic wanted semantics with
    | none, none => True
    | some value, some semantic => rel value semantic
    | _, _ => False := by
  induction related with
  | nil => simp [Ash.NetworkLedger.lookup]
  | @cons value semantic values semantics head tail ih =>
    have sameKey := keys value (by simp) semantic head
    have tailKeys : ∀ value ∈ values, ∀ semantic, rel value semantic → keyValue value = keySemantic semantic := by
      intro item member other rep
      exact keys item (by simp [member]) other rep
    by_cases same : keyValue value = wanted
    · simp [Ash.NetworkLedger.lookup, same, ← sameKey, head]
    · have semanticDifferent : keySemantic semantic ≠ wanted := by simpa [← sameKey] using same
      simp [Ash.NetworkLedger.lookup, same, semanticDifferent, ih tailKeys]

/-- First-match update preserves the finite Record correspondence and original order. -/
theorem related_values_update {A : Type} (rel : Value → A → Prop)
    (keyValue : Value → Id) (keySemantic : A → Id) (wanted : Id)
    (values : List Value) (semantics : List A) (related : RelatedValues rel values semantics)
    (replacement : Value) (semanticReplacement : A) (newRep : rel replacement semanticReplacement)
    (keys : ∀ value ∈ values, ∀ semantic, rel value semantic → keyValue value = keySemantic semantic) :
    RelatedValues rel (Ash.NetworkLedger.update keyValue wanted replacement values)
      (Ash.NetworkLedger.update keySemantic wanted semanticReplacement semantics) := by
  induction related with
  | nil => exact .nil
  | @cons value semantic values semantics head tail ih =>
    have sameKey := keys value (by simp) semantic head
    have tailKeys : ∀ value ∈ values, ∀ semantic, rel value semantic → keyValue value = keySemantic semantic := by
      intro item member other rep
      exact keys item (by simp [member]) other rep
    by_cases same : keyValue value = wanted
    · have semanticSame : keySemantic semantic = wanted := by simpa [← sameKey] using same
      simpa [Ash.NetworkLedger.update, same, semanticSame] using RelatedValues.cons newRep tail
    · have semanticDifferent : keySemantic semantic ≠ wanted := by simpa [← sameKey] using same
      simpa [Ash.NetworkLedger.update, same, semanticDifferent] using RelatedValues.cons head (ih tailKeys)

/-- A Ledger decodes its exact counter, finite records and finite output sequence. -/
def DecodedLedger (ids recordsList outputsList : Constructors)
    (ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag : Constructor)
    (bytesRep : Value → List UInt8 → Prop) (store : Store) (value : Value) (ledger : Ledger) : Prop :=
  ∃ recordList outputList records outputs,
    NominalFields ledgerTag store value [.integer ledger.next, recordList, outputList] ∧
    Children recordsList store recordList records ∧
    RelatedValues (DecodedRecord ids recordTag noParent parentTag openTag closedTag store) records ledger.records ∧
    Children outputsList store outputList outputs ∧
    RelatedValues (DecodedOutput ids noParent parentTag workOutTag ackOutTag bytesRep store) outputs ledger.outputs

/-- The actual successor fields decode by first-match update and whole-output append. -/
theorem decoded_commit_successor (ids recordsList outputsList : Constructors)
    (ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag : Constructor)
    (bytesRep : Value → List UInt8 → Prop) (store : Store) (ledgerValue recordList outputList replacement newOutput : Value)
    (ledger : Ledger) (wanted : Id) (updated : Ash.NetworkLedger.Record) (output : Output)
    (records outputs : List Value) (key : Value → Id)
    (ledgerFields : NominalFields ledgerTag store ledgerValue [.integer (ledger.next + 1), recordList, outputList])
    (recordListRep : Children recordsList store recordList (Ash.NetworkLedger.update key wanted replacement records))
    (recordsRep : RelatedValues (DecodedRecord ids recordTag noParent parentTag openTag closedTag store) records ledger.records)
    (replacementRep : DecodedRecord ids recordTag noParent parentTag openTag closedTag store replacement updated)
    (keys : ∀ value ∈ records, ∀ semantic, DecodedRecord ids recordTag noParent parentTag openTag closedTag store value semantic →
      key value = semantic.id)
    (outputListRep : Children outputsList store outputList (outputs ++ [newOutput]))
    (outputsRep : RelatedValues (DecodedOutput ids noParent parentTag workOutTag ackOutTag bytesRep store) outputs ledger.outputs)
    (newOutputRep : DecodedOutput ids noParent parentTag workOutTag ackOutTag bytesRep store newOutput output) :
    DecodedLedger ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag
      bytesRep store ledgerValue
      ({ ledger with next := ledger.next + 1, records := Ash.NetworkLedger.update Ash.NetworkLedger.Record.id wanted updated ledger.records, outputs := ledger.outputs ++ [output] }) := by
  refine ⟨recordList, outputList, Ash.NetworkLedger.update key wanted replacement records, outputs ++ [newOutput],
    ledgerFields, recordListRep, ?_, outputListRep, ?_⟩
  · exact related_values_update (DecodedRecord ids recordTag noParent parentTag openTag closedTag store)
      key Ash.NetworkLedger.Record.id wanted records ledger.records recordsRep replacement updated replacementRep keys
  · exact related_values_snoc (DecodedOutput ids noParent parentTag workOutTag ackOutTag bytesRep store)
      outputs ledger.outputs newOutput output outputsRep newOutputRep

/-- A registration status preserves the exact returned identity. -/
def DecodedRegistration (ids : Constructors) (rejectedTag registeredTag : Constructor)
    (store : Store) (value : Value) (registration : Registration) : Prop :=
  match registration with
  | .rejected => ∃ address resolved, value = .location address ∧ Resolve store address resolved ∧
      readCell store resolved = some [.tag rejectedTag]
  | .registered id => ∃ address resolved child, value = .location address ∧ Resolve store address resolved ∧
      readCell store resolved = some [.tag registeredTag, child] ∧ Ident ids store child id

/-- The actual result tuple represents both the returned Ledger and status. -/
def DecodedRegistrationResult (ids recordsList outputsList : Constructors)
    (ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag rejectedTag registeredTag : Constructor)
    (bytesRep : Value → List UInt8 → Prop) (store : Store) (value : Value) (semantic : Ledger × Registration) : Prop :=
  ∃ ledger status, Result store value ledger status ∧
    DecodedLedger ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag
      bytesRep store ledger semantic.1 ∧
    DecodedRegistration ids rejectedTag registeredTag store status semantic.2

/-- Strict commit fields and finite input representations decode to register's open result. -/
theorem decoded_open_commit (ids recordsList outputsList : Constructors)
    (ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag rejectedTag registeredTag : Constructor)
    (bytesRep : Value → List UInt8 → Prop) (store : Store)
    (result ledgerValue status remaining outgoing replacement newOutput work wanted parent bytes : Value)
    (statusAddress : Nat) (ledger : Ledger) (wantedId : Id) (destination : Nat) (payload : List UInt8)
    (records outputs children : List Value) (key : Value → Id) (found : Ash.NetworkLedger.Record)
    (resultRep : Result store result ledgerValue status)
    (ledgerFields : NominalFields ledgerTag store ledgerValue [.integer (ledger.next + 1), remaining, outgoing])
    (statusEq : status = .location statusAddress) (statusResolution : Resolve store statusAddress statusAddress)
    (statusCell : readCell store statusAddress = some [.tag registeredTag, work])
    (workRep : Ident ids store work (.work ledger.owner ledger.next))
    (wantedRep : Ident ids store wanted wantedId)
    (parentRep : DecodedParent ids noParent parentTag store parent found.parent)
    (childEntries : RelatedValues (DecodedChild ids store) children found.children)
    (replacementRep : ReplacementEntry ids recordTag openTag store replacement wanted parent work
      (.integer (Int.ofNat destination)) children)
    (recordListRep : Children recordsList store remaining (Ash.NetworkLedger.update key wantedId replacement records))
    (recordsRep : RelatedValues (DecodedRecord ids recordTag noParent parentTag openTag closedTag store) records ledger.records)
    (keys : ∀ value ∈ records, ∀ semantic, DecodedRecord ids recordTag noParent parentTag openTag closedTag store value semantic →
      key value = semantic.id)
    (newOutputRep : WorkOutEntry workOutTag parentTag store newOutput work (.integer (Int.ofNat ledger.owner))
      wanted (.integer (Int.ofNat destination)) bytes)
    (outputListRep : Children outputsList store outgoing (outputs ++ [newOutput]))
    (outputsRep : RelatedValues (DecodedOutput ids noParent parentTag workOutTag ackOutTag bytesRep store) outputs ledger.outputs)
    (bytesMeaning : bytesRep bytes payload)
    (lookupResult : Ash.NetworkLedger.lookup Ash.NetworkLedger.Record.id wantedId ledger.records = some found)
    (isOpen : found.phase = .open) :
    DecodedRegistrationResult ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag workOutTag
      ackOutTag rejectedTag registeredTag bytesRep store result (Ash.NetworkLedger.register ledger wantedId destination payload) := by
  have foundKey : found.id = wantedId :=
    (Ash.NetworkLedger.lookup_sound Ash.NetworkLedger.Record.id wantedId ledger.records found lookupResult).2
  have foundWanted : Ident ids store wanted found.id := by simpa [foundKey] using wantedRep
  have updatedRep := replacement_record_decodes ids recordTag noParent parentTag openTag closedTag store replacement wanted parent work
    ledger.owner ledger.next destination children found replacementRep foundWanted parentRep childEntries workRep
  have outputRep := workout_decodes ids noParent parentTag workOutTag ackOutTag bytesRep store newOutput work wanted bytes ledger.owner
    ledger.next wantedId destination payload newOutputRep workRep wantedRep bytesMeaning
  have successorRep := decoded_commit_successor ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag
    workOutTag ackOutTag bytesRep store ledgerValue remaining outgoing replacement newOutput ledger wantedId
    { found with phase := .open, children := Ash.NetworkLedger.insert ⟨.work ledger.owner ledger.next, destination⟩ found.children }
    (.work (.work ledger.owner ledger.next) ⟨ledger.owner, wantedId⟩ destination payload) records outputs key ledgerFields
    recordListRep recordsRep updatedRep keys outputListRep outputsRep outputRep
  have statusRep : DecodedRegistration ids rejectedTag registeredTag store status (.registered (.work ledger.owner ledger.next)) :=
    ⟨statusAddress, statusAddress, work, statusEq, statusResolution, statusCell, workRep⟩
  refine ⟨ledgerValue, status, resultRep, ?_⟩
  simpa [Ash.NetworkLedger.register, lookupResult, isOpen] using And.intro successorRep statusRep

/-- Related finite sequences remain related when each entry representation is retained. -/
theorem related_values_preserved {A : Type} (beforeRel afterRel : Value → A → Prop)
    (values : List Value) (semantics : List A) (related : RelatedValues beforeRel values semantics)
    (preserved : ∀ value semantic, beforeRel value semantic → afterRel value semantic) :
    RelatedValues afterRel values semantics := by
  induction related with
  | nil => exact .nil
  | cons head _ ih => exact .cons (preserved _ _ head) ih

theorem decoded_parent_retained (c : Constructors) (noParent parentTag : Constructor)
    (before after : Store) (value : Value) (parent : Option Address)
    (aliases : after.aliases = before.aliases)
    (cells : ∀ address old, readCell before address = some old → readCell after address = some old)
    (rep : DecodedParent c noParent parentTag before value parent) : DecodedParent c noParent parentTag after value parent := by
  cases parent with
  | none =>
    obtain ⟨address, resolved, same, resolution, cell⟩ := rep
    exact ⟨address, resolved, same, resolve_preserved aliases cells resolution, cells resolved _ cell⟩
  | some parent =>
    obtain ⟨key, nominal, ident⟩ := rep
    exact ⟨key, nominal_fields_retained parentTag before after value _ aliases cells nominal,
      ident_retained c before after key parent.id aliases cells ident⟩

theorem decoded_phase_retained (openTag closedTag : Constructor) (before after : Store) (value : Value) (phase : Phase)
    (aliases : after.aliases = before.aliases)
    (cells : ∀ address old, readCell before address = some old → readCell after address = some old)
    (rep : DecodedPhase openTag closedTag before value phase) : DecodedPhase openTag closedTag after value phase := by
  obtain ⟨address, resolved, same, resolution, cell⟩ := rep
  exact ⟨address, resolved, same, resolve_preserved aliases cells resolution, cells resolved _ cell⟩

theorem decoded_record_retained (c : Constructors) (recordTag noParent parentTag openTag closedTag : Constructor)
    (before after : Store) (value : Value) (record : Ash.NetworkLedger.Record)
    (aliases : after.aliases = before.aliases)
    (cells : ∀ address old, readCell before address = some old → readCell after address = some old)
    (rep : DecodedRecord c recordTag noParent parentTag openTag closedTag before value record) :
    DecodedRecord c recordTag noParent parentTag openTag closedTag after value record := by
  obtain ⟨key, parent, phase, childList, entries, nominal, ident, parentRep, phaseRep, listRep, entriesRep⟩ := rep
  exact ⟨key, parent, phase, childList, entries, nominal_fields_retained recordTag before after value _ aliases cells nominal,
    ident_retained c before after key record.id aliases cells ident,
    decoded_parent_retained c noParent parentTag before after parent record.parent aliases cells parentRep,
    decoded_phase_retained openTag closedTag before after phase record.phase aliases cells phaseRep,
    children_retained c before after childList entries aliases cells listRep,
    decoded_children_retained c before after entries record.children aliases cells entriesRep⟩

theorem decoded_output_retained (c : Constructors) (noParent parentTag workOutTag ackOutTag : Constructor)
    (bytesRep : Value → List UInt8 → Prop) (before after : Store) (value : Value) (output : Output)
    (aliases : after.aliases = before.aliases)
    (cells : ∀ address old, readCell before address = some old → readCell after address = some old)
    (rep : DecodedOutput c noParent parentTag workOutTag ackOutTag bytesRep before value output) :
    DecodedOutput c noParent parentTag workOutTag ackOutTag bytesRep after value output := by
  cases output with
  | work child parent destination payload =>
    obtain ⟨childValue, wantedValue, bytes, outputRep, childRep, wantedRep, bytesMeaning⟩ := rep
    exact ⟨childValue, wantedValue, bytes,
      workout_entry_retained workOutTag parentTag before after value childValue (.integer (Int.ofNat parent.worker))
        wantedValue (.integer (Int.ofNat destination)) bytes aliases cells outputRep,
      ident_retained c before after childValue child aliases cells childRep,
      ident_retained c before after wantedValue parent.id aliases cells wantedRep, bytesMeaning⟩
  | ack parent child =>
    obtain ⟨parentValue, childValue, nominal, parentRep, childRep⟩ := rep
    exact ⟨parentValue, childValue, nominal_fields_retained ackOutTag before after value _ aliases cells nominal,
      decoded_parent_retained c noParent parentTag before after parentValue (some parent) aliases cells parentRep,
      ident_retained c before after childValue child aliases cells childRep⟩

/-- One resolved nominal value determines a unique ordered field list. -/
theorem nominal_fields_unique (tag : Constructor) (store : Store) (value : Value) (left right : List Value)
    (first : NominalFields tag store value left) (second : NominalFields tag store value right) : left = right := by
  obtain ⟨firstAddress, firstResolved, firstPayload, firstTuple, firstEq, firstResolution, firstCell,
    firstPayloadResolution, firstFields⟩ := first
  obtain ⟨secondAddress, secondResolved, secondPayload, secondTuple, secondEq, secondResolution, secondCell,
    secondPayloadResolution, secondFields⟩ := second
  have addressEq : firstAddress = secondAddress := by simpa using firstEq.symm.trans secondEq
  subst secondAddress
  have outerEq := resolved_fields_unique firstResolution secondResolution firstCell secondCell
  have payloadEq : firstPayload = secondPayload := by simpa using outerEq
  subst secondPayload
  exact resolved_fields_unique firstPayloadResolution secondPayloadResolution firstFields secondFields

/-- The actual Record match exposes exactly the fields in its finite decoding. -/
theorem decoded_record_fields (c : Constructors) (recordTag noParent parentTag openTag closedTag : Constructor)
    (store : Store) (value wanted parent phase childList : Value) (record : Ash.NetworkLedger.Record)
    (actualFields : NominalFields recordTag store value [wanted, parent, phase, childList])
    (decoded : DecodedRecord c recordTag noParent parentTag openTag closedTag store value record) :
    ∃ entries, Ident c store wanted record.id ∧ DecodedParent c noParent parentTag store parent record.parent ∧
      DecodedPhase openTag closedTag store phase record.phase ∧ Children c store childList entries ∧
      RelatedValues (DecodedChild c store) entries record.children := by
  obtain ⟨actualWanted, actualParent, actualPhase, actualChildren, entries, nominal, ident, parentRep, phaseRep,
    listRep, entriesRep⟩ := decoded
  have fields := nominal_fields_unique recordTag store value [wanted, parent, phase, childList]
    [actualWanted, actualParent, actualPhase, actualChildren] actualFields nominal
  simp only [List.cons.injEq, and_true] at fields
  obtain ⟨rfl, rfl, rfl, rfl⟩ := fields
  exact ⟨entries, ident, parentRep, phaseRep, listRep, entriesRep⟩

/-- Distinct phase constructors make an actual Open match semantically Open. -/
theorem decoded_phase_open (openTag closedTag : Constructor) (store : Store) (value : Value) (phase : Phase)
    (different : openTag ≠ closedTag) (decoded : DecodedPhase openTag closedTag store value phase)
    (address resolved : Nat) (same : value = .location address)
    (resolution : Resolve store address resolved) (cell : readCell store resolved = some [.tag openTag]) :
    phase = .open := by
  obtain ⟨otherAddress, otherResolved, otherEq, otherResolution, otherCell⟩ := decoded
  have addressEq : address = otherAddress := by simpa using same.symm.trans otherEq
  subst otherAddress
  have fields := resolved_fields_unique resolution otherResolution cell otherCell
  cases phase with
  | «open» => rfl
  | closed =>
    simp at fields
    exact False.elim (different fields)

/-- List-specific constructor sets agree on the identity constructors. -/
theorem ident_same_tags (first second : Constructors) (store : Store) (value : Value) (id : Id)
    (rootSame : first.root = second.root) (workSame : first.work = second.work)
    (rep : Ident first store value id) : Ident second store value id := by
  cases rep with
  | root address resolved resolution cell =>
    exact Ident.root address resolved resolution (by simpa [← rootSame] using cell)
  | work address resolved payload tuple allocator serial resolution cell payloadResolution fields =>
    exact Ident.work address resolved payload tuple allocator serial resolution
      (by simpa [← workSame] using cell) payloadResolution fields

/-- The checked projection key and a decoded whole Record identify the same ID. -/
theorem decoded_record_keys (ids recordsList : Constructors)
    (recordTag noParent parentTag openTag closedTag : Constructor) (store : Store)
    (records : List Value) (key : Value → Id)
    (rootSame : recordsList.root = ids.root) (workSame : recordsList.work = ids.work)
    (represented : RepresentedEntries recordsList (RecordEntry recordTag) store key records) :
    ∀ value ∈ records, ∀ semantic,
      DecodedRecord ids recordTag noParent parentTag openTag closedTag store value semantic → key value = semantic.id := by
  intro value member semantic decoded
  obtain ⟨_, keyAddress, _, entry, keyRep⟩ := represented value member
  obtain ⟨address, resolved, payload, tuple, parent, phase, children, same, resolution, cell, payloadResolution, fields⟩ := entry
  have nominal : NominalFields recordTag store value [.location keyAddress, parent, phase, children] :=
    ⟨address, resolved, payload, tuple, same, resolution, cell, payloadResolution, fields⟩
  obtain ⟨decodedKey, decodedParent, decodedPhase, decodedChildren, _, decodedNominal, decodedKeyRep, _⟩ := decoded
  have fieldEq := nominal_fields_unique recordTag store value [.location keyAddress, parent, phase, children]
    [decodedKey, decodedParent, decodedPhase, decodedChildren] nominal decodedNominal
  have keyEq : Value.location keyAddress = decodedKey := by
    have heads := congrArg List.head? fieldEq
    simpa using heads
  have keyRep' : Ident ids store decodedKey (key value) := by
    rw [← keyEq]
    exact ident_same_tags recordsList ids store (.location keyAddress) (key value) rootSame workSame keyRep
  exact ident_unique ids store decodedKey (key value) semantic.id keyRep' decodedKeyRep

/-- Actual checked commit execution decodes to the semantic open registration. -/
theorem registration_commit_decoded (ids recordsList outputsList : Constructors)
    (program : Program) (buffers : Ash.NetworkLedger.CoreIncrement.Buffers)
    (checkedResult : CheckedSuccessFields program buffers)
    (first second third fourth workNode replacementNode updateNode outputNode : NodeId)
    (workName replacementName remainingName outgoingName : Binder)
    (recordTag openTag workOutTag parentTag : Constructor)
    (env : Environment) (start finish : Store) (result wanted parent destination bytes : Value)
    (owner : Nat) (counter : Int) (wantedId : Id) (key : Value → Id)
    (children records outputs : List Value)
    (firstShape : program first = some (.bind workName workNode second))
    (secondShape : program second = some (.bind replacementName replacementNode third))
    (thirdShape : program third = some (.bind remainingName updateNode fourth))
    (fourthShape : program fourth = some (.bind outgoingName outputNode checkedResult.root))
    (nonnegative : 0 ≤ counter) (bounded : BoundedLocations start)
    (workFunction workArgument workOwnerNode workCounterNode workOperand : NodeId)
    (workOwnerName : Binder)
    (workClosure : CheckedClosure program workFunction)
    (workPair : CheckedTuple program workArgument none [workOwnerNode, workCounterNode])
    (workConstructor : CheckedTuple program workClosure.body (some ids.work) [workOperand])
    (workCallShape : program workNode = some (.apply workFunction workArgument))
    (workOwnerShape : program workOwnerNode = some (.variable workOwnerName))
    (workCounterShape : program workCounterNode = some (.variable checkedResult.increment.counterBinder))
    (workOwnerFresh : workOwnerName ≠ workPair.contextBinder)
    (workCounterFresh : checkedResult.increment.counterBinder ≠ workPair.contextBinder)
    (workOwnerBinding : CoreEval.lookup env workOwnerName = some (.integer (Int.ofNat owner)))
    (workOperandShape : program workOperand = some (.variable workClosure.parameter))
    (workOperandFresh : workClosure.parameter ≠ workConstructor.contextBinder)
    (childChecked : Ash.NetworkLedger.CoreInsert.CheckedInsert ids program)
    (replacementFunction replacementArgument replacementWantedNode replacementParentNode replacementOpenNode
      childAppendNode replacementOperand childFunction childArgument childCall childListNode childConstructorFunction childConstructorArgument
      childIdNode childDestinationNode childOperand : NodeId)
    (replacementWantedName replacementParentName childCallName childListName childIdName childDestinationName : Binder)
    (childSelfAddress childSelfResolved : Nat) (childCaptureValues : List Value) (childCaptureEnv : Environment)
    (replacementClosure : CheckedClosure program replacementFunction)
    (replacementConstructor : CheckedTuple program replacementClosure.body (some recordTag) [replacementOperand])
    (replacementTuple : CheckedTuple program replacementArgument none
      [replacementWantedNode, replacementParentNode, replacementOpenNode, childAppendNode])
    (replacementOpenTuple : CheckedTuple program replacementOpenNode (some openTag) [])
    (childOuterPair : CheckedTuple program childArgument none [childCall, childListNode])
    (childClosure : CheckedClosure program childConstructorFunction)
    (childPair : CheckedTuple program childConstructorArgument none [childIdNode, childDestinationNode])
    (childConstructor : CheckedTuple program childClosure.body (some ids.child) [childOperand])
    (replacementCallShape : program replacementNode = some (.apply replacementFunction replacementArgument))
    (replacementOperandShape : program replacementOperand = some (.variable replacementClosure.parameter))
    (replacementOperandFresh : replacementClosure.parameter ≠ replacementConstructor.contextBinder)
    (replacementWantedShape : program replacementWantedNode = some (.variable replacementWantedName))
    (replacementParentShape : program replacementParentNode = some (.variable replacementParentName))
    (replacementWantedFresh : replacementWantedName ≠ replacementTuple.contextBinder)
    (replacementParentFresh : replacementParentName ≠ replacementTuple.contextBinder)
    (childAppendShape : program childAppendNode = some (.apply childFunction childArgument))
    (childFunctionShape : program childFunction = some (.variable childCallName))
    (childListShape : program childListNode = some (.variable childListName))
    (childListFresh : childListName ≠ childOuterPair.contextBinder)
    (childCallShape : program childCall = some (.apply childConstructorFunction childConstructorArgument))
    (childIdShape : program childIdNode = some (.variable childIdName))
    (childDestinationShape : program childDestinationNode = some (.variable childDestinationName))
    (childIdOuterFresh : childIdName ≠ childOuterPair.contextBinder)
    (childDestinationOuterFresh : childDestinationName ≠ childOuterPair.contextBinder)
    (childIdFresh : childIdName ≠ childPair.contextBinder)
    (childDestinationFresh : childDestinationName ≠ childPair.contextBinder)
    (childOperandShape : program childOperand = some (.variable childClosure.parameter))
    (childOperandFresh : childClosure.parameter ≠ childConstructor.contextBinder)
    (childList : Value)
    (replacementBindings : ∀ work,
      let replacementEnv := extend env workName work
      CoreEval.lookup replacementEnv replacementWantedName = some wanted ∧
      CoreEval.lookup replacementEnv replacementParentName = some parent)
    (childBindings : ∀ work,
      let appendEnv := extend (extend env workName work) replacementTuple.contextBinder .context
      CoreEval.lookup appendEnv childCallName = some (.location childSelfAddress) ∧
      CoreEval.lookup appendEnv childListName = some childList ∧
      CoreEval.lookup appendEnv childIdName = some work ∧
      CoreEval.lookup appendEnv childDestinationName = some destination)
    (childSelfBinding : CoreEval.lookup childCaptureEnv.reverse childChecked.functionName = some (.location childSelfAddress))
    (childCaptureBindings : CaptureBindings program childChecked.captureNodes childCaptureValues childCaptureEnv)
    (childSelfResolution : Resolve start childSelfAddress childSelfResolved)
    (childSelfCell : readCell start childSelfResolved = some (.closureCode childChecked.code :: childCaptureValues))
    (childListRep : Children ids start childList children)
    (childLocated : Ash.NetworkLedger.CoreGenericInsert.LocatedEntries children)
    (updateChecked : Ash.NetworkLedger.CoreRecordUpdate.CheckedRecordUpdate recordsList program)
    (updateProjection : RecordProjectionShape program updateChecked.projection)
    (updateProjectionName : updateProjection.functionName = updateChecked.projectionName)
    (updateEntryName : updateProjection.recordName = updateChecked.entryName)
    (updateProjectionCode : updateProjection.code = updateChecked.projectionCode)
    (updateFunction updateArgument updateWantedNode updateReplacementNode updateListNode : NodeId)
    (updateCallName updateWantedName updateReplacementName updateListName : Binder)
    (updateSelfAddress updateSelfResolved updateComparisonAddress updateComparisonResolved
      updateProjectionAddress updateProjectionResolved : Nat)
    (updateCaptureValues : List Value) (updateCaptureEnv : Environment)
    (updateTriple : CheckedTuple program updateArgument none [updateWantedNode, updateReplacementNode, updateListNode])
    (updateCallShape : program updateNode = some (.apply updateFunction updateArgument))
    (updateFunctionShape : program updateFunction = some (.variable updateCallName))
    (updateWantedShape : program updateWantedNode = some (.variable updateWantedName))
    (updateReplacementShape : program updateReplacementNode = some (.variable updateReplacementName))
    (updateListShape : program updateListNode = some (.variable updateListName))
    (updateWantedFresh : updateWantedName ≠ updateTriple.contextBinder)
    (updateReplacementFresh : updateReplacementName ≠ updateTriple.contextBinder)
    (updateListFresh : updateListName ≠ updateTriple.contextBinder)
    (updateList : Value)
    (updateBindings : ∀ work replacement,
      let updateEnv := extend (extend env workName work) replacementName replacement
      CoreEval.lookup updateEnv updateCallName = some (.location updateSelfAddress) ∧
      CoreEval.lookup updateEnv updateWantedName = some wanted ∧
      CoreEval.lookup updateEnv updateReplacementName = some replacement ∧
      CoreEval.lookup updateEnv updateListName = some updateList)
    (updateSelfBinding : CoreEval.lookup updateCaptureEnv.reverse updateChecked.functionName = some (.location updateSelfAddress))
    (updateComparisonBinding : CoreEval.lookup updateCaptureEnv.reverse updateChecked.comparisonName = some (.location updateComparisonAddress))
    (updateProjectionBinding : CoreEval.lookup updateCaptureEnv.reverse updateChecked.projectionName = some (.location updateProjectionAddress))
    (updateCaptureBindings : CaptureBindings program updateChecked.captureNodes updateCaptureValues updateCaptureEnv)
    (updateSelfResolution : Resolve start updateSelfAddress updateSelfResolved)
    (updateSelfCell : readCell start updateSelfResolved = some (.closureCode updateChecked.code :: updateCaptureValues))
    (updateComparisonResolution : Resolve start updateComparisonAddress updateComparisonResolved)
    (updateComparisonCell : readCell start updateComparisonResolved = some [.closureCode updateChecked.comparator.code])
    (updateProjectionResolution : Resolve start updateProjectionAddress updateProjectionResolved)
    (updateProjectionCell : readCell start updateProjectionResolved = some [.closureCode updateChecked.projectionCode])
    (updateWantedRep : Ident recordsList start wanted wantedId)
    (updateListRep : Children recordsList start updateList records)
    (updateKeys : RepresentedEntries recordsList (RecordEntry updateProjection.record) start key records)
    (outputChecked : Ash.NetworkLedger.CoreInsert.CheckedInsert outputsList program)
    (outputFunction outputArgument outputCall outputListNode outputConstructorFunction outputConstructorArgument
      outputChildNode outputParentCall outputDestinationNode outputPayloadNode outputParentFunction outputParentArguments
      outputOwnerNode outputWantedNode outputParentOperand outputOperand : NodeId)
    (outputCallName outputListName outputChildName outputOwnerName outputWantedName outputDestinationName outputBytesName : Binder)
    (outputSelfAddress outputSelfResolved : Nat) (outputCaptureValues : List Value) (outputCaptureEnv : Environment)
    (outputOuterPair : CheckedTuple program outputArgument none [outputCall, outputListNode])
    (outputClosure : CheckedClosure program outputConstructorFunction)
    (outputConstructor : CheckedTuple program outputClosure.body (some workOutTag) [outputOperand])
    (outputTuple : CheckedTuple program outputConstructorArgument none [outputChildNode, outputParentCall, outputDestinationNode, outputPayloadNode])
    (outputParentClosure : CheckedClosure program outputParentFunction)
    (outputParentPair : CheckedTuple program outputParentArguments none [outputOwnerNode, outputWantedNode])
    (outputParentConstructor : CheckedTuple program outputParentClosure.body (some parentTag) [outputParentOperand])
    (outputCallShape : program outputNode = some (.apply outputFunction outputArgument))
    (outputFunctionShape : program outputFunction = some (.variable outputCallName))
    (outputListShape : program outputListNode = some (.variable outputListName))
    (outputListFresh : outputListName ≠ outputOuterPair.contextBinder)
    (outputShape : program outputCall = some (.apply outputConstructorFunction outputConstructorArgument))
    (outputOperandShape : program outputOperand = some (.variable outputClosure.parameter))
    (outputOperandFresh : outputClosure.parameter ≠ outputConstructor.contextBinder)
    (outputChildShape : program outputChildNode = some (.variable outputChildName))
    (outputParentShape : program outputParentCall = some (.apply outputParentFunction outputParentArguments))
    (outputOwnerShape : program outputOwnerNode = some (.variable outputOwnerName))
    (outputWantedShape : program outputWantedNode = some (.variable outputWantedName))
    (outputDestinationShape : program outputDestinationNode = some (.variable outputDestinationName))
    (outputBytesShape : program outputPayloadNode = some (.variable outputBytesName))
    (outputChildOuterFresh : outputChildName ≠ outputOuterPair.contextBinder)
    (outputOwnerOuterFresh : outputOwnerName ≠ outputOuterPair.contextBinder)
    (outputWantedOuterFresh : outputWantedName ≠ outputOuterPair.contextBinder)
    (outputDestinationOuterFresh : outputDestinationName ≠ outputOuterPair.contextBinder)
    (outputBytesOuterFresh : outputBytesName ≠ outputOuterPair.contextBinder)
    (outputChildFresh : outputChildName ≠ outputTuple.contextBinder)
    (outputOwnerFresh : outputOwnerName ≠ outputTuple.contextBinder)
    (outputWantedFresh : outputWantedName ≠ outputTuple.contextBinder)
    (outputDestinationFresh : outputDestinationName ≠ outputTuple.contextBinder)
    (outputBytesFresh : outputBytesName ≠ outputTuple.contextBinder)
    (outputOwnerParentFresh : outputOwnerName ≠ outputParentPair.contextBinder)
    (outputWantedParentFresh : outputWantedName ≠ outputParentPair.contextBinder)
    (outputParentOperandShape : program outputParentOperand = some (.variable outputParentClosure.parameter))
    (outputParentOperandFresh : outputParentClosure.parameter ≠ outputParentConstructor.contextBinder)
    (outputList : Value)
    (outputBindings : ∀ work replacement remaining,
      let outputEnv := extend (extend (extend env workName work) replacementName replacement) remainingName remaining
      CoreEval.lookup outputEnv outputCallName = some (.location outputSelfAddress) ∧
      CoreEval.lookup outputEnv outputListName = some outputList ∧
      CoreEval.lookup outputEnv outputChildName = some work ∧
      CoreEval.lookup outputEnv outputOwnerName = some (.integer (Int.ofNat owner)) ∧
      CoreEval.lookup outputEnv outputWantedName = some wanted ∧
      CoreEval.lookup outputEnv outputDestinationName = some destination ∧
      CoreEval.lookup outputEnv outputBytesName = some bytes)
    (outputSelfBinding : CoreEval.lookup outputCaptureEnv.reverse outputChecked.functionName = some (.location outputSelfAddress))
    (outputCaptureBindings : CaptureBindings program outputChecked.captureNodes outputCaptureValues outputCaptureEnv)
    (outputSelfResolution : Resolve start outputSelfAddress outputSelfResolved)
    (outputSelfCell : readCell start outputSelfResolved = some (.closureCode outputChecked.code :: outputCaptureValues))
    (outputListRep : Children outputsList start outputList outputs)
    (outputLocated : Ash.NetworkLedger.CoreGenericInsert.LocatedEntries outputs)
    (counterBinding : CoreEval.lookup env checkedResult.increment.counterBinder = some (.integer counter))
    (remainingBinder : checkedResult.remainingName = remainingName)
    (outgoingBinder : checkedResult.outgoingName = outgoingName)
    (childBinder : checkedResult.childName = workName)
    (counterWork : checkedResult.increment.counterBinder ≠ workName)
    (counterReplacement : checkedResult.increment.counterBinder ≠ replacementName)
    (counterRemaining : checkedResult.increment.counterBinder ≠ remainingName)
    (counterOutgoing : checkedResult.increment.counterBinder ≠ outgoingName)
    (workReplacement : workName ≠ replacementName) (workRemaining : workName ≠ remainingName)
    (workOutgoing : workName ≠ outgoingName) (remainingOutgoing : remainingName ≠ outgoingName)
    (evaluation : Eval program env first start result finish)
    (noParent closedTag ackOutTag rejectedTag : Constructor)
    (bytesRep : Value → List UInt8 → Prop) (ledger : Ledger) (found : Ash.NetworkLedger.Record)
    (destinationNat : Nat) (payload : List UInt8)
    (ownerEq : ledger.owner = owner) (counterEq : ledger.next = counter)
    (destinationEq : destination = .integer (Int.ofNat destinationNat))
    (rootSame : recordsList.root = ids.root) (workSame : recordsList.work = ids.work)
    (recordTagSame : updateProjection.record = recordTag)
    (semanticParent : DecodedParent ids noParent parentTag start parent found.parent)
    (semanticChildren : RelatedValues (DecodedChild ids start) children found.children)
    (semanticRecords : RelatedValues (DecodedRecord ids recordTag noParent parentTag openTag closedTag start) records ledger.records)
    (semanticOutputs : RelatedValues (DecodedOutput ids noParent parentTag workOutTag ackOutTag bytesRep start) outputs ledger.outputs)
    (bytesMeaning : bytesRep bytes payload)
    (lookupSemantic : Ash.NetworkLedger.lookup Ash.NetworkLedger.Record.id wantedId ledger.records = some found)
    (isOpen : found.phase = .open) :
    DecodedRegistrationResult ids recordsList outputsList checkedResult.ledgerTag recordTag noParent parentTag openTag closedTag
      workOutTag ackOutTag rejectedTag checkedResult.registeredTag bytesRep finish result
      (Ash.NetworkLedger.register ledger wantedId destinationNat payload) := by
  obtain ⟨work, replacement, remaining, outgoing, output, returnedLedger, status, statusAddress,
    workRep, replacementRep, recordListRep, outputRep, outputListRep, resultRep, ledgerFields,
    statusEq, statusResolution, statusCell, frame⟩ :=
    registration_commit_composed
      ids recordsList outputsList program buffers checkedResult first
      second third fourth workNode replacementNode updateNode outputNode
      workName replacementName remainingName outgoingName recordTag openTag workOutTag
      parentTag env start finish result wanted parent
      destination bytes owner counter wantedId key children
      records outputs firstShape secondShape thirdShape fourthShape nonnegative
      bounded workFunction workArgument workOwnerNode workCounterNode workOperand workOwnerName
      workClosure workPair workConstructor workCallShape workOwnerShape workCounterShape workOwnerFresh
      workCounterFresh workOwnerBinding workOperandShape workOperandFresh childChecked replacementFunction replacementArgument
      replacementWantedNode replacementParentNode replacementOpenNode childAppendNode replacementOperand childFunction childArgument
      childCall childListNode childConstructorFunction childConstructorArgument childIdNode childDestinationNode childOperand
      replacementWantedName replacementParentName childCallName childListName childIdName childDestinationName childSelfAddress
      childSelfResolved childCaptureValues childCaptureEnv replacementClosure replacementConstructor replacementTuple replacementOpenTuple
      childOuterPair childClosure childPair childConstructor replacementCallShape replacementOperandShape replacementOperandFresh
      replacementWantedShape replacementParentShape replacementWantedFresh replacementParentFresh childAppendShape childFunctionShape childListShape
      childListFresh childCallShape childIdShape childDestinationShape childIdOuterFresh childDestinationOuterFresh childIdFresh
      childDestinationFresh childOperandShape childOperandFresh childList replacementBindings childBindings childSelfBinding
      childCaptureBindings childSelfResolution childSelfCell childListRep childLocated updateChecked updateProjection
      updateProjectionName updateEntryName updateProjectionCode updateFunction updateArgument updateWantedNode updateReplacementNode
      updateListNode updateCallName updateWantedName updateReplacementName updateListName updateSelfAddress updateSelfResolved
      updateComparisonAddress updateComparisonResolved updateProjectionAddress updateProjectionResolved updateCaptureValues updateCaptureEnv updateTriple
      updateCallShape updateFunctionShape updateWantedShape updateReplacementShape updateListShape updateWantedFresh updateReplacementFresh
      updateListFresh updateList updateBindings updateSelfBinding updateComparisonBinding updateProjectionBinding updateCaptureBindings
      updateSelfResolution updateSelfCell updateComparisonResolution updateComparisonCell updateProjectionResolution updateProjectionCell updateWantedRep
      updateListRep updateKeys outputChecked outputFunction outputArgument outputCall outputListNode
      outputConstructorFunction outputConstructorArgument outputChildNode outputParentCall outputDestinationNode outputPayloadNode outputParentFunction
      outputParentArguments outputOwnerNode outputWantedNode outputParentOperand outputOperand outputCallName outputListName
      outputChildName outputOwnerName outputWantedName outputDestinationName outputBytesName outputSelfAddress outputSelfResolved
      outputCaptureValues outputCaptureEnv outputOuterPair outputClosure outputConstructor outputTuple outputParentClosure
      outputParentPair outputParentConstructor outputCallShape outputFunctionShape outputListShape outputListFresh outputShape
      outputOperandShape outputOperandFresh outputChildShape outputParentShape outputOwnerShape outputWantedShape outputDestinationShape
      outputBytesShape outputChildOuterFresh outputOwnerOuterFresh outputWantedOuterFresh outputDestinationOuterFresh outputBytesOuterFresh outputChildFresh
      outputOwnerFresh outputWantedFresh outputDestinationFresh outputBytesFresh outputOwnerParentFresh outputWantedParentFresh outputParentOperandShape
      outputParentOperandFresh outputList outputBindings outputSelfBinding outputCaptureBindings outputSelfResolution outputSelfCell
      outputListRep outputLocated counterBinding remainingBinder outgoingBinder childBinder counterWork
      counterReplacement counterRemaining counterOutgoing workReplacement workRemaining workOutgoing remainingOutgoing
      evaluation
  have wantedStart : Ident ids start wanted wantedId :=
    ident_same_tags recordsList ids start wanted wantedId rootSame workSame updateWantedRep
  have wantedFinish := ident_retained ids start finish wanted wantedId frame.1 frame.2.2 wantedStart
  have parentFinish := decoded_parent_retained ids noParent parentTag start finish parent found.parent frame.1 frame.2.2 semanticParent
  have childrenFinish := decoded_children_retained ids start finish children found.children frame.1 frame.2.2 semanticChildren
  have recordsFinish := related_values_preserved
    (DecodedRecord ids recordTag noParent parentTag openTag closedTag start)
    (DecodedRecord ids recordTag noParent parentTag openTag closedTag finish) records ledger.records semanticRecords
    (fun value semantic rep => decoded_record_retained ids recordTag noParent parentTag openTag closedTag
      start finish value semantic frame.1 frame.2.2 rep)
  have outputsFinish := related_values_preserved
    (DecodedOutput ids noParent parentTag workOutTag ackOutTag bytesRep start)
    (DecodedOutput ids noParent parentTag workOutTag ackOutTag bytesRep finish) outputs ledger.outputs semanticOutputs
    (fun value semantic rep => decoded_output_retained ids noParent parentTag workOutTag ackOutTag bytesRep
      start finish value semantic frame.1 frame.2.2 rep)
  have originalKeys : RepresentedEntries recordsList (RecordEntry recordTag) start key records := by
    simpa [recordTagSame] using updateKeys
  have finalKeys := represented_entries_retained recordsList (RecordEntry recordTag) start finish key records
    (record_entry_retained recordTag) frame.1 frame.2.2 originalKeys
  have keyCorrect := decoded_record_keys ids recordsList recordTag noParent parentTag openTag closedTag finish records key
    rootSame workSame finalKeys
  have workMeaning : Ident ids finish work (.work ledger.owner ledger.next) := by simpa [ownerEq, counterEq] using workRep
  have replacementMeaning : ReplacementEntry ids recordTag openTag finish replacement wanted parent work
      (.integer (Int.ofNat destinationNat)) children := by simpa [destinationEq] using replacementRep
  have ledgerMeaning : NominalFields checkedResult.ledgerTag finish returnedLedger
      [.integer (ledger.next + 1), remaining, outgoing] := by simpa [counterEq] using ledgerFields
  have outputMeaning : WorkOutEntry workOutTag parentTag finish output work (.integer (Int.ofNat ledger.owner))
      wanted (.integer (Int.ofNat destinationNat)) bytes := by simpa [ownerEq, destinationEq] using outputRep
  exact decoded_open_commit ids recordsList outputsList checkedResult.ledgerTag recordTag noParent parentTag openTag closedTag
    workOutTag ackOutTag rejectedTag checkedResult.registeredTag bytesRep finish result returnedLedger status remaining outgoing
    replacement output work wanted parent bytes statusAddress ledger wantedId destinationNat payload records outputs children key found
    resultRep ledgerMeaning statusEq statusResolution statusCell workMeaning wantedFinish parentFinish childrenFinish replacementMeaning
    recordListRep recordsFinish keyCorrect outputMeaning outputListRep outputsFinish bytesMeaning lookupSemantic isOpen

/-- A real finite lookup hit identifies its corresponding semantic Record. -/
theorem related_lookup_hit {A : Type} (rel : Value → A → Prop)
    (keyValue : Value → Id) (keySemantic : A → Id) (wanted : Id)
    (values : List Value) (semantics : List A) (related : RelatedValues rel values semantics)
    (keys : ∀ value ∈ values, ∀ semantic, rel value semantic → keyValue value = keySemantic semantic)
    (found : Value) (actual : Ash.NetworkLedger.lookup keyValue wanted values = some found) :
    ∃ semantic, Ash.NetworkLedger.lookup keySemantic wanted semantics = some semantic ∧ rel found semantic := by
  have correspondence := related_values_lookup rel keyValue keySemantic wanted values semantics related keys
  rw [actual] at correspondence
  cases semanticResult : Ash.NetworkLedger.lookup keySemantic wanted semantics with
  | none => simp [semanticResult] at correspondence
  | some semantic => exact ⟨semantic, rfl, by simpa [semanticResult] using correspondence⟩

/-- A real finite lookup miss is also absent from the semantic Record sequence. -/
theorem related_lookup_miss {A : Type} (rel : Value → A → Prop)
    (keyValue : Value → Id) (keySemantic : A → Id) (wanted : Id)
    (values : List Value) (semantics : List A) (related : RelatedValues rel values semantics)
    (keys : ∀ value ∈ values, ∀ semantic, rel value semantic → keyValue value = keySemantic semantic)
    (actual : Ash.NetworkLedger.lookup keyValue wanted values = none) :
    Ash.NetworkLedger.lookup keySemantic wanted semantics = none := by
  have correspondence := related_values_lookup rel keyValue keySemantic wanted values semantics related keys
  rw [actual] at correspondence
  cases semanticResult : Ash.NetworkLedger.lookup keySemantic wanted semantics with
  | none => rfl
  | some semantic => simp [semanticResult] at correspondence

/-- A complete tuple of binder patterns produces the actual values in source order. -/
theorem binder_fields_match (store : Store) (names : List Binder) (values : List Value)
    (arity : names.length = values.length) {result : Option Environment}
    (attempts : FieldAttempts store (names.map Pattern.binder) values result) :
    result = some (List.zip names values) := by
  induction names generalizing values result with
  | nil =>
    cases values with
    | nil => cases attempts; rfl
    | cons value values => simp at arity
  | cons name names ih =>
    cases values with
    | nil => simp at arity
    | cons value values =>
      have tailArity : names.length = values.length := by simpa using arity
      cases attempts with
      | headMiss _ _ _ _ miss => cases miss
      | tailMiss _ _ _ _ bindings hit miss =>
        cases hit
        have impossible := ih values tailArity miss
        contradiction
      | hit _ _ _ _ first rest head tail =>
        cases head
        have same := ih values tailArity tail
        cases same
        rfl

/-- Matching a plain represented tuple of binders keeps every argument and its order. -/
theorem binder_tuple_match (store : Store) (names : List Binder) (values : List Value)
    (address resolved : Nat) (arity : names.length = values.length)
    (resolution : Resolve store address resolved) (cell : readCell store resolved = some values)
    (plain : tupleFields values = some values) {result : Option Environment}
    (attempt : Attempt store (.tuple (names.map Pattern.binder)) (.location address) result) :
    result = some (List.zip names values) := by
  cases attempt with
  | tupleNotLocation _ _ notLocation => exact False.elim (notLocation address rfl)
  | tupleWrongKind _ _ other stored otherResolution otherRead wrong =>
    have equal := resolved_fields_unique resolution otherResolution cell otherRead
    subst stored
    simp_all
  | tupleFields _ _ other stored actual found otherResolution otherRead view attempts =>
    have equal := resolved_fields_unique resolution otherResolution cell otherRead
    subst stored
    rw [plain] at view
    have valueEq := Option.some.inj view
    subst actual
    exact binder_fields_match store names values arity attempts

/-- Strict evaluation of variable-only argument fields preserves their order and store. -/
theorem checked_variable_fields (program : Program) (env : Environment)
    (nodes : List NodeId) (values : List Value) (start finish : Store) (fieldValue : NodeId → Value)
    (shapes : ∀ node ∈ nodes, ∃ name, program node = some (.variable name) ∧
      CoreEval.lookup env name = some (fieldValue node))
    (evaluation : EvalFields program env nodes start values finish) :
    values = nodes.map fieldValue ∧ finish = start := by
  induction nodes generalizing start finish values with
  | nil => cases evaluation; simp
  | cons node nodes ih =>
    cases evaluation with
    | cons head tail =>
      obtain ⟨name, shape, binding⟩ := shapes node (by simp)
      obtain ⟨actual, sameStore⟩ := variable_inversion shape head
      have sameValue : _ := Option.some.inj (actual.symm.trans binding)
      have tailShapes : ∀ node ∈ nodes, ∃ name, program node = some (.variable name) ∧
          CoreEval.lookup env name = some (fieldValue node) := by
        intro other member
        exact shapes other (by simp [member])
      obtain ⟨sameValues, tailStore⟩ := ih _ _ _ tailShapes tail
      simp [sameValue, sameValues, tailStore, sameStore]

/-- A checked variable-only tuple stores exactly its evaluated argument values. -/
theorem checked_variable_tuple (program : Program) (root : NodeId) (nodes : List NodeId)
    (env : Environment) (start finish : Store) (result : Value) (fieldValue : NodeId → Value)
    (tuple : CheckedTuple program root none nodes)
    (shapes : ∀ node ∈ nodes, ∃ name, program node = some (.variable name) ∧
      CoreEval.lookup (extend env tuple.contextBinder .context) name = some (fieldValue node))
    (bounded : BoundedLocations start) (evaluation : Eval program env root start result finish) :
    ∃ payload, result = .location payload ∧ Resolve finish payload payload ∧
      readCell finish payload = some (nodes.map fieldValue) ∧ CommitFrame start finish := by
  obtain ⟨queried, afterFields, afterAlloc, payload, values, queryStep, fieldEvals,
    allocated, initialized, resultEq⟩ := checked_tuple_inversion tuple evaluation
  obtain ⟨sameValues, sameStore⟩ := checked_variable_fields program _ nodes values queried afterFields fieldValue shapes fieldEvals
  subst values
  subst afterFields
  have alloc : allocate .hostDefault (nodes.map fieldValue).length true queried = some (payload, afterAlloc) := by
    simpa using allocated
  have init : initializeStorage payload (nodes.map fieldValue).length (nodes.map fieldValue) afterAlloc =
      some (nodes.map fieldValue, finish) := by simpa [storedFields] using initialized
  obtain ⟨fresh, _, cell, aliases, finalBound, retained⟩ := host_construct_retains bounded queryStep alloc init
  have noAlias : readAlias finish payload = none := by
    simpa [readAlias, aliases, fresh] using bounded_fresh_no_alias start bounded
  exact ⟨payload, resultEq, Resolve.cell payload _ noAlias cell, cell, aliases, finalBound, retained⟩

/-- A checked stored helper call evaluates its exact forwarded tuple and enters that closure. -/
theorem checked_forward_call (program : Program) (call function argument : NodeId)
    (nodes : List NodeId) (env : Environment) (start finish : Store) (result : Value)
    (functionName : Binder) (address resolved code context storage parameter body : Nat)
    (captureNodes : List NodeId) (captureValues : List Value) (captureEnv : Environment)
    (fieldValue : NodeId → Value) (tuple : CheckedTuple program argument none nodes)
    (callShape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable functionName))
    (functionBinding : CoreEval.lookup env functionName = some (.location address))
    (resolution : Resolve start address resolved)
    (cell : readCell start resolved = some (.closureCode code :: captureValues))
    (closureShape : program code = some (.closure context captureNodes storage parameter body))
    (captureBindings : CaptureBindings program captureNodes captureValues captureEnv)
    (fieldShapes : ∀ node ∈ nodes, ∃ name, program node = some (.variable name) ∧
      CoreEval.lookup (extend env tuple.contextBinder .context) name = some (fieldValue node))
    (bounded : BoundedLocations start) (evaluation : Eval program env call start result finish) :
    ∃ afterArgument payload, Resolve afterArgument payload payload ∧
      readCell afterArgument payload = some (nodes.map fieldValue) ∧ CommitFrame start afterArgument ∧
      Eval program (extend captureEnv.reverse parameter (.location payload)) body afterArgument result finish := by
  obtain ⟨afterFunction, afterArgument, callable, argumentValue, actualParameter, actualBody, captured,
    functionEval, target, argumentEval, bodyEval⟩ := apply_inversion callShape evaluation
  obtain ⟨actualFunction, functionState⟩ := variable_inversion functionShape functionEval
  have sameFunction : callable = .location address := by simpa [functionBinding] using actualFunction.symm
  subst callable
  subst afterFunction
  obtain ⟨sameParameter, sameBody, sameCapture⟩ :=
    captured_target program start address resolved code context storage parameter body captureNodes captureValues captureEnv
      resolution cell closureShape captureBindings target
  subst actualParameter
  subst actualBody
  subst captured
  obtain ⟨payload, sameArgument, payloadResolution, payloadCell, frame⟩ :=
    checked_variable_tuple program argument nodes env start afterArgument argumentValue fieldValue tuple fieldShapes bounded argumentEval
  subst argumentValue
  exact ⟨afterArgument, payload, payloadResolution, payloadCell, frame, bodyEval⟩

/-- The sole checked tuple arm opens the exact forwarded values in order. -/
theorem checked_forwarded_match (program : Program) (node scrutinee body : NodeId)
    (parameter : Binder) (names : List Binder) (values : List Value) (env : Environment)
    (start finish : Store) (result : Value) (payload resolved : Nat)
    (shape : program node = some (.caseMatch scrutinee [(.tuple (names.map Pattern.binder), body)]))
    (scrutineeShape : program scrutinee = some (.variable parameter))
    (binding : CoreEval.lookup env parameter = some (.location payload))
    (arity : names.length = values.length) (resolution : Resolve start payload resolved)
    (cell : readCell start resolved = some values) (plain : tupleFields values = some values)
    (evaluation : Eval program env node start result finish) :
    Eval program ((List.zip names values).reverse ++ env) body start result finish := by
  obtain ⟨middle, value, chosen, bindings, scrutineeEval, selected, bodyEval⟩ :=
    case_match_inversion shape evaluation
  obtain ⟨actual, sameStore⟩ := variable_inversion scrutineeShape scrutineeEval
  have sameValue : value = .location payload := by simpa [binding] using actual.symm
  subst value
  subst middle
  cases selected with
  | first _ _ _ _ hit =>
    have sameBindings := binder_tuple_match start names values payload resolved arity resolution cell plain hit
    cases sameBindings
    exact bodyEval
  | later _ _ _ _ _ _ impossible => cases impossible

/-- A checked nominal tuple pattern opens the exact stored payload fields. -/
theorem nominal_binder_fields_match (store : Store) (tag : Constructor)
    (address resolved payload tuple : Nat) (names : List Binder) (values : List Value)
    (arity : names.length = values.length) (resolution : Resolve store address resolved)
    (cell : readCell store resolved = some [.tag tag, .location payload])
    (payloadResolution : Resolve store payload tuple) (fields : readCell store tuple = some values)
    (plain : tupleFields values = some values) {result : Option Environment}
    (attempt : Attempt store (.constructor tag (some (.tuple (names.map Pattern.binder))))
      (.location address) result) : result = some (List.zip names values) := by
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
    exact binder_tuple_match store names values payload tuple arity payloadResolution fields plain inner
  | constructorMissingPayload _ _ _ other stored otherResolution otherRead view =>
    have equal := resolved_fields_unique resolution otherResolution cell otherRead
    subst stored
    simp [constructorFields] at view

/-- A sole nominal arm exposes precisely the checked original stored fields. -/
theorem checked_nominal_match (program : Program) (node scrutinee body : NodeId) (name : Binder)
    (tag : Constructor) (names : List Binder) (values : List Value) (env : Environment)
    (start finish : Store) (result value : Value)
    (shape : program node = some (.caseMatch scrutinee
      [(.constructor tag (some (.tuple (names.map Pattern.binder))), body)]))
    (scrutineeShape : program scrutinee = some (.variable name))
    (binding : CoreEval.lookup env name = some value) (arity : names.length = values.length)
    (representation : NominalFields tag start value values) (plain : tupleFields values = some values)
    (evaluation : Eval program env node start result finish) :
    Eval program ((List.zip names values).reverse ++ env) body start result finish := by
  obtain ⟨address, resolved, payload, tuple, same, resolution, cell, payloadResolution, fields⟩ := representation
  obtain ⟨middle, actualValue, chosen, bindings, scrutineeEval, selected, bodyEval⟩ :=
    case_match_inversion shape evaluation
  obtain ⟨actualBinding, sameStore⟩ := variable_inversion scrutineeShape scrutineeEval
  have actualEq : actualValue = .location address := by simpa [binding, same] using actualBinding.symm
  subst actualValue
  subst middle
  cases selected with
  | first _ _ _ _ hit =>
    have sameBindings := nominal_binder_fields_match start tag address resolved payload tuple names values arity
      resolution cell payloadResolution fields plain hit
    cases sameBindings
    exact bodyEval
  | later _ _ _ _ _ _ impossible => cases impossible

/-- The actual stored call forwards its checked tuple into its single binder-pattern arm. -/
theorem checked_forwarded_body (program : Program) (call function argument : NodeId)
    (nodes : List NodeId) (env : Environment) (start finish : Store) (result : Value)
    (functionName : Binder) (address resolved code context storage parameter body : Nat)
    (captureNodes : List NodeId) (captureValues : List Value) (captureEnv : Environment)
    (fieldValue : NodeId → Value) (tuple : CheckedTuple program argument none nodes)
    (callShape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable functionName))
    (functionBinding : CoreEval.lookup env functionName = some (.location address))
    (resolution : Resolve start address resolved)
    (cell : readCell start resolved = some (.closureCode code :: captureValues))
    (closureShape : program code = some (.closure context captureNodes storage parameter body))
    (captureBindings : CaptureBindings program captureNodes captureValues captureEnv)
    (fieldShapes : ∀ node ∈ nodes, ∃ name, program node = some (.variable name) ∧
      CoreEval.lookup (extend env tuple.contextBinder .context) name = some (fieldValue node))
    (scrutinee arm : NodeId) (names : List Binder)
    (bodyShape : program body = some (.caseMatch scrutinee [(.tuple (names.map Pattern.binder), arm)]))
    (scrutineeShape : program scrutinee = some (.variable parameter))
    (arity : names.length = (nodes.map fieldValue).length)
    (plain : tupleFields (nodes.map fieldValue) = some (nodes.map fieldValue))
    (bounded : BoundedLocations start) (evaluation : Eval program env call start result finish) :
    ∃ afterArgument payload, CommitFrame start afterArgument ∧
      Eval program ((List.zip names (nodes.map fieldValue)).reverse ++
        extend captureEnv.reverse parameter (.location payload)) arm afterArgument result finish := by
  obtain ⟨afterArgument, payload, payloadResolution, payloadCell, frame, bodyEval⟩ :=
    checked_forward_call program call function argument nodes env start finish result functionName address resolved code context storage
      parameter body captureNodes captureValues captureEnv fieldValue tuple callShape functionShape functionBinding resolution cell closureShape
      captureBindings fieldShapes bounded evaluation
  have parameterBinding : CoreEval.lookup (extend captureEnv.reverse parameter (.location payload)) parameter =
      some (.location payload) := by simp [CoreEval.lookup, extend]
  refine ⟨afterArgument, payload, frame, ?_⟩
  exact checked_forwarded_match program body scrutinee arm parameter names (nodes.map fieldValue)
    (extend captureEnv.reverse parameter (.location payload)) afterArgument finish result payload payload bodyShape scrutineeShape
    parameterBinding arity payloadResolution payloadCell plain bodyEval

/-- Retaining the original cells and aliases preserves the whole decoded Ledger. -/
theorem decoded_ledger_retained (ids recordsList outputsList : Constructors)
    (ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag : Constructor)
    (bytesRep : Value → List UInt8 → Prop) (before after : Store) (value : Value) (ledger : Ledger)
    (aliases : after.aliases = before.aliases)
    (cells : ∀ address old, readCell before address = some old → readCell after address = some old)
    (rep : DecodedLedger ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag
      bytesRep before value ledger) :
    DecodedLedger ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag
      bytesRep after value ledger := by
  obtain ⟨recordList, outputList, records, outputs, nominal, recordSpine, recordValues, outputSpine, outputValues⟩ := rep
  exact ⟨recordList, outputList, records, outputs, nominal_fields_retained ledgerTag before after value _ aliases cells nominal,
    children_retained recordsList before after recordList records aliases cells recordSpine,
    related_values_preserved (DecodedRecord ids recordTag noParent parentTag openTag closedTag before)
      (DecodedRecord ids recordTag noParent parentTag openTag closedTag after) records ledger.records recordValues
      (fun value semantic rep => decoded_record_retained ids recordTag noParent parentTag openTag closedTag
        before after value semantic aliases cells rep),
    children_retained outputsList before after outputList outputs aliases cells outputSpine,
    related_values_preserved (DecodedOutput ids noParent parentTag workOutTag ackOutTag bytesRep before)
      (DecodedOutput ids noParent parentTag workOutTag ackOutTag bytesRep after) outputs ledger.outputs outputValues
      (fun value semantic rep => decoded_output_retained ids noParent parentTag workOutTag ackOutTag bytesRep
        before after value semantic aliases cells rep)⟩

/-- A real rejecting return preserves the decoded input Ledger and status. -/
theorem decoded_rejected_result (ids recordsList outputsList : Constructors)
    (ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag rejectedTag registeredTag : Constructor)
    (bytesRep : Value → List UInt8 → Prop) (start finish : Store) (result ledgerValue : Value) (ledger : Ledger)
    (statusAddress : Nat) (resultRep : Result finish result ledgerValue (.location statusAddress))
    (statusResolution : Resolve finish statusAddress statusAddress)
    (statusCell : readCell finish statusAddress = some [.tag rejectedTag])
    (frame : CommitFrame start finish)
    (ledgerRep : DecodedLedger ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag
      bytesRep start ledgerValue ledger) :
    DecodedRegistrationResult ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag
      rejectedTag registeredTag bytesRep finish result (ledger, .rejected) := by
  exact ⟨ledgerValue, .location statusAddress, resultRep,
    decoded_ledger_retained ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag
      bytesRep start finish ledgerValue ledger frame.1 frame.2.2 ledgerRep,
    statusAddress, statusAddress, rfl, statusResolution, statusCell⟩

/-- The actual missing branch decodes to registration's rejected result. -/
theorem registration_missing_decoded (ids recordsList outputsList : Constructors)
    (ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag rejectedTag registeredTag absent present : Constructor)
    (bytesRep : Value → List UInt8 → Prop) (program : Program)
    (branch call missingBody foundBody ledgerNode statusNode : NodeId) (name ledgerName : Binder)
    (env : Environment) (start finish : Store) (result ledgerValue : Value) (ledger : Ledger)
    (wanted : Id) (destination : Nat) (payload : List UInt8) (records : List Value) (key : Value → Id)
    (branchShape : program branch = some (.caseMatch call
      [(.constructor absent none, missingBody), (.constructor present (some (.binder name)), foundBody)]))
    (lookupLaw : ∀ middle value, Eval program env call start value middle → LookupOutcome absent present start middle value none)
    (pair : CheckedTuple program missingBody none [ledgerNode, statusNode])
    (status : CheckedTuple program statusNode (some rejectedTag) [])
    (ledgerShape : program ledgerNode = some (.variable ledgerName)) (ledgerFresh : ledgerName ≠ pair.contextBinder)
    (ledgerBinding : CoreEval.lookup env ledgerName = some ledgerValue)
    (actualLookup : Ash.NetworkLedger.lookup key wanted records = none)
    (recordsRep : RelatedValues (DecodedRecord ids recordTag noParent parentTag openTag closedTag start) records ledger.records)
    (keys : ∀ value ∈ records, ∀ semantic, DecodedRecord ids recordTag noParent parentTag openTag closedTag start value semantic →
      key value = semantic.id)
    (ledgerRep : DecodedLedger ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag
      bytesRep start ledgerValue ledger) (evaluation : Eval program env branch start result finish) :
    DecodedRegistrationResult ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag
      rejectedTag registeredTag bytesRep finish result (Ash.NetworkLedger.register ledger wanted destination payload) := by
  obtain ⟨statusAddress, resultRep, statusResolution, statusCell, _, aliases, finalBound, retained⟩ :=
    registration_missing_branch program absent present rejectedTag branch call missingBody foundBody ledgerNode statusNode name ledgerName
      env start finish result ledgerValue branchShape lookupLaw pair status ledgerShape ledgerFresh ledgerBinding evaluation
  have semanticLookup := related_lookup_miss (DecodedRecord ids recordTag noParent parentTag openTag closedTag start)
    key Ash.NetworkLedger.Record.id wanted records ledger.records recordsRep keys actualLookup
  have rejected := decoded_rejected_result ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag workOutTag
    ackOutTag rejectedTag registeredTag bytesRep start finish result ledgerValue ledger statusAddress resultRep statusResolution statusCell
    ⟨aliases, finalBound, retained⟩ ledgerRep
  simpa [Ash.NetworkLedger.register, semanticLookup] using rejected

/-- The actual Closed branch decodes to registration's rejected result. -/
theorem registration_closed_decoded (ids recordsList outputsList : Constructors)
    (ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag rejectedTag registeredTag : Constructor)
    (bytesRep : Value → List UInt8 → Prop) (program : Program)
    (branch phaseNode closedBody openBody ledgerNode statusNode : NodeId) (phaseName ledgerName : Binder)
    (env : Environment) (start finish : Store) (result ledgerValue : Value) (ledger : Ledger)
    (wanted : Id) (destination : Nat) (payload : List UInt8) (found : Ash.NetworkLedger.Record)
    (phaseAddress phaseResolved : Nat)
    (branchShape : program branch = some (.caseMatch phaseNode
      [(.constructor closedTag none, closedBody), (.constructor openTag none, openBody)]))
    (phaseShape : program phaseNode = some (.variable phaseName))
    (phaseBinding : CoreEval.lookup env phaseName = some (.location phaseAddress))
    (phaseResolution : Resolve start phaseAddress phaseResolved)
    (phaseCell : readCell start phaseResolved = some [.tag closedTag])
    (pair : CheckedTuple program closedBody none [ledgerNode, statusNode])
    (status : CheckedTuple program statusNode (some rejectedTag) [])
    (ledgerShape : program ledgerNode = some (.variable ledgerName)) (ledgerFresh : ledgerName ≠ pair.contextBinder)
    (ledgerBinding : CoreEval.lookup env ledgerName = some ledgerValue) (bounded : BoundedLocations start)
    (ledgerRep : DecodedLedger ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag
      bytesRep start ledgerValue ledger)
    (lookupSemantic : Ash.NetworkLedger.lookup Ash.NetworkLedger.Record.id wanted ledger.records = some found)
    (isClosed : found.phase = .closed) (evaluation : Eval program env branch start result finish) :
    DecodedRegistrationResult ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag
      rejectedTag registeredTag bytesRep finish result (Ash.NetworkLedger.register ledger wanted destination payload) := by
  obtain ⟨statusAddress, resultRep, statusResolution, statusCell, _, aliases, finalBound, retained⟩ :=
    registration_closed_branch program closedTag openTag rejectedTag branch phaseNode closedBody openBody ledgerNode statusNode
      phaseName ledgerName env start finish result ledgerValue phaseAddress phaseResolved branchShape phaseShape phaseBinding
      phaseResolution phaseCell pair status ledgerShape ledgerFresh ledgerBinding bounded evaluation
  have rejected := decoded_rejected_result ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag workOutTag
    ackOutTag rejectedTag registeredTag bytesRep start finish result ledgerValue ledger statusAddress resultRep statusResolution statusCell
    ⟨aliases, finalBound, retained⟩ ledgerRep
  simpa [Ash.NetworkLedger.register, lookupSemantic, isClosed] using rejected

/-- An actual lookup hit and Open Record match expose the corresponding semantic Record. -/
theorem checked_open_lookup_decodes (ids recordsList : Constructors)
    (recordTag noParent parentTag openTag closedTag : Constructor) (store : Store)
    (records : List Value) (semanticRecords : List Ash.NetworkLedger.Record) (key : Value → Id) (wantedId : Id)
    (foundValue foundKey parent phase childList : Value) (phaseAddress phaseResolved : Nat)
    (rootSame : recordsList.root = ids.root) (workSame : recordsList.work = ids.work)
    (different : openTag ≠ closedTag)
    (represented : RepresentedEntries recordsList (RecordEntry recordTag) store key records)
    (recordValues : RelatedValues (DecodedRecord ids recordTag noParent parentTag openTag closedTag store) records semanticRecords)
    (actualLookup : Ash.NetworkLedger.lookup key wantedId records = some foundValue)
    (actualFields : NominalFields recordTag store foundValue [foundKey, parent, phase, childList])
    (phaseEq : phase = .location phaseAddress) (phaseResolution : Resolve store phaseAddress phaseResolved)
    (phaseCell : readCell store phaseResolved = some [.tag openTag]) :
    ∃ found entries, Ash.NetworkLedger.lookup Ash.NetworkLedger.Record.id wantedId semanticRecords = some found ∧
      found.phase = .open ∧ Ident ids store foundKey found.id ∧
      DecodedParent ids noParent parentTag store parent found.parent ∧ Children ids store childList entries ∧
      RelatedValues (DecodedChild ids store) entries found.children := by
  have keys := decoded_record_keys ids recordsList recordTag noParent parentTag openTag closedTag store records key
    rootSame workSame represented
  obtain ⟨found, lookupSemantic, foundRep⟩ := related_lookup_hit
    (DecodedRecord ids recordTag noParent parentTag openTag closedTag store) key Ash.NetworkLedger.Record.id wantedId
    records semanticRecords recordValues keys foundValue actualLookup
  obtain ⟨entries, keyRep, parentRep, phaseRep, childrenRep, childrenValues⟩ :=
    decoded_record_fields ids recordTag noParent parentTag openTag closedTag store foundValue foundKey parent phase childList found
      actualFields foundRep
  have isOpen := decoded_phase_open openTag closedTag store phase found.phase different phaseRep phaseAddress phaseResolved
    phaseEq phaseResolution phaseCell
  exact ⟨found, entries, lookupSemantic, isOpen, keyRep, parentRep, childrenRep, childrenValues⟩

/-- Distinct phase constructors make an actual Closed match semantically Closed. -/
theorem decoded_phase_closed (openTag closedTag : Constructor) (store : Store) (value : Value) (phase : Phase)
    (different : openTag ≠ closedTag) (decoded : DecodedPhase openTag closedTag store value phase)
    (address resolved : Nat) (same : value = .location address)
    (resolution : Resolve store address resolved) (cell : readCell store resolved = some [.tag closedTag]) :
    phase = .closed := by
  obtain ⟨otherAddress, otherResolved, otherEq, otherResolution, otherCell⟩ := decoded
  have addressEq : address = otherAddress := by simpa using same.symm.trans otherEq
  subst otherAddress
  have fields := resolved_fields_unique resolution otherResolution cell otherCell
  cases phase with
  | «open» =>
    simp at fields
    exact False.elim (different fields.symm)
  | closed => rfl

/-- An actual lookup hit and Closed Record match correspond to a semantic Closed Record. -/
theorem checked_closed_lookup_decodes (ids recordsList : Constructors)
    (recordTag noParent parentTag openTag closedTag : Constructor) (store : Store)
    (records : List Value) (semanticRecords : List Ash.NetworkLedger.Record) (key : Value → Id) (wantedId : Id)
    (foundValue foundKey parent phase childList : Value) (phaseAddress phaseResolved : Nat)
    (rootSame : recordsList.root = ids.root) (workSame : recordsList.work = ids.work)
    (different : openTag ≠ closedTag)
    (represented : RepresentedEntries recordsList (RecordEntry recordTag) store key records)
    (recordValues : RelatedValues (DecodedRecord ids recordTag noParent parentTag openTag closedTag store) records semanticRecords)
    (actualLookup : Ash.NetworkLedger.lookup key wantedId records = some foundValue)
    (actualFields : NominalFields recordTag store foundValue [foundKey, parent, phase, childList])
    (phaseEq : phase = .location phaseAddress) (phaseResolution : Resolve store phaseAddress phaseResolved)
    (phaseCell : readCell store phaseResolved = some [.tag closedTag]) :
    ∃ found, Ash.NetworkLedger.lookup Ash.NetworkLedger.Record.id wantedId semanticRecords = some found ∧ found.phase = .closed := by
  have keys := decoded_record_keys ids recordsList recordTag noParent parentTag openTag closedTag store records key
    rootSame workSame represented
  obtain ⟨found, lookupSemantic, foundRep⟩ := related_lookup_hit
    (DecodedRecord ids recordTag noParent parentTag openTag closedTag store) key Ash.NetworkLedger.Record.id wantedId
    records semanticRecords recordValues keys foundValue actualLookup
  obtain ⟨_, _, _, phaseRep, _, _⟩ :=
    decoded_record_fields ids recordTag noParent parentTag openTag closedTag store foundValue foundKey parent phase childList found
      actualFields foundRep
  exact ⟨found, lookupSemantic, decoded_phase_closed openTag closedTag store phase found.phase different phaseRep
    phaseAddress phaseResolved phaseEq phaseResolution phaseCell⟩

/-- The checked linked lookup and actual missing branch return the semantic rejection. -/
theorem registration_missing_checked (ids recordsList outputsList : Constructors)
    (ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag rejectedTag registeredTag absent present : Constructor)
    (bytesRep : Value → List UInt8 → Prop) (program : Program)
    (checked : CheckedLookupBase recordsList program absent present)
    (projection : RecordProjectionShape program checked.projection)
    (projectionFunctionName : projection.functionName = checked.projectionName)
    (projectionEntryName : projection.recordName = checked.entryName)
    (projectionCode : projection.code = checked.projectionCode)
    (projectionRecordTag : projection.record = recordTag)
    (branch call missingBody foundBody ledgerNode statusNode function argument wantedNode listNode : NodeId)
    (name ledgerName callName wantedName listName : Binder)
    (env : Environment) (start finish : Store) (result ledgerValue wantedValue list : Value) (ledger : Ledger)
    (wanted : Id) (destination : Nat) (payload : List UInt8) (records : List Value) (key : Value → Id)
    (selfAddress selfResolved comparisonAddress comparisonResolved projectionAddress projectionResolved : Nat)
    (captureValues : List Value) (captureEnv : Environment)
    (branchShape : program branch = some (.caseMatch call
      [(.constructor absent none, missingBody), (.constructor present (some (.binder name)), foundBody)]))
    (lookupPair : CheckedTuple program argument none [wantedNode, listNode])
    (callShape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable callName))
    (functionBinding : CoreEval.lookup env callName = some (.location selfAddress))
    (wantedShape : program wantedNode = some (.variable wantedName)) (listShape : program listNode = some (.variable listName))
    (wantedFresh : wantedName ≠ lookupPair.contextBinder) (listFresh : listName ≠ lookupPair.contextBinder)
    (wantedBinding : CoreEval.lookup env wantedName = some wantedValue) (listBinding : CoreEval.lookup env listName = some list)
    (selfBinding : CoreEval.lookup captureEnv.reverse checked.functionName = some (.location selfAddress))
    (comparisonBinding : CoreEval.lookup captureEnv.reverse checked.comparisonName = some (.location comparisonAddress))
    (projectionBinding : CoreEval.lookup captureEnv.reverse checked.projectionName = some (.location projectionAddress))
    (captureBindings : CaptureBindings program checked.captureNodes captureValues captureEnv)
    (selfResolution : Resolve start selfAddress selfResolved)
    (selfCell : readCell start selfResolved = some (.closureCode checked.code :: captureValues))
    (comparisonResolution : Resolve start comparisonAddress comparisonResolved)
    (comparisonCell : readCell start comparisonResolved = some [.closureCode checked.comparator.code])
    (projectionResolution : Resolve start projectionAddress projectionResolved)
    (projectionCell : readCell start projectionResolved = some [.closureCode checked.projectionCode])
    (bounded : BoundedLocations start) (wantedRep : Ident recordsList start wantedValue wanted)
    (listRep : Children recordsList start list records)
    (lookupKeys : RepresentedEntries recordsList (RecordEntry projection.record) start key records)
    (resultPair : CheckedTuple program missingBody none [ledgerNode, statusNode])
    (status : CheckedTuple program statusNode (some rejectedTag) [])
    (ledgerShape : program ledgerNode = some (.variable ledgerName)) (ledgerFresh : ledgerName ≠ resultPair.contextBinder)
    (ledgerBinding : CoreEval.lookup env ledgerName = some ledgerValue)
    (actualLookup : Ash.NetworkLedger.lookup key wanted records = none)
    (recordsRep : RelatedValues (DecodedRecord ids recordTag noParent parentTag openTag closedTag start) records ledger.records)
    (rootSame : recordsList.root = ids.root) (workSame : recordsList.work = ids.work)
    (ledgerRep : DecodedLedger ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag
      bytesRep start ledgerValue ledger) (evaluation : Eval program env branch start result finish) :
    DecodedRegistrationResult ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag
      rejectedTag registeredTag bytesRep finish result (Ash.NetworkLedger.register ledger wanted destination payload) := by
  have keysAtTag : RepresentedEntries recordsList (RecordEntry recordTag) start key records := by
    simpa [projectionRecordTag] using lookupKeys
  have semanticKeys := decoded_record_keys ids recordsList recordTag noParent parentTag openTag closedTag start records key
    rootSame workSame keysAtTag
  have lookupLaw : ∀ middle value, Eval program env call start value middle →
      LookupOutcome absent present start middle value none := by
    intro middle value callEval
    have lookup := checked_record_lookup_call recordsList program absent present checked projection projectionFunctionName
      projectionEntryName projectionCode call function argument wantedNode listNode env start middle value wantedValue list wanted key records
      callName wantedName listName selfAddress selfResolved comparisonAddress comparisonResolved projectionAddress projectionResolved
      captureValues captureEnv lookupPair callShape functionShape functionBinding wantedShape listShape wantedFresh listFresh wantedBinding
      listBinding selfBinding comparisonBinding projectionBinding captureBindings selfResolution selfCell comparisonResolution comparisonCell
      projectionResolution projectionCell bounded wantedRep listRep lookupKeys callEval
    simpa [actualLookup] using lookup
  exact registration_missing_decoded ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag workOutTag
    ackOutTag rejectedTag registeredTag absent present bytesRep program branch call missingBody foundBody ledgerNode statusNode name
    ledgerName env start finish result ledgerValue ledger wanted destination payload records key branchShape lookupLaw resultPair status
    ledgerShape ledgerFresh ledgerBinding actualLookup recordsRep semanticKeys ledgerRep evaluation

/-- A checked actual lookup hit and Closed branch yield the semantic rejection. -/
theorem registration_closed_checked (ids recordsList outputsList : Constructors)
    (ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag rejectedTag registeredTag : Constructor)
    (bytesRep : Value → List UInt8 → Prop) (program : Program)
    (branch phaseNode closedBody openBody ledgerNode statusNode : NodeId) (phaseName ledgerName : Binder)
    (env : Environment) (start finish : Store) (result ledgerValue foundValue foundKey parent phase childList : Value)
    (ledger : Ledger) (wanted : Id) (destination : Nat) (payload : List UInt8) (records : List Value) (key : Value → Id)
    (phaseAddress phaseResolved : Nat)
    (rootSame : recordsList.root = ids.root) (workSame : recordsList.work = ids.work) (different : openTag ≠ closedTag)
    (represented : RepresentedEntries recordsList (RecordEntry recordTag) start key records)
    (recordValues : RelatedValues (DecodedRecord ids recordTag noParent parentTag openTag closedTag start) records ledger.records)
    (actualLookup : Ash.NetworkLedger.lookup key wanted records = some foundValue)
    (actualFields : NominalFields recordTag start foundValue [foundKey, parent, phase, childList])
    (phaseEq : phase = .location phaseAddress)
    (branchShape : program branch = some (.caseMatch phaseNode
      [(.constructor closedTag none, closedBody), (.constructor openTag none, openBody)]))
    (phaseShape : program phaseNode = some (.variable phaseName))
    (phaseBinding : CoreEval.lookup env phaseName = some (.location phaseAddress))
    (phaseResolution : Resolve start phaseAddress phaseResolved)
    (phaseCell : readCell start phaseResolved = some [.tag closedTag])
    (pair : CheckedTuple program closedBody none [ledgerNode, statusNode])
    (status : CheckedTuple program statusNode (some rejectedTag) [])
    (ledgerShape : program ledgerNode = some (.variable ledgerName)) (ledgerFresh : ledgerName ≠ pair.contextBinder)
    (ledgerBinding : CoreEval.lookup env ledgerName = some ledgerValue) (bounded : BoundedLocations start)
    (ledgerRep : DecodedLedger ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag
      bytesRep start ledgerValue ledger) (evaluation : Eval program env branch start result finish) :
    DecodedRegistrationResult ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag
      rejectedTag registeredTag bytesRep finish result (Ash.NetworkLedger.register ledger wanted destination payload) := by
  obtain ⟨found, lookupSemantic, isClosed⟩ :=
    checked_closed_lookup_decodes ids recordsList recordTag noParent parentTag openTag closedTag start records ledger.records key wanted
      foundValue foundKey parent phase childList phaseAddress phaseResolved rootSame workSame different represented recordValues actualLookup
      actualFields phaseEq phaseResolution phaseCell
  exact registration_closed_decoded ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag
    rejectedTag registeredTag bytesRep program branch phaseNode closedBody openBody ledgerNode statusNode phaseName ledgerName env start finish
    result ledgerValue ledger wanted destination payload found phaseAddress phaseResolved branchShape phaseShape phaseBinding phaseResolution
    phaseCell pair status ledgerShape ledgerFresh ledgerBinding bounded ledgerRep lookupSemantic isClosed evaluation

/-- The actual finish call forwards its fields and matches the original whole Record. -/
theorem checked_finish_call (program : Program) (call function argument : NodeId)
    (nodes : List NodeId) (env : Environment) (start finish : Store) (result : Value)
    (functionName : Binder) (address resolved code context storage parameter body : Nat)
    (captureNodes : List NodeId) (captureValues : List Value) (captureEnv : Environment)
    (fieldValue : NodeId → Value) (tuple : CheckedTuple program argument none nodes)
    (callShape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable functionName))
    (functionBinding : CoreEval.lookup env functionName = some (.location address))
    (resolution : Resolve start address resolved)
    (cell : readCell start resolved = some (.closureCode code :: captureValues))
    (closureShape : program code = some (.closure context captureNodes storage parameter body))
    (captureBindings : CaptureBindings program captureNodes captureValues captureEnv)
    (fieldShapes : ∀ node ∈ nodes, ∃ name, program node = some (.variable name) ∧
      CoreEval.lookup (extend env tuple.contextBinder .context) name = some (fieldValue node))
    (scrutinee recordMatch recordScrutinee phaseBranch : NodeId) (names recordNames : List Binder)
    (recordName : Binder) (recordTag : Constructor) (record foundKey parent phase children : Value)
    (bodyShape : program body = some (.caseMatch scrutinee [(.tuple (names.map Pattern.binder), recordMatch)]))
    (scrutineeShape : program scrutinee = some (.variable parameter))
    (arity : names.length = (nodes.map fieldValue).length)
    (plain : tupleFields (nodes.map fieldValue) = some (nodes.map fieldValue))
    (recordShape : program recordMatch = some (.caseMatch recordScrutinee
      [(.constructor recordTag (some (.tuple (recordNames.map Pattern.binder))), phaseBranch)]))
    (recordScrutineeShape : program recordScrutinee = some (.variable recordName))
    (recordBinding : ∀ payload,
      CoreEval.lookup ((List.zip names (nodes.map fieldValue)).reverse ++
        extend captureEnv.reverse parameter (.location payload)) recordName = some record)
    (recordArity : recordNames.length = 4)
    (recordRep : NominalFields recordTag start record [foundKey, parent, phase, children])
    (recordPlain : tupleFields [foundKey, parent, phase, children] = some [foundKey, parent, phase, children])
    (bounded : BoundedLocations start) (evaluation : Eval program env call start result finish) :
    ∃ afterArgument payload, CommitFrame start afterArgument ∧
      Eval program ((List.zip recordNames [foundKey, parent, phase, children]).reverse ++
        ((List.zip names (nodes.map fieldValue)).reverse ++ extend captureEnv.reverse parameter (.location payload)))
        phaseBranch afterArgument result finish := by
  obtain ⟨afterArgument, payload, frame, recordEval⟩ :=
    checked_forwarded_body program call function argument nodes env start finish result functionName address resolved code context storage
      parameter body captureNodes captureValues captureEnv fieldValue tuple callShape functionShape functionBinding resolution cell closureShape
      captureBindings fieldShapes scrutinee recordMatch names bodyShape scrutineeShape arity plain bounded evaluation
  have retainedRecord := nominal_fields_retained recordTag start afterArgument record _ frame.1 frame.2.2 recordRep
  refine ⟨afterArgument, payload, frame, ?_⟩
  exact checked_nominal_match program recordMatch recordScrutinee phaseBranch recordName recordTag recordNames
    [foundKey, parent, phase, children] _ afterArgument finish result record recordShape recordScrutineeShape (recordBinding payload)
    (by simpa using recordArity) retainedRecord recordPlain recordEval

/-- The actual stored finish call and Closed phase return the decoded rejection. -/
theorem checked_finish_closed (ids recordsList outputsList : Constructors)
    (ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag rejectedTag registeredTag : Constructor)
    (bytesRep : Value → List UInt8 → Prop) (program : Program) (call function argument : NodeId)
    (nodes : List NodeId) (env : Environment) (start finish : Store) (result : Value)
    (functionName : Binder) (address resolved code context storage parameter body : Nat)
    (captureNodes : List NodeId) (captureValues : List Value) (captureEnv : Environment)
    (fieldValue : NodeId → Value) (tuple : CheckedTuple program argument none nodes)
    (callShape : program call = some (.apply function argument)) (functionShape : program function = some (.variable functionName))
    (functionBinding : CoreEval.lookup env functionName = some (.location address))
    (resolution : Resolve start address resolved) (cell : readCell start resolved = some (.closureCode code :: captureValues))
    (closureShape : program code = some (.closure context captureNodes storage parameter body))
    (captureBindings : CaptureBindings program captureNodes captureValues captureEnv)
    (fieldShapes : ∀ node ∈ nodes, ∃ name, program node = some (.variable name) ∧
      CoreEval.lookup (extend env tuple.contextBinder .context) name = some (fieldValue node))
    (scrutinee recordMatch recordScrutinee phaseBranch : NodeId) (names recordNames : List Binder) (recordName : Binder)
    (record foundKey parent phase childList ledgerValue : Value) (ledger : Ledger)
    (bodyShape : program body = some (.caseMatch scrutinee [(.tuple (names.map Pattern.binder), recordMatch)]))
    (scrutineeShape : program scrutinee = some (.variable parameter))
    (arity : names.length = (nodes.map fieldValue).length) (plain : tupleFields (nodes.map fieldValue) = some (nodes.map fieldValue))
    (recordShape : program recordMatch = some (.caseMatch recordScrutinee
      [(.constructor recordTag (some (.tuple (recordNames.map Pattern.binder))), phaseBranch)]))
    (recordScrutineeShape : program recordScrutinee = some (.variable recordName))
    (recordBinding : ∀ payload, CoreEval.lookup ((List.zip names (nodes.map fieldValue)).reverse ++
      extend captureEnv.reverse parameter (.location payload)) recordName = some record)
    (recordArity : recordNames.length = 4)
    (recordRep : NominalFields recordTag start record [foundKey, parent, phase, childList])
    (recordPlain : tupleFields [foundKey, parent, phase, childList] = some [foundKey, parent, phase, childList])
    (wanted : Id) (destination : Nat) (payloadBytes : List UInt8) (records : List Value) (key : Value → Id)
    (phaseAddress phaseResolved : Nat) (phaseEq : phase = .location phaseAddress)
    (phaseResolution : Resolve start phaseAddress phaseResolved) (phaseCell : readCell start phaseResolved = some [.tag closedTag])
    (rootSame : recordsList.root = ids.root) (workSame : recordsList.work = ids.work) (different : openTag ≠ closedTag)
    (represented : RepresentedEntries recordsList (RecordEntry recordTag) start key records)
    (recordValues : RelatedValues (DecodedRecord ids recordTag noParent parentTag openTag closedTag start) records ledger.records)
    (actualLookup : Ash.NetworkLedger.lookup key wanted records = some record)
    (phaseNode closedBody openBody ledgerNode statusNode : NodeId) (phaseName ledgerName : Binder)
    (phaseShape : program phaseBranch = some (.caseMatch phaseNode
      [(.constructor closedTag none, closedBody), (.constructor openTag none, openBody)]))
    (phaseNodeShape : program phaseNode = some (.variable phaseName))
    (phaseBinding : ∀ payload, CoreEval.lookup ((List.zip recordNames [foundKey, parent, phase, childList]).reverse ++
      ((List.zip names (nodes.map fieldValue)).reverse ++ extend captureEnv.reverse parameter (.location payload))) phaseName = some phase)
    (resultPair : CheckedTuple program closedBody none [ledgerNode, statusNode])
    (status : CheckedTuple program statusNode (some rejectedTag) [])
    (ledgerShape : program ledgerNode = some (.variable ledgerName)) (ledgerFresh : ledgerName ≠ resultPair.contextBinder)
    (ledgerBinding : ∀ payload, CoreEval.lookup ((List.zip recordNames [foundKey, parent, phase, childList]).reverse ++
      ((List.zip names (nodes.map fieldValue)).reverse ++ extend captureEnv.reverse parameter (.location payload))) ledgerName = some ledgerValue)
    (bounded : BoundedLocations start)
    (ledgerRep : DecodedLedger ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag
      bytesRep start ledgerValue ledger) (evaluation : Eval program env call start result finish) :
    DecodedRegistrationResult ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag
      rejectedTag registeredTag bytesRep finish result (Ash.NetworkLedger.register ledger wanted destination payloadBytes) := by
  obtain ⟨afterArgument, payload, frame, phaseEval⟩ := checked_finish_call program call function argument nodes env start finish result
    functionName address resolved code context storage parameter body captureNodes captureValues captureEnv fieldValue tuple callShape
    functionShape functionBinding resolution cell closureShape captureBindings fieldShapes scrutinee recordMatch recordScrutinee phaseBranch
    names recordNames recordName recordTag record foundKey parent phase childList bodyShape scrutineeShape arity plain recordShape
    recordScrutineeShape recordBinding recordArity recordRep recordPlain bounded evaluation
  have retainedRecord := nominal_fields_retained recordTag start afterArgument record _ frame.1 frame.2.2 recordRep
  have retainedKeys := represented_entries_retained recordsList (RecordEntry recordTag) start afterArgument key records
    (record_entry_retained recordTag) frame.1 frame.2.2 represented
  have retainedValues := related_values_preserved
    (DecodedRecord ids recordTag noParent parentTag openTag closedTag start)
    (DecodedRecord ids recordTag noParent parentTag openTag closedTag afterArgument) records ledger.records recordValues
    (fun value semantic rep => decoded_record_retained ids recordTag noParent parentTag openTag closedTag
      start afterArgument value semantic frame.1 frame.2.2 rep)
  have retainedLedger := decoded_ledger_retained ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag
    workOutTag ackOutTag bytesRep start afterArgument ledgerValue ledger frame.1 frame.2.2 ledgerRep
  exact registration_closed_checked ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag workOutTag
    ackOutTag rejectedTag registeredTag bytesRep program phaseBranch phaseNode closedBody openBody ledgerNode statusNode phaseName ledgerName
    _ afterArgument finish result ledgerValue record foundKey parent phase childList ledger wanted destination payloadBytes records key
    phaseAddress phaseResolved rootSame workSame different retainedKeys retainedValues actualLookup retainedRecord phaseEq phaseShape
    phaseNodeShape (by simpa [phaseEq] using phaseBinding payload) (resolve_preserved frame.1 frame.2.2 phaseResolution)
    (frame.2.2 phaseResolved _ phaseCell) resultPair status ledgerShape ledgerFresh (ledgerBinding payload) frame.2.1 retainedLedger phaseEval

/-- The actual finish and commit calls enter the checked open commit body. -/
theorem checked_finish_open_body (program : Program) (call function argument : NodeId)
    (nodes : List NodeId) (env : Environment) (start finish : Store) (result : Value)
    (functionName : Binder) (address resolved code context storage parameter body : Nat)
    (captureNodes : List NodeId) (captureValues : List Value) (captureEnv : Environment)
    (fieldValue : NodeId → Value) (tuple : CheckedTuple program argument none nodes)
    (callShape : program call = some (.apply function argument)) (functionShape : program function = some (.variable functionName))
    (functionBinding : CoreEval.lookup env functionName = some (.location address))
    (resolution : Resolve start address resolved) (cell : readCell start resolved = some (.closureCode code :: captureValues))
    (closureShape : program code = some (.closure context captureNodes storage parameter body))
    (captureBindings : CaptureBindings program captureNodes captureValues captureEnv)
    (fieldShapes : ∀ node ∈ nodes, ∃ name, program node = some (.variable name) ∧
      CoreEval.lookup (extend env tuple.contextBinder .context) name = some (fieldValue node))
    (scrutinee recordMatch recordScrutinee phaseBranch : NodeId) (names recordNames : List Binder) (recordName : Binder)
    (recordTag openTag closedTag : Constructor) (record foundKey parent phase children : Value)
    (bodyShape : program body = some (.caseMatch scrutinee [(.tuple (names.map Pattern.binder), recordMatch)]))
    (scrutineeShape : program scrutinee = some (.variable parameter))
    (arity : names.length = (nodes.map fieldValue).length) (plain : tupleFields (nodes.map fieldValue) = some (nodes.map fieldValue))
    (recordShape : program recordMatch = some (.caseMatch recordScrutinee
      [(.constructor recordTag (some (.tuple (recordNames.map Pattern.binder))), phaseBranch)]))
    (recordScrutineeShape : program recordScrutinee = some (.variable recordName))
    (recordBinding : ∀ payload, CoreEval.lookup ((List.zip names (nodes.map fieldValue)).reverse ++
      extend captureEnv.reverse parameter (.location payload)) recordName = some record)
    (recordArity : recordNames.length = 4)
    (recordRep : NominalFields recordTag start record [foundKey, parent, phase, children])
    (recordPlain : tupleFields [foundKey, parent, phase, children] = some [foundKey, parent, phase, children])
    (phaseAddress phaseResolved : Nat) (phaseEq : phase = .location phaseAddress)
    (phaseResolution : Resolve start phaseAddress phaseResolved) (phaseCell : readCell start phaseResolved = some [.tag openTag])
    (different : openTag ≠ closedTag) (phaseNode closedBody commitCall : NodeId) (phaseName : Binder)
    (phaseShape : program phaseBranch = some (.caseMatch phaseNode
      [(.constructor closedTag none, closedBody), (.constructor openTag none, commitCall)]))
    (phaseNodeShape : program phaseNode = some (.variable phaseName))
    (phaseBinding : ∀ payload, CoreEval.lookup ((List.zip recordNames [foundKey, parent, phase, children]).reverse ++
      ((List.zip names (nodes.map fieldValue)).reverse ++ extend captureEnv.reverse parameter (.location payload))) phaseName = some phase)
    (commitFunction commitArgument commitScrutinee commitArm : NodeId) (commitNodes : List NodeId)
    (commitName : Binder) (commitAddress commitResolved commitCode commitContext commitStorage commitParameter commitBody : Nat)
    (commitCaptureNodes : List NodeId) (commitCaptureValues : List Value) (commitCaptureEnv : Environment)
    (commitFieldValue : NodeId → Value) (commitTuple : CheckedTuple program commitArgument none commitNodes)
    (commitCallShape : program commitCall = some (.apply commitFunction commitArgument))
    (commitFunctionShape : program commitFunction = some (.variable commitName))
    (commitBinding : ∀ payload, CoreEval.lookup ((List.zip recordNames [foundKey, parent, phase, children]).reverse ++
      ((List.zip names (nodes.map fieldValue)).reverse ++ extend captureEnv.reverse parameter (.location payload))) commitName =
      some (.location commitAddress))
    (commitResolution : Resolve start commitAddress commitResolved)
    (commitCell : readCell start commitResolved = some (.closureCode commitCode :: commitCaptureValues))
    (commitClosureShape : program commitCode = some (.closure commitContext commitCaptureNodes commitStorage commitParameter commitBody))
    (commitCaptureBindings : CaptureBindings program commitCaptureNodes commitCaptureValues commitCaptureEnv)
    (commitFieldShapes : ∀ payload node, node ∈ commitNodes → ∃ name, program node = some (.variable name) ∧
      CoreEval.lookup (extend ((List.zip recordNames [foundKey, parent, phase, children]).reverse ++
        ((List.zip names (nodes.map fieldValue)).reverse ++ extend captureEnv.reverse parameter (.location payload)))
        commitTuple.contextBinder .context) name = some (commitFieldValue node))
    (commitNames : List Binder)
    (commitBodyShape : program commitBody = some (.caseMatch commitScrutinee [(.tuple (commitNames.map Pattern.binder), commitArm)]))
    (commitScrutineeShape : program commitScrutinee = some (.variable commitParameter))
    (commitArity : commitNames.length = (commitNodes.map commitFieldValue).length)
    (commitPlain : tupleFields (commitNodes.map commitFieldValue) = some (commitNodes.map commitFieldValue))
    (bounded : BoundedLocations start) (evaluation : Eval program env call start result finish) :
    ∃ (afterCommit : Store) (commitPayload : Nat), CommitFrame start afterCommit ∧
      Eval program ((List.zip commitNames (commitNodes.map commitFieldValue)).reverse ++
        extend commitCaptureEnv.reverse commitParameter (.location commitPayload)) commitArm afterCommit result finish := by
  obtain ⟨afterFinish, finishPayload, finishFrame, phaseEval⟩ := checked_finish_call program call function argument nodes env start finish result
    functionName address resolved code context storage parameter body captureNodes captureValues captureEnv fieldValue tuple callShape
    functionShape functionBinding resolution cell closureShape captureBindings fieldShapes scrutinee recordMatch recordScrutinee phaseBranch
    names recordNames recordName recordTag record foundKey parent phase children bodyShape scrutineeShape arity plain recordShape
    recordScrutineeShape recordBinding recordArity recordRep recordPlain bounded evaluation
  have commitEval := registration_open_branch program closedTag openTag phaseBranch phaseNode closedBody commitCall phaseName _
    afterFinish finish result phaseAddress phaseResolved different phaseShape phaseNodeShape
    (by simpa [phaseEq] using phaseBinding finishPayload) (resolve_preserved finishFrame.1 finishFrame.2.2 phaseResolution)
    (finishFrame.2.2 phaseResolved _ phaseCell) phaseEval
  obtain ⟨afterCommit, commitPayload, commitFrame, bodyEval⟩ := checked_forwarded_body program commitCall commitFunction commitArgument
    commitNodes _ afterFinish finish result commitName commitAddress commitResolved commitCode commitContext commitStorage commitParameter commitBody
    commitCaptureNodes commitCaptureValues commitCaptureEnv commitFieldValue commitTuple commitCallShape commitFunctionShape
    (commitBinding finishPayload) (resolve_preserved finishFrame.1 finishFrame.2.2 commitResolution)
    (finishFrame.2.2 commitResolved _ commitCell) commitClosureShape commitCaptureBindings (commitFieldShapes finishPayload)
    commitScrutinee commitArm commitNames commitBodyShape commitScrutineeShape commitArity commitPlain finishFrame.2.1 commitEval
  exact ⟨afterCommit, commitPayload, commit_frame_trans start afterFinish afterCommit finishFrame commitFrame, bodyEval⟩

/-- A finite represented spine has a unique sequence of whole values. -/
theorem children_sequence_unique (ids : Constructors) (store : Store) (value : Value)
    (left right : List Value) (first : Children ids store value left)
    (second : Children ids store value right) : left = right := by
  induction first generalizing right with
  | empty address resolved resolution cell =>
    cases second with
    | empty => rfl
    | more _ otherResolved _ _ _ _ _ otherResolution otherCell _ _ _ =>
      have equal := resolved_fields_unique resolution otherResolution cell otherCell
      simp at equal
  | more address resolved payload tuple head tail entries resolution cell payloadResolution fields remaining ih =>
    cases second with
    | empty _ otherResolved otherResolution otherCell =>
      have equal := resolved_fields_unique resolution otherResolution cell otherCell
      simp at equal
    | more _ otherResolved otherPayload otherTuple otherHead otherTail otherEntries otherResolution otherCell otherPayloadResolution otherFields otherRemaining =>
      have outer := resolved_fields_unique resolution otherResolution cell otherCell
      have payloadEq : payload = otherPayload := by simpa using outer
      subst otherPayload
      have inner := resolved_fields_unique payloadResolution otherPayloadResolution fields otherFields
      have headEq : head = otherHead := by simpa using congrArg List.head? inner
      have tailEq : tail = otherTail := by simpa using congrArg List.tail inner
      subst otherHead
      subst otherTail
      exact congrArg (List.cons head) (ih otherEntries otherRemaining)

/-- A checked open commit derives its semantic input from the actual lookup and matched Record. -/
theorem registration_commit_from_lookup
    (ids recordsList outputsList : Constructors)
    (program : Program)
    (buffers : Ash.NetworkLedger.CoreIncrement.Buffers)
    (checkedResult : CheckedSuccessFields program buffers)
    (first second third fourth workNode replacementNode updateNode outputNode : NodeId)
    (workName replacementName remainingName outgoingName : Binder)
    (recordTag openTag workOutTag parentTag : Constructor)
    (env : Environment)
    (start finish : Store)
    (result wanted parent destination bytes : Value)
    (owner : Nat)
    (counter : Int)
    (wantedId : Id)
    (key : Value → Id)
    (children records outputs : List Value)
    (firstShape : program first = some (.bind workName workNode second))
    (secondShape : program second = some (.bind replacementName replacementNode third))
    (thirdShape : program third = some (.bind remainingName updateNode fourth))
    (fourthShape : program fourth = some (.bind outgoingName outputNode checkedResult.root))
    (nonnegative : 0 ≤ counter)
    (bounded : BoundedLocations start)
    (workFunction workArgument workOwnerNode workCounterNode workOperand : NodeId)
    (workOwnerName : Binder)
    (workClosure : CheckedClosure program workFunction)
    (workPair : CheckedTuple program workArgument none [workOwnerNode, workCounterNode])
    (workConstructor : CheckedTuple program workClosure.body (some ids.work) [workOperand])
    (workCallShape : program workNode = some (.apply workFunction workArgument))
    (workOwnerShape : program workOwnerNode = some (.variable workOwnerName))
    (workCounterShape : program workCounterNode = some (.variable checkedResult.increment.counterBinder))
    (workOwnerFresh : workOwnerName ≠ workPair.contextBinder)
    (workCounterFresh : checkedResult.increment.counterBinder ≠ workPair.contextBinder)
    (workOwnerBinding : CoreEval.lookup env workOwnerName = some (.integer (Int.ofNat owner)))
    (workOperandShape : program workOperand = some (.variable workClosure.parameter))
    (workOperandFresh : workClosure.parameter ≠ workConstructor.contextBinder)
    (childChecked : Ash.NetworkLedger.CoreInsert.CheckedInsert ids program)
    (replacementFunction replacementArgument replacementWantedNode replacementParentNode replacementOpenNode
      childAppendNode replacementOperand childFunction childArgument childCall childListNode childConstructorFunction childConstructorArgument
      childIdNode childDestinationNode childOperand : NodeId)
    (replacementWantedName replacementParentName childCallName childListName childIdName childDestinationName : Binder)
    (childSelfAddress childSelfResolved : Nat)
    (childCaptureValues : List Value)
    (childCaptureEnv : Environment)
    (replacementClosure : CheckedClosure program replacementFunction)
    (replacementConstructor : CheckedTuple program replacementClosure.body (some recordTag) [replacementOperand])
    (replacementTuple : CheckedTuple program replacementArgument none
      [replacementWantedNode, replacementParentNode, replacementOpenNode, childAppendNode])
    (replacementOpenTuple : CheckedTuple program replacementOpenNode (some openTag) [])
    (childOuterPair : CheckedTuple program childArgument none [childCall, childListNode])
    (childClosure : CheckedClosure program childConstructorFunction)
    (childPair : CheckedTuple program childConstructorArgument none [childIdNode, childDestinationNode])
    (childConstructor : CheckedTuple program childClosure.body (some ids.child) [childOperand])
    (replacementCallShape : program replacementNode = some (.apply replacementFunction replacementArgument))
    (replacementOperandShape : program replacementOperand = some (.variable replacementClosure.parameter))
    (replacementOperandFresh : replacementClosure.parameter ≠ replacementConstructor.contextBinder)
    (replacementWantedShape : program replacementWantedNode = some (.variable replacementWantedName))
    (replacementParentShape : program replacementParentNode = some (.variable replacementParentName))
    (replacementWantedFresh : replacementWantedName ≠ replacementTuple.contextBinder)
    (replacementParentFresh : replacementParentName ≠ replacementTuple.contextBinder)
    (childAppendShape : program childAppendNode = some (.apply childFunction childArgument))
    (childFunctionShape : program childFunction = some (.variable childCallName))
    (childListShape : program childListNode = some (.variable childListName))
    (childListFresh : childListName ≠ childOuterPair.contextBinder)
    (childCallShape : program childCall = some (.apply childConstructorFunction childConstructorArgument))
    (childIdShape : program childIdNode = some (.variable childIdName))
    (childDestinationShape : program childDestinationNode = some (.variable childDestinationName))
    (childIdOuterFresh : childIdName ≠ childOuterPair.contextBinder)
    (childDestinationOuterFresh : childDestinationName ≠ childOuterPair.contextBinder)
    (childIdFresh : childIdName ≠ childPair.contextBinder)
    (childDestinationFresh : childDestinationName ≠ childPair.contextBinder)
    (childOperandShape : program childOperand = some (.variable childClosure.parameter))
    (childOperandFresh : childClosure.parameter ≠ childConstructor.contextBinder)
    (childList : Value)
    (replacementBindings : ∀ work,
      let replacementEnv := extend env workName work
      CoreEval.lookup replacementEnv replacementWantedName = some wanted ∧
      CoreEval.lookup replacementEnv replacementParentName = some parent)
    (childBindings : ∀ work,
      let appendEnv := extend (extend env workName work) replacementTuple.contextBinder .context
      CoreEval.lookup appendEnv childCallName = some (.location childSelfAddress) ∧
      CoreEval.lookup appendEnv childListName = some childList ∧
      CoreEval.lookup appendEnv childIdName = some work ∧
      CoreEval.lookup appendEnv childDestinationName = some destination)
    (childSelfBinding : CoreEval.lookup childCaptureEnv.reverse childChecked.functionName = some (.location childSelfAddress))
    (childCaptureBindings : CaptureBindings program childChecked.captureNodes childCaptureValues childCaptureEnv)
    (childSelfResolution : Resolve start childSelfAddress childSelfResolved)
    (childSelfCell : readCell start childSelfResolved = some (.closureCode childChecked.code :: childCaptureValues))
    (childListRep : Children ids start childList children)
    (childLocated : Ash.NetworkLedger.CoreGenericInsert.LocatedEntries children)
    (updateChecked : Ash.NetworkLedger.CoreRecordUpdate.CheckedRecordUpdate recordsList program)
    (updateProjection : RecordProjectionShape program updateChecked.projection)
    (updateProjectionName : updateProjection.functionName = updateChecked.projectionName)
    (updateEntryName : updateProjection.recordName = updateChecked.entryName)
    (updateProjectionCode : updateProjection.code = updateChecked.projectionCode)
    (updateFunction updateArgument updateWantedNode updateReplacementNode updateListNode : NodeId)
    (updateCallName updateWantedName updateReplacementName updateListName : Binder)
    (updateSelfAddress updateSelfResolved updateComparisonAddress updateComparisonResolved
      updateProjectionAddress updateProjectionResolved : Nat)
    (updateCaptureValues : List Value)
    (updateCaptureEnv : Environment)
    (updateTriple : CheckedTuple program updateArgument none [updateWantedNode, updateReplacementNode, updateListNode])
    (updateCallShape : program updateNode = some (.apply updateFunction updateArgument))
    (updateFunctionShape : program updateFunction = some (.variable updateCallName))
    (updateWantedShape : program updateWantedNode = some (.variable updateWantedName))
    (updateReplacementShape : program updateReplacementNode = some (.variable updateReplacementName))
    (updateListShape : program updateListNode = some (.variable updateListName))
    (updateWantedFresh : updateWantedName ≠ updateTriple.contextBinder)
    (updateReplacementFresh : updateReplacementName ≠ updateTriple.contextBinder)
    (updateListFresh : updateListName ≠ updateTriple.contextBinder)
    (updateList : Value)
    (updateBindings : ∀ work replacement,
      let updateEnv := extend (extend env workName work) replacementName replacement
      CoreEval.lookup updateEnv updateCallName = some (.location updateSelfAddress) ∧
      CoreEval.lookup updateEnv updateWantedName = some wanted ∧
      CoreEval.lookup updateEnv updateReplacementName = some replacement ∧
      CoreEval.lookup updateEnv updateListName = some updateList)
    (updateSelfBinding : CoreEval.lookup updateCaptureEnv.reverse updateChecked.functionName = some (.location updateSelfAddress))
    (updateComparisonBinding : CoreEval.lookup updateCaptureEnv.reverse updateChecked.comparisonName = some (.location updateComparisonAddress))
    (updateProjectionBinding : CoreEval.lookup updateCaptureEnv.reverse updateChecked.projectionName = some (.location updateProjectionAddress))
    (updateCaptureBindings : CaptureBindings program updateChecked.captureNodes updateCaptureValues updateCaptureEnv)
    (updateSelfResolution : Resolve start updateSelfAddress updateSelfResolved)
    (updateSelfCell : readCell start updateSelfResolved = some (.closureCode updateChecked.code :: updateCaptureValues))
    (updateComparisonResolution : Resolve start updateComparisonAddress updateComparisonResolved)
    (updateComparisonCell : readCell start updateComparisonResolved = some [.closureCode updateChecked.comparator.code])
    (updateProjectionResolution : Resolve start updateProjectionAddress updateProjectionResolved)
    (updateProjectionCell : readCell start updateProjectionResolved = some [.closureCode updateChecked.projectionCode])
    (updateWantedRep : Ident recordsList start wanted wantedId)
    (updateListRep : Children recordsList start updateList records)
    (updateKeys : RepresentedEntries recordsList (RecordEntry updateProjection.record) start key records)
    (outputChecked : Ash.NetworkLedger.CoreInsert.CheckedInsert outputsList program)
    (outputFunction outputArgument outputCall outputListNode outputConstructorFunction outputConstructorArgument
      outputChildNode outputParentCall outputDestinationNode outputPayloadNode outputParentFunction outputParentArguments
      outputOwnerNode outputWantedNode outputParentOperand outputOperand : NodeId)
    (outputCallName outputListName outputChildName outputOwnerName outputWantedName outputDestinationName outputBytesName : Binder)
    (outputSelfAddress outputSelfResolved : Nat)
    (outputCaptureValues : List Value)
    (outputCaptureEnv : Environment)
    (outputOuterPair : CheckedTuple program outputArgument none [outputCall, outputListNode])
    (outputClosure : CheckedClosure program outputConstructorFunction)
    (outputConstructor : CheckedTuple program outputClosure.body (some workOutTag) [outputOperand])
    (outputTuple : CheckedTuple program outputConstructorArgument none [outputChildNode, outputParentCall, outputDestinationNode, outputPayloadNode])
    (outputParentClosure : CheckedClosure program outputParentFunction)
    (outputParentPair : CheckedTuple program outputParentArguments none [outputOwnerNode, outputWantedNode])
    (outputParentConstructor : CheckedTuple program outputParentClosure.body (some parentTag) [outputParentOperand])
    (outputCallShape : program outputNode = some (.apply outputFunction outputArgument))
    (outputFunctionShape : program outputFunction = some (.variable outputCallName))
    (outputListShape : program outputListNode = some (.variable outputListName))
    (outputListFresh : outputListName ≠ outputOuterPair.contextBinder)
    (outputShape : program outputCall = some (.apply outputConstructorFunction outputConstructorArgument))
    (outputOperandShape : program outputOperand = some (.variable outputClosure.parameter))
    (outputOperandFresh : outputClosure.parameter ≠ outputConstructor.contextBinder)
    (outputChildShape : program outputChildNode = some (.variable outputChildName))
    (outputParentShape : program outputParentCall = some (.apply outputParentFunction outputParentArguments))
    (outputOwnerShape : program outputOwnerNode = some (.variable outputOwnerName))
    (outputWantedShape : program outputWantedNode = some (.variable outputWantedName))
    (outputDestinationShape : program outputDestinationNode = some (.variable outputDestinationName))
    (outputBytesShape : program outputPayloadNode = some (.variable outputBytesName))
    (outputChildOuterFresh : outputChildName ≠ outputOuterPair.contextBinder)
    (outputOwnerOuterFresh : outputOwnerName ≠ outputOuterPair.contextBinder)
    (outputWantedOuterFresh : outputWantedName ≠ outputOuterPair.contextBinder)
    (outputDestinationOuterFresh : outputDestinationName ≠ outputOuterPair.contextBinder)
    (outputBytesOuterFresh : outputBytesName ≠ outputOuterPair.contextBinder)
    (outputChildFresh : outputChildName ≠ outputTuple.contextBinder)
    (outputOwnerFresh : outputOwnerName ≠ outputTuple.contextBinder)
    (outputWantedFresh : outputWantedName ≠ outputTuple.contextBinder)
    (outputDestinationFresh : outputDestinationName ≠ outputTuple.contextBinder)
    (outputBytesFresh : outputBytesName ≠ outputTuple.contextBinder)
    (outputOwnerParentFresh : outputOwnerName ≠ outputParentPair.contextBinder)
    (outputWantedParentFresh : outputWantedName ≠ outputParentPair.contextBinder)
    (outputParentOperandShape : program outputParentOperand = some (.variable outputParentClosure.parameter))
    (outputParentOperandFresh : outputParentClosure.parameter ≠ outputParentConstructor.contextBinder)
    (outputList : Value)
    (outputBindings : ∀ work replacement remaining,
      let outputEnv := extend (extend (extend env workName work) replacementName replacement) remainingName remaining
      CoreEval.lookup outputEnv outputCallName = some (.location outputSelfAddress) ∧
      CoreEval.lookup outputEnv outputListName = some outputList ∧
      CoreEval.lookup outputEnv outputChildName = some work ∧
      CoreEval.lookup outputEnv outputOwnerName = some (.integer (Int.ofNat owner)) ∧
      CoreEval.lookup outputEnv outputWantedName = some wanted ∧
      CoreEval.lookup outputEnv outputDestinationName = some destination ∧
      CoreEval.lookup outputEnv outputBytesName = some bytes)
    (outputSelfBinding : CoreEval.lookup outputCaptureEnv.reverse outputChecked.functionName = some (.location outputSelfAddress))
    (outputCaptureBindings : CaptureBindings program outputChecked.captureNodes outputCaptureValues outputCaptureEnv)
    (outputSelfResolution : Resolve start outputSelfAddress outputSelfResolved)
    (outputSelfCell : readCell start outputSelfResolved = some (.closureCode outputChecked.code :: outputCaptureValues))
    (outputListRep : Children outputsList start outputList outputs)
    (outputLocated : Ash.NetworkLedger.CoreGenericInsert.LocatedEntries outputs)
    (counterBinding : CoreEval.lookup env checkedResult.increment.counterBinder = some (.integer counter))
    (remainingBinder : checkedResult.remainingName = remainingName)
    (outgoingBinder : checkedResult.outgoingName = outgoingName)
    (childBinder : checkedResult.childName = workName)
    (counterWork : checkedResult.increment.counterBinder ≠ workName)
    (counterReplacement : checkedResult.increment.counterBinder ≠ replacementName)
    (counterRemaining : checkedResult.increment.counterBinder ≠ remainingName)
    (counterOutgoing : checkedResult.increment.counterBinder ≠ outgoingName)
    (workReplacement : workName ≠ replacementName)
    (workRemaining : workName ≠ remainingName)
    (workOutgoing : workName ≠ outgoingName)
    (remainingOutgoing : remainingName ≠ outgoingName)
    (evaluation : Eval program env first start result finish)
    (noParent closedTag ackOutTag rejectedTag : Constructor)
    (bytesRep : Value → List UInt8 → Prop)
    (ledger : Ledger)
    (destinationNat : Nat)
    (payload : List UInt8)
    (ownerEq : ledger.owner = owner)
    (counterEq : ledger.next = counter)
    (destinationEq : destination = .integer (Int.ofNat destinationNat))
    (rootSame : recordsList.root = ids.root)
    (workSame : recordsList.work = ids.work)
    (recordTagSame : updateProjection.record = recordTag)
    (semanticRecords : RelatedValues (DecodedRecord ids recordTag noParent parentTag openTag closedTag start) records ledger.records)
    (semanticOutputs : RelatedValues (DecodedOutput ids noParent parentTag workOutTag ackOutTag bytesRep start) outputs ledger.outputs)
    (bytesMeaning : bytesRep bytes payload)
    (foundValue foundKey phase : Value) (phaseAddress phaseResolved : Nat)
    (different : openTag ≠ closedTag)
    (actualLookup : Ash.NetworkLedger.lookup key wantedId records = some foundValue)
    (actualFields : NominalFields recordTag start foundValue [foundKey, parent, phase, childList])
    (phaseEq : phase = .location phaseAddress) (phaseResolution : Resolve start phaseAddress phaseResolved)
    (phaseCell : readCell start phaseResolved = some [.tag openTag])
    :
    DecodedRegistrationResult ids recordsList outputsList checkedResult.ledgerTag recordTag noParent parentTag openTag closedTag
      workOutTag ackOutTag rejectedTag checkedResult.registeredTag bytesRep finish result
      (Ash.NetworkLedger.register ledger wantedId destinationNat payload) := by
  have actualKeys : RepresentedEntries recordsList (RecordEntry recordTag) start key records := by
    simpa [recordTagSame] using updateKeys
  obtain ⟨found, entries, lookupSemantic, isOpen, _, semanticParent, actualChildren, semanticChildren⟩ :=
    checked_open_lookup_decodes ids recordsList recordTag noParent parentTag openTag closedTag start records ledger.records key wantedId
      foundValue foundKey parent phase childList phaseAddress phaseResolved rootSame workSame different actualKeys semanticRecords
      actualLookup actualFields phaseEq phaseResolution phaseCell
  have entriesEq := children_sequence_unique ids start childList children entries childListRep actualChildren
  subst entries
  exact registration_commit_decoded ids recordsList outputsList program buffers checkedResult first second third fourth workNode replacementNode updateNode outputNode workName replacementName remainingName outgoingName recordTag openTag workOutTag parentTag env start finish result wanted parent destination bytes owner counter wantedId key children records outputs firstShape secondShape thirdShape fourthShape nonnegative bounded workFunction workArgument workOwnerNode workCounterNode workOperand workOwnerName workClosure workPair workConstructor workCallShape workOwnerShape workCounterShape workOwnerFresh workCounterFresh workOwnerBinding workOperandShape workOperandFresh childChecked replacementFunction replacementArgument replacementWantedNode replacementParentNode replacementOpenNode childAppendNode replacementOperand childFunction childArgument childCall childListNode childConstructorFunction childConstructorArgument childIdNode childDestinationNode childOperand replacementWantedName replacementParentName childCallName childListName childIdName childDestinationName childSelfAddress childSelfResolved childCaptureValues childCaptureEnv replacementClosure replacementConstructor replacementTuple replacementOpenTuple childOuterPair childClosure childPair childConstructor replacementCallShape replacementOperandShape replacementOperandFresh replacementWantedShape replacementParentShape replacementWantedFresh replacementParentFresh childAppendShape childFunctionShape childListShape childListFresh childCallShape childIdShape childDestinationShape childIdOuterFresh childDestinationOuterFresh childIdFresh childDestinationFresh childOperandShape childOperandFresh childList replacementBindings childBindings childSelfBinding childCaptureBindings childSelfResolution childSelfCell childListRep childLocated updateChecked updateProjection updateProjectionName updateEntryName updateProjectionCode updateFunction updateArgument updateWantedNode updateReplacementNode updateListNode updateCallName updateWantedName updateReplacementName updateListName updateSelfAddress updateSelfResolved updateComparisonAddress updateComparisonResolved updateProjectionAddress updateProjectionResolved updateCaptureValues updateCaptureEnv updateTriple updateCallShape updateFunctionShape updateWantedShape updateReplacementShape updateListShape updateWantedFresh updateReplacementFresh updateListFresh updateList updateBindings updateSelfBinding updateComparisonBinding updateProjectionBinding updateCaptureBindings updateSelfResolution updateSelfCell updateComparisonResolution updateComparisonCell updateProjectionResolution updateProjectionCell updateWantedRep updateListRep updateKeys outputChecked outputFunction outputArgument outputCall outputListNode outputConstructorFunction outputConstructorArgument outputChildNode outputParentCall outputDestinationNode outputPayloadNode outputParentFunction outputParentArguments outputOwnerNode outputWantedNode outputParentOperand outputOperand outputCallName outputListName outputChildName outputOwnerName outputWantedName outputDestinationName outputBytesName outputSelfAddress outputSelfResolved outputCaptureValues outputCaptureEnv outputOuterPair outputClosure outputConstructor outputTuple outputParentClosure outputParentPair outputParentConstructor outputCallShape outputFunctionShape outputListShape outputListFresh outputShape outputOperandShape outputOperandFresh outputChildShape outputParentShape outputOwnerShape outputWantedShape outputDestinationShape outputBytesShape outputChildOuterFresh outputOwnerOuterFresh outputWantedOuterFresh outputDestinationOuterFresh outputBytesOuterFresh outputChildFresh outputOwnerFresh outputWantedFresh outputDestinationFresh outputBytesFresh outputOwnerParentFresh outputWantedParentFresh outputParentOperandShape outputParentOperandFresh outputList outputBindings outputSelfBinding outputCaptureBindings outputSelfResolution outputSelfCell outputListRep outputLocated counterBinding remainingBinder outgoingBinder childBinder counterWork counterReplacement counterRemaining counterOutgoing workReplacement workRemaining workOutgoing remainingOutgoing evaluation noParent closedTag ackOutTag rejectedTag bytesRep ledger found destinationNat payload ownerEq counterEq destinationEq rootSame workSame recordTagSame semanticParent semanticChildren semanticRecords semanticOutputs bytesMeaning lookupSemantic isOpen

/-- The stored finish and commit calls execute the open registration result. -/
theorem checked_finish_open_registration
    (f_program : Program)
    (f_call f_function f_argument : NodeId)
    (f_nodes : List NodeId)
    (f_env : Environment)
    (f_start f_finish : Store)
    (f_result : Value)
    (f_functionName : Binder)
    (f_address f_resolved f_code f_context f_storage f_parameter f_body : Nat)
    (f_captureNodes : List NodeId)
    (f_captureValues : List Value)
    (f_captureEnv : Environment)
    (f_fieldValue : NodeId → Value)
    (f_tuple : CheckedTuple f_program f_argument none f_nodes)
    (f_callShape : f_program f_call = some (.apply f_function f_argument))
    (f_functionShape : f_program f_function = some (.variable f_functionName))
    (f_functionBinding : CoreEval.lookup f_env f_functionName = some (.location f_address))
    (f_resolution : Resolve f_start f_address f_resolved)
    (f_cell : readCell f_start f_resolved = some (.closureCode f_code :: f_captureValues))
    (f_closureShape : f_program f_code = some (.closure f_context f_captureNodes f_storage f_parameter f_body))
    (f_captureBindings : CaptureBindings f_program f_captureNodes f_captureValues f_captureEnv)
    (f_fieldShapes : ∀ node ∈ f_nodes, ∃ name, f_program node = some (.variable name) ∧
      CoreEval.lookup (extend f_env f_tuple.contextBinder .context) name = some (f_fieldValue node))
    (f_scrutinee f_recordMatch f_recordScrutinee f_phaseBranch : NodeId)
    (f_names f_recordNames : List Binder)
    (f_recordName : Binder)
    (f_recordTag f_openTag f_closedTag : Constructor)
    (f_record f_foundKey f_parent f_phase f_children : Value)
    (f_bodyShape : f_program f_body = some (.caseMatch f_scrutinee [(.tuple (f_names.map Pattern.binder), f_recordMatch)]))
    (f_scrutineeShape : f_program f_scrutinee = some (.variable f_parameter))
    (f_arity : f_names.length = (f_nodes.map f_fieldValue).length)
    (f_plain : tupleFields (f_nodes.map f_fieldValue) = some (f_nodes.map f_fieldValue))
    (f_recordShape : f_program f_recordMatch = some (.caseMatch f_recordScrutinee
      [(.constructor f_recordTag (some (.tuple (f_recordNames.map Pattern.binder))), f_phaseBranch)]))
    (f_recordScrutineeShape : f_program f_recordScrutinee = some (.variable f_recordName))
    (f_recordBinding : ∀ payload, CoreEval.lookup ((List.zip f_names (f_nodes.map f_fieldValue)).reverse ++
      extend f_captureEnv.reverse f_parameter (.location payload)) f_recordName = some f_record)
    (f_recordArity : f_recordNames.length = 4)
    (f_recordRep : NominalFields f_recordTag f_start f_record [f_foundKey, f_parent, f_phase, f_children])
    (f_recordPlain : tupleFields [f_foundKey, f_parent, f_phase, f_children] = some [f_foundKey, f_parent, f_phase, f_children])
    (f_phaseAddress f_phaseResolved : Nat)
    (f_phaseEq : f_phase = .location f_phaseAddress)
    (f_phaseResolution : Resolve f_start f_phaseAddress f_phaseResolved)
    (f_phaseCell : readCell f_start f_phaseResolved = some [.tag f_openTag])
    (f_different : f_openTag ≠ f_closedTag)
    (f_phaseNode f_closedBody f_commitCall : NodeId)
    (f_phaseName : Binder)
    (f_phaseShape : f_program f_phaseBranch = some (.caseMatch f_phaseNode
      [(.constructor f_closedTag none, f_closedBody), (.constructor f_openTag none, f_commitCall)]))
    (f_phaseNodeShape : f_program f_phaseNode = some (.variable f_phaseName))
    (f_phaseBinding : ∀ payload, CoreEval.lookup ((List.zip f_recordNames [f_foundKey, f_parent, f_phase, f_children]).reverse ++
      ((List.zip f_names (f_nodes.map f_fieldValue)).reverse ++ extend f_captureEnv.reverse f_parameter (.location payload))) f_phaseName = some f_phase)
    (f_commitFunction f_commitArgument f_commitScrutinee f_commitArm : NodeId)
    (f_commitNodes : List NodeId)
    (f_commitName : Binder)
    (f_commitAddress f_commitResolved f_commitCode f_commitContext f_commitStorage f_commitParameter f_commitBody : Nat)
    (f_commitCaptureNodes : List NodeId)
    (f_commitCaptureValues : List Value)
    (f_commitCaptureEnv : Environment)
    (f_commitFieldValue : NodeId → Value)
    (f_commitTuple : CheckedTuple f_program f_commitArgument none f_commitNodes)
    (f_commitCallShape : f_program f_commitCall = some (.apply f_commitFunction f_commitArgument))
    (f_commitFunctionShape : f_program f_commitFunction = some (.variable f_commitName))
    (f_commitBinding : ∀ payload, CoreEval.lookup ((List.zip f_recordNames [f_foundKey, f_parent, f_phase, f_children]).reverse ++
      ((List.zip f_names (f_nodes.map f_fieldValue)).reverse ++ extend f_captureEnv.reverse f_parameter (.location payload))) f_commitName =
      some (.location f_commitAddress))
    (f_commitResolution : Resolve f_start f_commitAddress f_commitResolved)
    (f_commitCell : readCell f_start f_commitResolved = some (.closureCode f_commitCode :: f_commitCaptureValues))
    (f_commitClosureShape : f_program f_commitCode = some (.closure f_commitContext f_commitCaptureNodes f_commitStorage f_commitParameter f_commitBody))
    (f_commitCaptureBindings : CaptureBindings f_program f_commitCaptureNodes f_commitCaptureValues f_commitCaptureEnv)
    (f_commitFieldShapes : ∀ payload node, node ∈ f_commitNodes → ∃ name, f_program node = some (.variable name) ∧
      CoreEval.lookup (extend ((List.zip f_recordNames [f_foundKey, f_parent, f_phase, f_children]).reverse ++
        ((List.zip f_names (f_nodes.map f_fieldValue)).reverse ++ extend f_captureEnv.reverse f_parameter (.location payload)))
        f_commitTuple.contextBinder .context) name = some (f_commitFieldValue node))
    (f_commitNames : List Binder)
    (f_commitBodyShape : f_program f_commitBody = some (.caseMatch f_commitScrutinee [(.tuple (f_commitNames.map Pattern.binder), f_commitArm)]))
    (f_commitScrutineeShape : f_program f_commitScrutinee = some (.variable f_commitParameter))
    (f_commitArity : f_commitNames.length = (f_commitNodes.map f_commitFieldValue).length)
    (f_commitPlain : tupleFields (f_commitNodes.map f_commitFieldValue) = some (f_commitNodes.map f_commitFieldValue))
    (f_bounded : BoundedLocations f_start)
    (f_evaluation : Eval f_program f_env f_call f_start f_result f_finish)
    (c_ids : Constructors)
    (c_recordsList : Constructors)
    (c_outputsList : Constructors)
    (c_buffers : Ash.NetworkLedger.CoreIncrement.Buffers)
    (c_checkedResult : CheckedSuccessFields f_program c_buffers)
    (c_second : NodeId)
    (c_third : NodeId)
    (c_fourth : NodeId)
    (c_workNode : NodeId)
    (c_replacementNode : NodeId)
    (c_updateNode : NodeId)
    (c_outputNode : NodeId)
    (c_workName : Binder)
    (c_replacementName : Binder)
    (c_remainingName : Binder)
    (c_outgoingName : Binder)
    (c_workOutTag : Constructor)
    (c_parentTag : Constructor)
    (c_wanted : Value)
    (c_destination : Value)
    (c_bytes : Value)
    (c_owner : Nat)
    (c_counter : Int)
    (c_wantedId : Id)
    (c_key : Value → Id)
    (c_children : List Value)
    (c_records : List Value)
    (c_outputs : List Value)
    (c_firstShape : f_program f_commitArm = some (.bind c_workName c_workNode c_second))
    (c_secondShape : f_program c_second = some (.bind c_replacementName c_replacementNode c_third))
    (c_thirdShape : f_program c_third = some (.bind c_remainingName c_updateNode c_fourth))
    (c_fourthShape : f_program c_fourth = some (.bind c_outgoingName c_outputNode c_checkedResult.root))
    (c_nonnegative : 0 ≤ c_counter)
    (c_workFunction : NodeId)
    (c_workArgument : NodeId)
    (c_workOwnerNode : NodeId)
    (c_workCounterNode : NodeId)
    (c_workOperand : NodeId)
    (c_workOwnerName : Binder)
    (c_workClosure : CheckedClosure f_program c_workFunction)
    (c_workPair : CheckedTuple f_program c_workArgument none [c_workOwnerNode, c_workCounterNode])
    (c_workConstructor : CheckedTuple f_program c_workClosure.body (some c_ids.work) [c_workOperand])
    (c_workCallShape : f_program c_workNode = some (.apply c_workFunction c_workArgument))
    (c_workOwnerShape : f_program c_workOwnerNode = some (.variable c_workOwnerName))
    (c_workCounterShape : f_program c_workCounterNode = some (.variable c_checkedResult.increment.counterBinder))
    (c_workOwnerFresh : c_workOwnerName ≠ c_workPair.contextBinder)
    (c_workCounterFresh : c_checkedResult.increment.counterBinder ≠ c_workPair.contextBinder)
    (c_workOwnerBinding : ∀ (s : Store) (p : Nat), CommitFrame f_start s → CoreEval.lookup ((List.zip f_commitNames (f_commitNodes.map f_commitFieldValue)).reverse ++ extend f_commitCaptureEnv.reverse f_commitParameter (.location p)) c_workOwnerName = some (.integer (Int.ofNat c_owner)))
    (c_workOperandShape : f_program c_workOperand = some (.variable c_workClosure.parameter))
    (c_workOperandFresh : c_workClosure.parameter ≠ c_workConstructor.contextBinder)
    (c_childChecked : Ash.NetworkLedger.CoreInsert.CheckedInsert c_ids f_program)
    (c_replacementFunction : NodeId)
    (c_replacementArgument : NodeId)
    (c_replacementWantedNode : NodeId)
    (c_replacementParentNode : NodeId)
    (c_replacementOpenNode : NodeId)
    (c_childAppendNode : NodeId)
    (c_replacementOperand : NodeId)
    (c_childFunction : NodeId)
    (c_childArgument : NodeId)
    (c_childCall : NodeId)
    (c_childListNode : NodeId)
    (c_childConstructorFunction : NodeId)
    (c_childConstructorArgument : NodeId)
    (c_childIdNode : NodeId)
    (c_childDestinationNode : NodeId)
    (c_childOperand : NodeId)
    (c_replacementWantedName : Binder)
    (c_replacementParentName : Binder)
    (c_childCallName : Binder)
    (c_childListName : Binder)
    (c_childIdName : Binder)
    (c_childDestinationName : Binder)
    (c_childSelfAddress : Nat)
    (c_childSelfResolved : Nat)
    (c_childCaptureValues : List Value)
    (c_childCaptureEnv : Environment)
    (c_replacementClosure : CheckedClosure f_program c_replacementFunction)
    (c_replacementConstructor : CheckedTuple f_program c_replacementClosure.body (some f_recordTag) [c_replacementOperand])
    (c_replacementTuple : CheckedTuple f_program c_replacementArgument none
      [c_replacementWantedNode, c_replacementParentNode, c_replacementOpenNode, c_childAppendNode])
    (c_replacementOpenTuple : CheckedTuple f_program c_replacementOpenNode (some f_openTag) [])
    (c_childOuterPair : CheckedTuple f_program c_childArgument none [c_childCall, c_childListNode])
    (c_childClosure : CheckedClosure f_program c_childConstructorFunction)
    (c_childPair : CheckedTuple f_program c_childConstructorArgument none [c_childIdNode, c_childDestinationNode])
    (c_childConstructor : CheckedTuple f_program c_childClosure.body (some c_ids.child) [c_childOperand])
    (c_replacementCallShape : f_program c_replacementNode = some (.apply c_replacementFunction c_replacementArgument))
    (c_replacementOperandShape : f_program c_replacementOperand = some (.variable c_replacementClosure.parameter))
    (c_replacementOperandFresh : c_replacementClosure.parameter ≠ c_replacementConstructor.contextBinder)
    (c_replacementWantedShape : f_program c_replacementWantedNode = some (.variable c_replacementWantedName))
    (c_replacementParentShape : f_program c_replacementParentNode = some (.variable c_replacementParentName))
    (c_replacementWantedFresh : c_replacementWantedName ≠ c_replacementTuple.contextBinder)
    (c_replacementParentFresh : c_replacementParentName ≠ c_replacementTuple.contextBinder)
    (c_childAppendShape : f_program c_childAppendNode = some (.apply c_childFunction c_childArgument))
    (c_childFunctionShape : f_program c_childFunction = some (.variable c_childCallName))
    (c_childListShape : f_program c_childListNode = some (.variable c_childListName))
    (c_childListFresh : c_childListName ≠ c_childOuterPair.contextBinder)
    (c_childCallShape : f_program c_childCall = some (.apply c_childConstructorFunction c_childConstructorArgument))
    (c_childIdShape : f_program c_childIdNode = some (.variable c_childIdName))
    (c_childDestinationShape : f_program c_childDestinationNode = some (.variable c_childDestinationName))
    (c_childIdOuterFresh : c_childIdName ≠ c_childOuterPair.contextBinder)
    (c_childDestinationOuterFresh : c_childDestinationName ≠ c_childOuterPair.contextBinder)
    (c_childIdFresh : c_childIdName ≠ c_childPair.contextBinder)
    (c_childDestinationFresh : c_childDestinationName ≠ c_childPair.contextBinder)
    (c_childOperandShape : f_program c_childOperand = some (.variable c_childClosure.parameter))
    (c_childOperandFresh : c_childClosure.parameter ≠ c_childConstructor.contextBinder)
    (c_replacementBindings : ∀ (s : Store) (p : Nat), CommitFrame f_start s → ∀ work,
      let replacementEnv := extend ((List.zip f_commitNames (f_commitNodes.map f_commitFieldValue)).reverse ++ extend f_commitCaptureEnv.reverse f_commitParameter (.location p)) c_workName work
      CoreEval.lookup replacementEnv c_replacementWantedName = some c_wanted ∧
      CoreEval.lookup replacementEnv c_replacementParentName = some f_parent)
    (c_childBindings : ∀ (s : Store) (p : Nat), CommitFrame f_start s → ∀ work,
      let appendEnv := extend (extend ((List.zip f_commitNames (f_commitNodes.map f_commitFieldValue)).reverse ++ extend f_commitCaptureEnv.reverse f_commitParameter (.location p)) c_workName work) c_replacementTuple.contextBinder .context
      CoreEval.lookup appendEnv c_childCallName = some (.location c_childSelfAddress) ∧
      CoreEval.lookup appendEnv c_childListName = some f_children ∧
      CoreEval.lookup appendEnv c_childIdName = some work ∧
      CoreEval.lookup appendEnv c_childDestinationName = some c_destination)
    (c_childSelfBinding : CoreEval.lookup c_childCaptureEnv.reverse c_childChecked.functionName = some (.location c_childSelfAddress))
    (c_childCaptureBindings : CaptureBindings f_program c_childChecked.captureNodes c_childCaptureValues c_childCaptureEnv)
    (c_childSelfResolution : ∀ (s : Store) (_p : Nat), CommitFrame f_start s → Resolve s c_childSelfAddress c_childSelfResolved)
    (c_childSelfCell : ∀ (s : Store) (_p : Nat), CommitFrame f_start s → readCell s c_childSelfResolved = some (.closureCode c_childChecked.code :: c_childCaptureValues))
    (c_childListRep : ∀ (s : Store) (_p : Nat), CommitFrame f_start s → Children c_ids s f_children c_children)
    (c_childLocated : Ash.NetworkLedger.CoreGenericInsert.LocatedEntries c_children)
    (c_updateChecked : Ash.NetworkLedger.CoreRecordUpdate.CheckedRecordUpdate c_recordsList f_program)
    (c_updateProjection : RecordProjectionShape f_program c_updateChecked.projection)
    (c_updateProjectionName : c_updateProjection.functionName = c_updateChecked.projectionName)
    (c_updateEntryName : c_updateProjection.recordName = c_updateChecked.entryName)
    (c_updateProjectionCode : c_updateProjection.code = c_updateChecked.projectionCode)
    (c_updateFunction : NodeId)
    (c_updateArgument : NodeId)
    (c_updateWantedNode : NodeId)
    (c_updateReplacementNode : NodeId)
    (c_updateListNode : NodeId)
    (c_updateCallName : Binder)
    (c_updateWantedName : Binder)
    (c_updateReplacementName : Binder)
    (c_updateListName : Binder)
    (c_updateSelfAddress : Nat)
    (c_updateSelfResolved : Nat)
    (c_updateComparisonAddress : Nat)
    (c_updateComparisonResolved : Nat)
    (c_updateProjectionAddress : Nat)
    (c_updateProjectionResolved : Nat)
    (c_updateCaptureValues : List Value)
    (c_updateCaptureEnv : Environment)
    (c_updateTriple : CheckedTuple f_program c_updateArgument none [c_updateWantedNode, c_updateReplacementNode, c_updateListNode])
    (c_updateCallShape : f_program c_updateNode = some (.apply c_updateFunction c_updateArgument))
    (c_updateFunctionShape : f_program c_updateFunction = some (.variable c_updateCallName))
    (c_updateWantedShape : f_program c_updateWantedNode = some (.variable c_updateWantedName))
    (c_updateReplacementShape : f_program c_updateReplacementNode = some (.variable c_updateReplacementName))
    (c_updateListShape : f_program c_updateListNode = some (.variable c_updateListName))
    (c_updateWantedFresh : c_updateWantedName ≠ c_updateTriple.contextBinder)
    (c_updateReplacementFresh : c_updateReplacementName ≠ c_updateTriple.contextBinder)
    (c_updateListFresh : c_updateListName ≠ c_updateTriple.contextBinder)
    (c_updateList : Value)
    (c_updateBindings : ∀ (s : Store) (p : Nat), CommitFrame f_start s → ∀ work replacement,
      let updateEnv := extend (extend ((List.zip f_commitNames (f_commitNodes.map f_commitFieldValue)).reverse ++ extend f_commitCaptureEnv.reverse f_commitParameter (.location p)) c_workName work) c_replacementName replacement
      CoreEval.lookup updateEnv c_updateCallName = some (.location c_updateSelfAddress) ∧
      CoreEval.lookup updateEnv c_updateWantedName = some c_wanted ∧
      CoreEval.lookup updateEnv c_updateReplacementName = some replacement ∧
      CoreEval.lookup updateEnv c_updateListName = some c_updateList)
    (c_updateSelfBinding : CoreEval.lookup c_updateCaptureEnv.reverse c_updateChecked.functionName = some (.location c_updateSelfAddress))
    (c_updateComparisonBinding : CoreEval.lookup c_updateCaptureEnv.reverse c_updateChecked.comparisonName = some (.location c_updateComparisonAddress))
    (c_updateProjectionBinding : CoreEval.lookup c_updateCaptureEnv.reverse c_updateChecked.projectionName = some (.location c_updateProjectionAddress))
    (c_updateCaptureBindings : CaptureBindings f_program c_updateChecked.captureNodes c_updateCaptureValues c_updateCaptureEnv)
    (c_updateSelfResolution : ∀ (s : Store) (_p : Nat), CommitFrame f_start s → Resolve s c_updateSelfAddress c_updateSelfResolved)
    (c_updateSelfCell : ∀ (s : Store) (_p : Nat), CommitFrame f_start s → readCell s c_updateSelfResolved = some (.closureCode c_updateChecked.code :: c_updateCaptureValues))
    (c_updateComparisonResolution : ∀ (s : Store) (_p : Nat), CommitFrame f_start s → Resolve s c_updateComparisonAddress c_updateComparisonResolved)
    (c_updateComparisonCell : ∀ (s : Store) (_p : Nat), CommitFrame f_start s → readCell s c_updateComparisonResolved = some [.closureCode c_updateChecked.comparator.code])
    (c_updateProjectionResolution : ∀ (s : Store) (_p : Nat), CommitFrame f_start s → Resolve s c_updateProjectionAddress c_updateProjectionResolved)
    (c_updateProjectionCell : ∀ (s : Store) (_p : Nat), CommitFrame f_start s → readCell s c_updateProjectionResolved = some [.closureCode c_updateChecked.projectionCode])
    (c_updateWantedRep : ∀ (s : Store) (_p : Nat), CommitFrame f_start s → Ident c_recordsList s c_wanted c_wantedId)
    (c_updateListRep : ∀ (s : Store) (_p : Nat), CommitFrame f_start s → Children c_recordsList s c_updateList c_records)
    (c_updateKeys : ∀ (s : Store) (_p : Nat), CommitFrame f_start s → RepresentedEntries c_recordsList (RecordEntry c_updateProjection.record) s c_key c_records)
    (c_outputChecked : Ash.NetworkLedger.CoreInsert.CheckedInsert c_outputsList f_program)
    (c_outputFunction : NodeId)
    (c_outputArgument : NodeId)
    (c_outputCall : NodeId)
    (c_outputListNode : NodeId)
    (c_outputConstructorFunction : NodeId)
    (c_outputConstructorArgument : NodeId)
    (c_outputChildNode : NodeId)
    (c_outputParentCall : NodeId)
    (c_outputDestinationNode : NodeId)
    (c_outputPayloadNode : NodeId)
    (c_outputParentFunction : NodeId)
    (c_outputParentArguments : NodeId)
    (c_outputOwnerNode : NodeId)
    (c_outputWantedNode : NodeId)
    (c_outputParentOperand : NodeId)
    (c_outputOperand : NodeId)
    (c_outputCallName : Binder)
    (c_outputListName : Binder)
    (c_outputChildName : Binder)
    (c_outputOwnerName : Binder)
    (c_outputWantedName : Binder)
    (c_outputDestinationName : Binder)
    (c_outputBytesName : Binder)
    (c_outputSelfAddress : Nat)
    (c_outputSelfResolved : Nat)
    (c_outputCaptureValues : List Value)
    (c_outputCaptureEnv : Environment)
    (c_outputOuterPair : CheckedTuple f_program c_outputArgument none [c_outputCall, c_outputListNode])
    (c_outputClosure : CheckedClosure f_program c_outputConstructorFunction)
    (c_outputConstructor : CheckedTuple f_program c_outputClosure.body (some c_workOutTag) [c_outputOperand])
    (c_outputTuple : CheckedTuple f_program c_outputConstructorArgument none [c_outputChildNode, c_outputParentCall, c_outputDestinationNode, c_outputPayloadNode])
    (c_outputParentClosure : CheckedClosure f_program c_outputParentFunction)
    (c_outputParentPair : CheckedTuple f_program c_outputParentArguments none [c_outputOwnerNode, c_outputWantedNode])
    (c_outputParentConstructor : CheckedTuple f_program c_outputParentClosure.body (some c_parentTag) [c_outputParentOperand])
    (c_outputCallShape : f_program c_outputNode = some (.apply c_outputFunction c_outputArgument))
    (c_outputFunctionShape : f_program c_outputFunction = some (.variable c_outputCallName))
    (c_outputListShape : f_program c_outputListNode = some (.variable c_outputListName))
    (c_outputListFresh : c_outputListName ≠ c_outputOuterPair.contextBinder)
    (c_outputShape : f_program c_outputCall = some (.apply c_outputConstructorFunction c_outputConstructorArgument))
    (c_outputOperandShape : f_program c_outputOperand = some (.variable c_outputClosure.parameter))
    (c_outputOperandFresh : c_outputClosure.parameter ≠ c_outputConstructor.contextBinder)
    (c_outputChildShape : f_program c_outputChildNode = some (.variable c_outputChildName))
    (c_outputParentShape : f_program c_outputParentCall = some (.apply c_outputParentFunction c_outputParentArguments))
    (c_outputOwnerShape : f_program c_outputOwnerNode = some (.variable c_outputOwnerName))
    (c_outputWantedShape : f_program c_outputWantedNode = some (.variable c_outputWantedName))
    (c_outputDestinationShape : f_program c_outputDestinationNode = some (.variable c_outputDestinationName))
    (c_outputBytesShape : f_program c_outputPayloadNode = some (.variable c_outputBytesName))
    (c_outputChildOuterFresh : c_outputChildName ≠ c_outputOuterPair.contextBinder)
    (c_outputOwnerOuterFresh : c_outputOwnerName ≠ c_outputOuterPair.contextBinder)
    (c_outputWantedOuterFresh : c_outputWantedName ≠ c_outputOuterPair.contextBinder)
    (c_outputDestinationOuterFresh : c_outputDestinationName ≠ c_outputOuterPair.contextBinder)
    (c_outputBytesOuterFresh : c_outputBytesName ≠ c_outputOuterPair.contextBinder)
    (c_outputChildFresh : c_outputChildName ≠ c_outputTuple.contextBinder)
    (c_outputOwnerFresh : c_outputOwnerName ≠ c_outputTuple.contextBinder)
    (c_outputWantedFresh : c_outputWantedName ≠ c_outputTuple.contextBinder)
    (c_outputDestinationFresh : c_outputDestinationName ≠ c_outputTuple.contextBinder)
    (c_outputBytesFresh : c_outputBytesName ≠ c_outputTuple.contextBinder)
    (c_outputOwnerParentFresh : c_outputOwnerName ≠ c_outputParentPair.contextBinder)
    (c_outputWantedParentFresh : c_outputWantedName ≠ c_outputParentPair.contextBinder)
    (c_outputParentOperandShape : f_program c_outputParentOperand = some (.variable c_outputParentClosure.parameter))
    (c_outputParentOperandFresh : c_outputParentClosure.parameter ≠ c_outputParentConstructor.contextBinder)
    (c_outputList : Value)
    (c_outputBindings : ∀ (s : Store) (p : Nat), CommitFrame f_start s → ∀ work replacement remaining,
      let outputEnv := extend (extend (extend ((List.zip f_commitNames (f_commitNodes.map f_commitFieldValue)).reverse ++ extend f_commitCaptureEnv.reverse f_commitParameter (.location p)) c_workName work) c_replacementName replacement) c_remainingName remaining
      CoreEval.lookup outputEnv c_outputCallName = some (.location c_outputSelfAddress) ∧
      CoreEval.lookup outputEnv c_outputListName = some c_outputList ∧
      CoreEval.lookup outputEnv c_outputChildName = some work ∧
      CoreEval.lookup outputEnv c_outputOwnerName = some (.integer (Int.ofNat c_owner)) ∧
      CoreEval.lookup outputEnv c_outputWantedName = some c_wanted ∧
      CoreEval.lookup outputEnv c_outputDestinationName = some c_destination ∧
      CoreEval.lookup outputEnv c_outputBytesName = some c_bytes)
    (c_outputSelfBinding : CoreEval.lookup c_outputCaptureEnv.reverse c_outputChecked.functionName = some (.location c_outputSelfAddress))
    (c_outputCaptureBindings : CaptureBindings f_program c_outputChecked.captureNodes c_outputCaptureValues c_outputCaptureEnv)
    (c_outputSelfResolution : ∀ (s : Store) (_p : Nat), CommitFrame f_start s → Resolve s c_outputSelfAddress c_outputSelfResolved)
    (c_outputSelfCell : ∀ (s : Store) (_p : Nat), CommitFrame f_start s → readCell s c_outputSelfResolved = some (.closureCode c_outputChecked.code :: c_outputCaptureValues))
    (c_outputListRep : ∀ (s : Store) (_p : Nat), CommitFrame f_start s → Children c_outputsList s c_outputList c_outputs)
    (c_outputLocated : Ash.NetworkLedger.CoreGenericInsert.LocatedEntries c_outputs)
    (c_counterBinding : ∀ (s : Store) (p : Nat), CommitFrame f_start s → CoreEval.lookup ((List.zip f_commitNames (f_commitNodes.map f_commitFieldValue)).reverse ++ extend f_commitCaptureEnv.reverse f_commitParameter (.location p)) c_checkedResult.increment.counterBinder = some (.integer c_counter))
    (c_remainingBinder : c_checkedResult.remainingName = c_remainingName)
    (c_outgoingBinder : c_checkedResult.outgoingName = c_outgoingName)
    (c_childBinder : c_checkedResult.childName = c_workName)
    (c_counterWork : c_checkedResult.increment.counterBinder ≠ c_workName)
    (c_counterReplacement : c_checkedResult.increment.counterBinder ≠ c_replacementName)
    (c_counterRemaining : c_checkedResult.increment.counterBinder ≠ c_remainingName)
    (c_counterOutgoing : c_checkedResult.increment.counterBinder ≠ c_outgoingName)
    (c_workReplacement : c_workName ≠ c_replacementName)
    (c_workRemaining : c_workName ≠ c_remainingName)
    (c_workOutgoing : c_workName ≠ c_outgoingName)
    (c_remainingOutgoing : c_remainingName ≠ c_outgoingName)
    (c_noParent : Constructor)
    (c_ackOutTag : Constructor)
    (c_rejectedTag : Constructor)
    (c_bytesRep : Value → List UInt8 → Prop)
    (c_ledger : Ledger)
    (c_destinationNat : Nat)
    (c_payload : List UInt8)
    (c_ownerEq : c_ledger.owner = c_owner)
    (c_counterEq : c_ledger.next = c_counter)
    (c_destinationEq : c_destination = .integer (Int.ofNat c_destinationNat))
    (c_rootSame : c_recordsList.root = c_ids.root)
    (c_workSame : c_recordsList.work = c_ids.work)
    (c_recordTagSame : c_updateProjection.record = f_recordTag)
    (c_semanticRecords : ∀ (s : Store) (_p : Nat), CommitFrame f_start s → RelatedValues (DecodedRecord c_ids f_recordTag c_noParent c_parentTag f_openTag f_closedTag s) c_records c_ledger.records)
    (c_semanticOutputs : ∀ (s : Store) (_p : Nat), CommitFrame f_start s → RelatedValues (DecodedOutput c_ids c_noParent c_parentTag c_workOutTag c_ackOutTag c_bytesRep s) c_outputs c_ledger.outputs)
    (c_bytesMeaning : c_bytesRep c_bytes c_payload)
    (c_actualLookup : Ash.NetworkLedger.lookup c_key c_wantedId c_records = some f_record)
    :
    DecodedRegistrationResult c_ids c_recordsList c_outputsList c_checkedResult.ledgerTag f_recordTag c_noParent c_parentTag f_openTag f_closedTag
      c_workOutTag c_ackOutTag c_rejectedTag c_checkedResult.registeredTag c_bytesRep f_finish f_result
      (Ash.NetworkLedger.register c_ledger c_wantedId c_destinationNat c_payload) := by
  obtain ⟨afterCommit, commitPayload, frame, bodyEval⟩ := checked_finish_open_body f_program f_call f_function f_argument f_nodes f_env f_start f_finish f_result f_functionName f_address f_resolved f_code f_context f_storage f_parameter f_body f_captureNodes f_captureValues f_captureEnv f_fieldValue f_tuple f_callShape f_functionShape f_functionBinding f_resolution f_cell f_closureShape f_captureBindings f_fieldShapes f_scrutinee f_recordMatch f_recordScrutinee f_phaseBranch f_names f_recordNames f_recordName f_recordTag f_openTag f_closedTag f_record f_foundKey f_parent f_phase f_children f_bodyShape f_scrutineeShape f_arity f_plain f_recordShape f_recordScrutineeShape f_recordBinding f_recordArity f_recordRep f_recordPlain f_phaseAddress f_phaseResolved f_phaseEq f_phaseResolution f_phaseCell f_different f_phaseNode f_closedBody f_commitCall f_phaseName f_phaseShape f_phaseNodeShape f_phaseBinding f_commitFunction f_commitArgument f_commitScrutinee f_commitArm f_commitNodes f_commitName f_commitAddress f_commitResolved f_commitCode f_commitContext f_commitStorage f_commitParameter f_commitBody f_commitCaptureNodes f_commitCaptureValues f_commitCaptureEnv f_commitFieldValue f_commitTuple f_commitCallShape f_commitFunctionShape f_commitBinding f_commitResolution f_commitCell f_commitClosureShape f_commitCaptureBindings f_commitFieldShapes f_commitNames f_commitBodyShape f_commitScrutineeShape f_commitArity f_commitPlain f_bounded f_evaluation
  exact registration_commit_from_lookup c_ids c_recordsList c_outputsList f_program c_buffers c_checkedResult f_commitArm c_second c_third c_fourth c_workNode c_replacementNode c_updateNode c_outputNode c_workName c_replacementName c_remainingName c_outgoingName f_recordTag f_openTag c_workOutTag c_parentTag ((List.zip f_commitNames (f_commitNodes.map f_commitFieldValue)).reverse ++ extend f_commitCaptureEnv.reverse f_commitParameter (.location commitPayload)) afterCommit f_finish f_result c_wanted f_parent c_destination c_bytes c_owner c_counter c_wantedId c_key c_children c_records c_outputs c_firstShape c_secondShape c_thirdShape c_fourthShape c_nonnegative frame.2.1 c_workFunction c_workArgument c_workOwnerNode c_workCounterNode c_workOperand c_workOwnerName c_workClosure c_workPair c_workConstructor c_workCallShape c_workOwnerShape c_workCounterShape c_workOwnerFresh c_workCounterFresh (c_workOwnerBinding afterCommit commitPayload frame) c_workOperandShape c_workOperandFresh c_childChecked c_replacementFunction c_replacementArgument c_replacementWantedNode c_replacementParentNode c_replacementOpenNode c_childAppendNode c_replacementOperand c_childFunction c_childArgument c_childCall c_childListNode c_childConstructorFunction c_childConstructorArgument c_childIdNode c_childDestinationNode c_childOperand c_replacementWantedName c_replacementParentName c_childCallName c_childListName c_childIdName c_childDestinationName c_childSelfAddress c_childSelfResolved c_childCaptureValues c_childCaptureEnv c_replacementClosure c_replacementConstructor c_replacementTuple c_replacementOpenTuple c_childOuterPair c_childClosure c_childPair c_childConstructor c_replacementCallShape c_replacementOperandShape c_replacementOperandFresh c_replacementWantedShape c_replacementParentShape c_replacementWantedFresh c_replacementParentFresh c_childAppendShape c_childFunctionShape c_childListShape c_childListFresh c_childCallShape c_childIdShape c_childDestinationShape c_childIdOuterFresh c_childDestinationOuterFresh c_childIdFresh c_childDestinationFresh c_childOperandShape c_childOperandFresh f_children (c_replacementBindings afterCommit commitPayload frame) (c_childBindings afterCommit commitPayload frame) c_childSelfBinding c_childCaptureBindings (c_childSelfResolution afterCommit commitPayload frame) (c_childSelfCell afterCommit commitPayload frame) (c_childListRep afterCommit commitPayload frame) c_childLocated c_updateChecked c_updateProjection c_updateProjectionName c_updateEntryName c_updateProjectionCode c_updateFunction c_updateArgument c_updateWantedNode c_updateReplacementNode c_updateListNode c_updateCallName c_updateWantedName c_updateReplacementName c_updateListName c_updateSelfAddress c_updateSelfResolved c_updateComparisonAddress c_updateComparisonResolved c_updateProjectionAddress c_updateProjectionResolved c_updateCaptureValues c_updateCaptureEnv c_updateTriple c_updateCallShape c_updateFunctionShape c_updateWantedShape c_updateReplacementShape c_updateListShape c_updateWantedFresh c_updateReplacementFresh c_updateListFresh c_updateList (c_updateBindings afterCommit commitPayload frame) c_updateSelfBinding c_updateComparisonBinding c_updateProjectionBinding c_updateCaptureBindings (c_updateSelfResolution afterCommit commitPayload frame) (c_updateSelfCell afterCommit commitPayload frame) (c_updateComparisonResolution afterCommit commitPayload frame) (c_updateComparisonCell afterCommit commitPayload frame) (c_updateProjectionResolution afterCommit commitPayload frame) (c_updateProjectionCell afterCommit commitPayload frame) (c_updateWantedRep afterCommit commitPayload frame) (c_updateListRep afterCommit commitPayload frame) (c_updateKeys afterCommit commitPayload frame) c_outputChecked c_outputFunction c_outputArgument c_outputCall c_outputListNode c_outputConstructorFunction c_outputConstructorArgument c_outputChildNode c_outputParentCall c_outputDestinationNode c_outputPayloadNode c_outputParentFunction c_outputParentArguments c_outputOwnerNode c_outputWantedNode c_outputParentOperand c_outputOperand c_outputCallName c_outputListName c_outputChildName c_outputOwnerName c_outputWantedName c_outputDestinationName c_outputBytesName c_outputSelfAddress c_outputSelfResolved c_outputCaptureValues c_outputCaptureEnv c_outputOuterPair c_outputClosure c_outputConstructor c_outputTuple c_outputParentClosure c_outputParentPair c_outputParentConstructor c_outputCallShape c_outputFunctionShape c_outputListShape c_outputListFresh c_outputShape c_outputOperandShape c_outputOperandFresh c_outputChildShape c_outputParentShape c_outputOwnerShape c_outputWantedShape c_outputDestinationShape c_outputBytesShape c_outputChildOuterFresh c_outputOwnerOuterFresh c_outputWantedOuterFresh c_outputDestinationOuterFresh c_outputBytesOuterFresh c_outputChildFresh c_outputOwnerFresh c_outputWantedFresh c_outputDestinationFresh c_outputBytesFresh c_outputOwnerParentFresh c_outputWantedParentFresh c_outputParentOperandShape c_outputParentOperandFresh c_outputList (c_outputBindings afterCommit commitPayload frame) c_outputSelfBinding c_outputCaptureBindings (c_outputSelfResolution afterCommit commitPayload frame) (c_outputSelfCell afterCommit commitPayload frame) (c_outputListRep afterCommit commitPayload frame) c_outputLocated (c_counterBinding afterCommit commitPayload frame) c_remainingBinder c_outgoingBinder c_childBinder c_counterWork c_counterReplacement c_counterRemaining c_counterOutgoing c_workReplacement c_workRemaining c_workOutgoing c_remainingOutgoing bodyEval c_noParent f_closedTag c_ackOutTag c_rejectedTag c_bytesRep c_ledger c_destinationNat c_payload c_ownerEq c_counterEq c_destinationEq c_rootSame c_workSame c_recordTagSame (c_semanticRecords afterCommit commitPayload frame) (c_semanticOutputs afterCommit commitPayload frame) c_bytesMeaning f_record f_foundKey f_phase f_phaseAddress f_phaseResolved f_different c_actualLookup (nominal_fields_retained f_recordTag f_start afterCommit f_record _ frame.1 frame.2.2 f_recordRep) f_phaseEq (resolve_preserved frame.1 frame.2.2 f_phaseResolution) (frame.2.2 f_phaseResolved _ f_phaseCell)

/-- The actual lookup call enters the hit branch with the whole located Record. -/
theorem checked_lookup_hit_branch (recordsList : Constructors) (program : Program)
    (absent present : Constructor) (checked : CheckedLookupBase recordsList program absent present)
    (projection : RecordProjectionShape program checked.projection)
    (projectionFunctionName : projection.functionName = checked.projectionName)
    (projectionEntryName : projection.recordName = checked.entryName)
    (projectionCode : projection.code = checked.projectionCode)
    (branch call missingBody foundBody function argument wantedNode listNode : NodeId)
    (name callName wantedName listName : Binder) (env : Environment) (start finish : Store)
    (result wantedValue list found : Value) (wanted : Id) (records : List Value) (key : Value → Id)
    (selfAddress selfResolved comparisonAddress comparisonResolved projectionAddress projectionResolved : Nat)
    (captureValues : List Value) (captureEnv : Environment)
    (branchShape : program branch = some (.caseMatch call
      [(.constructor absent none, missingBody), (.constructor present (some (.binder name)), foundBody)]))
    (lookupPair : CheckedTuple program argument none [wantedNode, listNode])
    (callShape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable callName))
    (functionBinding : CoreEval.lookup env callName = some (.location selfAddress))
    (wantedShape : program wantedNode = some (.variable wantedName)) (listShape : program listNode = some (.variable listName))
    (wantedFresh : wantedName ≠ lookupPair.contextBinder) (listFresh : listName ≠ lookupPair.contextBinder)
    (wantedBinding : CoreEval.lookup env wantedName = some wantedValue) (listBinding : CoreEval.lookup env listName = some list)
    (selfBinding : CoreEval.lookup captureEnv.reverse checked.functionName = some (.location selfAddress))
    (comparisonBinding : CoreEval.lookup captureEnv.reverse checked.comparisonName = some (.location comparisonAddress))
    (projectionBinding : CoreEval.lookup captureEnv.reverse checked.projectionName = some (.location projectionAddress))
    (captureBindings : CaptureBindings program checked.captureNodes captureValues captureEnv)
    (selfResolution : Resolve start selfAddress selfResolved)
    (selfCell : readCell start selfResolved = some (.closureCode checked.code :: captureValues))
    (comparisonResolution : Resolve start comparisonAddress comparisonResolved)
    (comparisonCell : readCell start comparisonResolved = some [.closureCode checked.comparator.code])
    (projectionResolution : Resolve start projectionAddress projectionResolved)
    (projectionCell : readCell start projectionResolved = some [.closureCode checked.projectionCode])
    (bounded : BoundedLocations start) (wantedRep : Ident recordsList start wantedValue wanted)
    (listRep : Children recordsList start list records)
    (lookupKeys : RepresentedEntries recordsList (RecordEntry projection.record) start key records)
    (actualLookup : Ash.NetworkLedger.lookup key wanted records = some found)
    (evaluation : Eval program env branch start result finish) :
    ∃ middle, CommitFrame start middle ∧ Eval program (extend env name found) foundBody middle result finish := by
  have lookupLaw : ∀ middle value, Eval program env call start value middle →
      LookupOutcome absent present start middle value (some found) := by
    intro middle value callEval
    have lookup := checked_record_lookup_call recordsList program absent present checked projection projectionFunctionName
      projectionEntryName projectionCode call function argument wantedNode listNode env start middle value wantedValue list wanted key records
      callName wantedName listName selfAddress selfResolved comparisonAddress comparisonResolved projectionAddress projectionResolved
      captureValues captureEnv lookupPair callShape functionShape functionBinding wantedShape listShape wantedFresh listFresh wantedBinding
      listBinding selfBinding comparisonBinding projectionBinding captureBindings selfResolution selfCell comparisonResolution comparisonCell
      projectionResolution projectionCell bounded wantedRep listRep lookupKeys callEval
    simpa [actualLookup] using lookup
  obtain ⟨middle, bodyEval, _progress, aliases, middleBound, retained⟩ :=
    registration_lookup_branch program absent present branch call missingBody foundBody name env start finish result (some found)
      branchShape lookupLaw evaluation
  exact ⟨middle, ⟨aliases, middleBound, retained⟩, bodyEval⟩

/-- The actual lookup hit, stored finish call, and checked commit return the open registration result. -/
theorem checked_lookup_finish_open_registration
    (o_recordsList : Constructors)
    (o_program : Program)
    (o_absent o_present : Constructor)
    (o_checked : CheckedLookupBase o_recordsList o_program o_absent o_present)
    (o_projection : RecordProjectionShape o_program o_checked.projection)
    (o_projectionFunctionName : o_projection.functionName = o_checked.projectionName)
    (o_projectionEntryName : o_projection.recordName = o_checked.entryName)
    (o_projectionCode : o_projection.code = o_checked.projectionCode)
    (o_branch o_call o_missingBody o_foundBody o_function o_argument o_wantedNode o_listNode : NodeId)
    (o_name o_callName o_wantedName o_listName : Binder)
    (o_env : Environment)
    (o_start o_finish : Store)
    (o_result o_wantedValue o_list o_found : Value)
    (o_wanted : Id)
    (o_records : List Value)
    (o_key : Value → Id)
    (o_selfAddress o_selfResolved o_comparisonAddress o_comparisonResolved o_projectionAddress o_projectionResolved : Nat)
    (o_captureValues : List Value)
    (o_captureEnv : Environment)
    (o_branchShape : o_program o_branch = some (.caseMatch o_call
      [(.constructor o_absent none, o_missingBody), (.constructor o_present (some (.binder o_name)), o_foundBody)]))
    (o_lookupPair : CheckedTuple o_program o_argument none [o_wantedNode, o_listNode])
    (o_callShape : o_program o_call = some (.apply o_function o_argument))
    (o_functionShape : o_program o_function = some (.variable o_callName))
    (o_functionBinding : CoreEval.lookup o_env o_callName = some (.location o_selfAddress))
    (o_wantedShape : o_program o_wantedNode = some (.variable o_wantedName))
    (o_listShape : o_program o_listNode = some (.variable o_listName))
    (o_wantedFresh : o_wantedName ≠ o_lookupPair.contextBinder)
    (o_listFresh : o_listName ≠ o_lookupPair.contextBinder)
    (o_wantedBinding : CoreEval.lookup o_env o_wantedName = some o_wantedValue)
    (o_listBinding : CoreEval.lookup o_env o_listName = some o_list)
    (o_selfBinding : CoreEval.lookup o_captureEnv.reverse o_checked.functionName = some (.location o_selfAddress))
    (o_comparisonBinding : CoreEval.lookup o_captureEnv.reverse o_checked.comparisonName = some (.location o_comparisonAddress))
    (o_projectionBinding : CoreEval.lookup o_captureEnv.reverse o_checked.projectionName = some (.location o_projectionAddress))
    (o_captureBindings : CaptureBindings o_program o_checked.captureNodes o_captureValues o_captureEnv)
    (o_selfResolution : Resolve o_start o_selfAddress o_selfResolved)
    (o_selfCell : readCell o_start o_selfResolved = some (.closureCode o_checked.code :: o_captureValues))
    (o_comparisonResolution : Resolve o_start o_comparisonAddress o_comparisonResolved)
    (o_comparisonCell : readCell o_start o_comparisonResolved = some [.closureCode o_checked.comparator.code])
    (o_projectionResolution : Resolve o_start o_projectionAddress o_projectionResolved)
    (o_projectionCell : readCell o_start o_projectionResolved = some [.closureCode o_checked.projectionCode])
    (o_bounded : BoundedLocations o_start)
    (o_wantedRep : Ident o_recordsList o_start o_wantedValue o_wanted)
    (o_listRep : Children o_recordsList o_start o_list o_records)
    (o_lookupKeys : RepresentedEntries o_recordsList (RecordEntry o_projection.record) o_start o_key o_records)
    (o_actualLookup : Ash.NetworkLedger.lookup o_key o_wanted o_records = some o_found)
    (o_evaluation : Eval o_program o_env o_branch o_start o_result o_finish)
    (n_f_function : NodeId)
    (n_f_argument : NodeId)
    (n_f_nodes : List NodeId)
    (n_f_functionName : Binder)
    (n_f_address : Nat)
    (n_f_resolved : Nat)
    (n_f_code : Nat)
    (n_f_context : Nat)
    (n_f_storage : Nat)
    (n_f_parameter : Nat)
    (n_f_body : Nat)
    (n_f_captureNodes : List NodeId)
    (n_f_captureValues : List Value)
    (n_f_captureEnv : Environment)
    (n_f_fieldValue : NodeId → Value)
    (n_f_tuple : CheckedTuple o_program n_f_argument none n_f_nodes)
    (n_f_callShape : o_program o_foundBody = some (.apply n_f_function n_f_argument))
    (n_f_functionShape : o_program n_f_function = some (.variable n_f_functionName))
    (n_f_functionBinding : CoreEval.lookup (extend o_env o_name o_found) n_f_functionName = some (.location n_f_address))
    (n_f_resolution : ∀ (middle : Store), CommitFrame o_start middle → Resolve middle n_f_address n_f_resolved)
    (n_f_cell : ∀ (middle : Store), CommitFrame o_start middle → readCell middle n_f_resolved = some (.closureCode n_f_code :: n_f_captureValues))
    (n_f_closureShape : o_program n_f_code = some (.closure n_f_context n_f_captureNodes n_f_storage n_f_parameter n_f_body))
    (n_f_captureBindings : CaptureBindings o_program n_f_captureNodes n_f_captureValues n_f_captureEnv)
    (n_f_fieldShapes : ∀ node ∈ n_f_nodes, ∃ name, o_program node = some (.variable name) ∧
      CoreEval.lookup (extend (extend o_env o_name o_found) n_f_tuple.contextBinder .context) name = some (n_f_fieldValue node))
    (n_f_scrutinee : NodeId)
    (n_f_recordMatch : NodeId)
    (n_f_recordScrutinee : NodeId)
    (n_f_phaseBranch : NodeId)
    (n_f_names : List Binder)
    (n_f_recordNames : List Binder)
    (n_f_recordName : Binder)
    (n_f_recordTag : Constructor)
    (n_f_openTag : Constructor)
    (n_f_closedTag : Constructor)
    (n_f_foundKey : Value)
    (n_f_parent : Value)
    (n_f_phase : Value)
    (n_f_children : Value)
    (n_f_bodyShape : o_program n_f_body = some (.caseMatch n_f_scrutinee [(.tuple (n_f_names.map Pattern.binder), n_f_recordMatch)]))
    (n_f_scrutineeShape : o_program n_f_scrutinee = some (.variable n_f_parameter))
    (n_f_arity : n_f_names.length = (n_f_nodes.map n_f_fieldValue).length)
    (n_f_plain : tupleFields (n_f_nodes.map n_f_fieldValue) = some (n_f_nodes.map n_f_fieldValue))
    (n_f_recordShape : o_program n_f_recordMatch = some (.caseMatch n_f_recordScrutinee
      [(.constructor n_f_recordTag (some (.tuple (n_f_recordNames.map Pattern.binder))), n_f_phaseBranch)]))
    (n_f_recordScrutineeShape : o_program n_f_recordScrutinee = some (.variable n_f_recordName))
    (n_f_recordBinding : ∀ payload, CoreEval.lookup ((List.zip n_f_names (n_f_nodes.map n_f_fieldValue)).reverse ++
      extend n_f_captureEnv.reverse n_f_parameter (.location payload)) n_f_recordName = some o_found)
    (n_f_recordArity : n_f_recordNames.length = 4)
    (n_f_recordRep : ∀ (middle : Store), CommitFrame o_start middle → NominalFields n_f_recordTag middle o_found [n_f_foundKey, n_f_parent, n_f_phase, n_f_children])
    (n_f_recordPlain : tupleFields [n_f_foundKey, n_f_parent, n_f_phase, n_f_children] = some [n_f_foundKey, n_f_parent, n_f_phase, n_f_children])
    (n_f_phaseAddress : Nat)
    (n_f_phaseResolved : Nat)
    (n_f_phaseEq : n_f_phase = .location n_f_phaseAddress)
    (n_f_phaseResolution : ∀ (middle : Store), CommitFrame o_start middle → Resolve middle n_f_phaseAddress n_f_phaseResolved)
    (n_f_phaseCell : ∀ (middle : Store), CommitFrame o_start middle → readCell middle n_f_phaseResolved = some [.tag n_f_openTag])
    (n_f_different : n_f_openTag ≠ n_f_closedTag)
    (n_f_phaseNode : NodeId)
    (n_f_closedBody : NodeId)
    (n_f_commitCall : NodeId)
    (n_f_phaseName : Binder)
    (n_f_phaseShape : o_program n_f_phaseBranch = some (.caseMatch n_f_phaseNode
      [(.constructor n_f_closedTag none, n_f_closedBody), (.constructor n_f_openTag none, n_f_commitCall)]))
    (n_f_phaseNodeShape : o_program n_f_phaseNode = some (.variable n_f_phaseName))
    (n_f_phaseBinding : ∀ payload, CoreEval.lookup ((List.zip n_f_recordNames [n_f_foundKey, n_f_parent, n_f_phase, n_f_children]).reverse ++
      ((List.zip n_f_names (n_f_nodes.map n_f_fieldValue)).reverse ++ extend n_f_captureEnv.reverse n_f_parameter (.location payload))) n_f_phaseName = some n_f_phase)
    (n_f_commitFunction : NodeId)
    (n_f_commitArgument : NodeId)
    (n_f_commitScrutinee : NodeId)
    (n_f_commitArm : NodeId)
    (n_f_commitNodes : List NodeId)
    (n_f_commitName : Binder)
    (n_f_commitAddress : Nat)
    (n_f_commitResolved : Nat)
    (n_f_commitCode : Nat)
    (n_f_commitContext : Nat)
    (n_f_commitStorage : Nat)
    (n_f_commitParameter : Nat)
    (n_f_commitBody : Nat)
    (n_f_commitCaptureNodes : List NodeId)
    (n_f_commitCaptureValues : List Value)
    (n_f_commitCaptureEnv : Environment)
    (n_f_commitFieldValue : NodeId → Value)
    (n_f_commitTuple : CheckedTuple o_program n_f_commitArgument none n_f_commitNodes)
    (n_f_commitCallShape : o_program n_f_commitCall = some (.apply n_f_commitFunction n_f_commitArgument))
    (n_f_commitFunctionShape : o_program n_f_commitFunction = some (.variable n_f_commitName))
    (n_f_commitBinding : ∀ payload, CoreEval.lookup ((List.zip n_f_recordNames [n_f_foundKey, n_f_parent, n_f_phase, n_f_children]).reverse ++
      ((List.zip n_f_names (n_f_nodes.map n_f_fieldValue)).reverse ++ extend n_f_captureEnv.reverse n_f_parameter (.location payload))) n_f_commitName =
      some (.location n_f_commitAddress))
    (n_f_commitResolution : ∀ (middle : Store), CommitFrame o_start middle → Resolve middle n_f_commitAddress n_f_commitResolved)
    (n_f_commitCell : ∀ (middle : Store), CommitFrame o_start middle → readCell middle n_f_commitResolved = some (.closureCode n_f_commitCode :: n_f_commitCaptureValues))
    (n_f_commitClosureShape : o_program n_f_commitCode = some (.closure n_f_commitContext n_f_commitCaptureNodes n_f_commitStorage n_f_commitParameter n_f_commitBody))
    (n_f_commitCaptureBindings : CaptureBindings o_program n_f_commitCaptureNodes n_f_commitCaptureValues n_f_commitCaptureEnv)
    (n_f_commitFieldShapes : ∀ payload node, node ∈ n_f_commitNodes → ∃ name, o_program node = some (.variable name) ∧
      CoreEval.lookup (extend ((List.zip n_f_recordNames [n_f_foundKey, n_f_parent, n_f_phase, n_f_children]).reverse ++
        ((List.zip n_f_names (n_f_nodes.map n_f_fieldValue)).reverse ++ extend n_f_captureEnv.reverse n_f_parameter (.location payload)))
        n_f_commitTuple.contextBinder .context) name = some (n_f_commitFieldValue node))
    (n_f_commitNames : List Binder)
    (n_f_commitBodyShape : o_program n_f_commitBody = some (.caseMatch n_f_commitScrutinee [(.tuple (n_f_commitNames.map Pattern.binder), n_f_commitArm)]))
    (n_f_commitScrutineeShape : o_program n_f_commitScrutinee = some (.variable n_f_commitParameter))
    (n_f_commitArity : n_f_commitNames.length = (n_f_commitNodes.map n_f_commitFieldValue).length)
    (n_f_commitPlain : tupleFields (n_f_commitNodes.map n_f_commitFieldValue) = some (n_f_commitNodes.map n_f_commitFieldValue))
    (n_f_bounded : ∀ (middle : Store), CommitFrame o_start middle → BoundedLocations middle)
    (n_c_ids : Constructors)
    (n_c_outputsList : Constructors)
    (n_c_buffers : Ash.NetworkLedger.CoreIncrement.Buffers)
    (n_c_checkedResult : CheckedSuccessFields o_program n_c_buffers)
    (n_c_second : NodeId)
    (n_c_third : NodeId)
    (n_c_fourth : NodeId)
    (n_c_workNode : NodeId)
    (n_c_replacementNode : NodeId)
    (n_c_updateNode : NodeId)
    (n_c_outputNode : NodeId)
    (n_c_workName : Binder)
    (n_c_replacementName : Binder)
    (n_c_remainingName : Binder)
    (n_c_outgoingName : Binder)
    (n_c_workOutTag : Constructor)
    (n_c_parentTag : Constructor)
    (n_c_destination : Value)
    (n_c_bytes : Value)
    (n_c_owner : Nat)
    (n_c_counter : Int)
    (n_c_children : List Value)
    (n_c_outputs : List Value)
    (n_c_firstShape : o_program n_f_commitArm = some (.bind n_c_workName n_c_workNode n_c_second))
    (n_c_secondShape : o_program n_c_second = some (.bind n_c_replacementName n_c_replacementNode n_c_third))
    (n_c_thirdShape : o_program n_c_third = some (.bind n_c_remainingName n_c_updateNode n_c_fourth))
    (n_c_fourthShape : o_program n_c_fourth = some (.bind n_c_outgoingName n_c_outputNode n_c_checkedResult.root))
    (n_c_nonnegative : 0 ≤ n_c_counter)
    (n_c_workFunction : NodeId)
    (n_c_workArgument : NodeId)
    (n_c_workOwnerNode : NodeId)
    (n_c_workCounterNode : NodeId)
    (n_c_workOperand : NodeId)
    (n_c_workOwnerName : Binder)
    (n_c_workClosure : CheckedClosure o_program n_c_workFunction)
    (n_c_workPair : CheckedTuple o_program n_c_workArgument none [n_c_workOwnerNode, n_c_workCounterNode])
    (n_c_workConstructor : CheckedTuple o_program n_c_workClosure.body (some n_c_ids.work) [n_c_workOperand])
    (n_c_workCallShape : o_program n_c_workNode = some (.apply n_c_workFunction n_c_workArgument))
    (n_c_workOwnerShape : o_program n_c_workOwnerNode = some (.variable n_c_workOwnerName))
    (n_c_workCounterShape : o_program n_c_workCounterNode = some (.variable n_c_checkedResult.increment.counterBinder))
    (n_c_workOwnerFresh : n_c_workOwnerName ≠ n_c_workPair.contextBinder)
    (n_c_workCounterFresh : n_c_checkedResult.increment.counterBinder ≠ n_c_workPair.contextBinder)
    (n_c_workOwnerBinding : ∀ (middle : Store), CommitFrame o_start middle → ∀ (s : Store) (p : Nat), CommitFrame middle s → CoreEval.lookup ((List.zip n_f_commitNames (n_f_commitNodes.map n_f_commitFieldValue)).reverse ++ extend n_f_commitCaptureEnv.reverse n_f_commitParameter (.location p)) n_c_workOwnerName = some (.integer (Int.ofNat n_c_owner)))
    (n_c_workOperandShape : o_program n_c_workOperand = some (.variable n_c_workClosure.parameter))
    (n_c_workOperandFresh : n_c_workClosure.parameter ≠ n_c_workConstructor.contextBinder)
    (n_c_childChecked : Ash.NetworkLedger.CoreInsert.CheckedInsert n_c_ids o_program)
    (n_c_replacementFunction : NodeId)
    (n_c_replacementArgument : NodeId)
    (n_c_replacementWantedNode : NodeId)
    (n_c_replacementParentNode : NodeId)
    (n_c_replacementOpenNode : NodeId)
    (n_c_childAppendNode : NodeId)
    (n_c_replacementOperand : NodeId)
    (n_c_childFunction : NodeId)
    (n_c_childArgument : NodeId)
    (n_c_childCall : NodeId)
    (n_c_childListNode : NodeId)
    (n_c_childConstructorFunction : NodeId)
    (n_c_childConstructorArgument : NodeId)
    (n_c_childIdNode : NodeId)
    (n_c_childDestinationNode : NodeId)
    (n_c_childOperand : NodeId)
    (n_c_replacementWantedName : Binder)
    (n_c_replacementParentName : Binder)
    (n_c_childCallName : Binder)
    (n_c_childListName : Binder)
    (n_c_childIdName : Binder)
    (n_c_childDestinationName : Binder)
    (n_c_childSelfAddress : Nat)
    (n_c_childSelfResolved : Nat)
    (n_c_childCaptureValues : List Value)
    (n_c_childCaptureEnv : Environment)
    (n_c_replacementClosure : CheckedClosure o_program n_c_replacementFunction)
    (n_c_replacementConstructor : CheckedTuple o_program n_c_replacementClosure.body (some n_f_recordTag) [n_c_replacementOperand])
    (n_c_replacementTuple : CheckedTuple o_program n_c_replacementArgument none
      [n_c_replacementWantedNode, n_c_replacementParentNode, n_c_replacementOpenNode, n_c_childAppendNode])
    (n_c_replacementOpenTuple : CheckedTuple o_program n_c_replacementOpenNode (some n_f_openTag) [])
    (n_c_childOuterPair : CheckedTuple o_program n_c_childArgument none [n_c_childCall, n_c_childListNode])
    (n_c_childClosure : CheckedClosure o_program n_c_childConstructorFunction)
    (n_c_childPair : CheckedTuple o_program n_c_childConstructorArgument none [n_c_childIdNode, n_c_childDestinationNode])
    (n_c_childConstructor : CheckedTuple o_program n_c_childClosure.body (some n_c_ids.child) [n_c_childOperand])
    (n_c_replacementCallShape : o_program n_c_replacementNode = some (.apply n_c_replacementFunction n_c_replacementArgument))
    (n_c_replacementOperandShape : o_program n_c_replacementOperand = some (.variable n_c_replacementClosure.parameter))
    (n_c_replacementOperandFresh : n_c_replacementClosure.parameter ≠ n_c_replacementConstructor.contextBinder)
    (n_c_replacementWantedShape : o_program n_c_replacementWantedNode = some (.variable n_c_replacementWantedName))
    (n_c_replacementParentShape : o_program n_c_replacementParentNode = some (.variable n_c_replacementParentName))
    (n_c_replacementWantedFresh : n_c_replacementWantedName ≠ n_c_replacementTuple.contextBinder)
    (n_c_replacementParentFresh : n_c_replacementParentName ≠ n_c_replacementTuple.contextBinder)
    (n_c_childAppendShape : o_program n_c_childAppendNode = some (.apply n_c_childFunction n_c_childArgument))
    (n_c_childFunctionShape : o_program n_c_childFunction = some (.variable n_c_childCallName))
    (n_c_childListShape : o_program n_c_childListNode = some (.variable n_c_childListName))
    (n_c_childListFresh : n_c_childListName ≠ n_c_childOuterPair.contextBinder)
    (n_c_childCallShape : o_program n_c_childCall = some (.apply n_c_childConstructorFunction n_c_childConstructorArgument))
    (n_c_childIdShape : o_program n_c_childIdNode = some (.variable n_c_childIdName))
    (n_c_childDestinationShape : o_program n_c_childDestinationNode = some (.variable n_c_childDestinationName))
    (n_c_childIdOuterFresh : n_c_childIdName ≠ n_c_childOuterPair.contextBinder)
    (n_c_childDestinationOuterFresh : n_c_childDestinationName ≠ n_c_childOuterPair.contextBinder)
    (n_c_childIdFresh : n_c_childIdName ≠ n_c_childPair.contextBinder)
    (n_c_childDestinationFresh : n_c_childDestinationName ≠ n_c_childPair.contextBinder)
    (n_c_childOperandShape : o_program n_c_childOperand = some (.variable n_c_childClosure.parameter))
    (n_c_childOperandFresh : n_c_childClosure.parameter ≠ n_c_childConstructor.contextBinder)
    (n_c_replacementBindings : ∀ (middle : Store), CommitFrame o_start middle → ∀ (s : Store) (p : Nat), CommitFrame middle s → ∀ work,
      let replacementEnv := extend ((List.zip n_f_commitNames (n_f_commitNodes.map n_f_commitFieldValue)).reverse ++ extend n_f_commitCaptureEnv.reverse n_f_commitParameter (.location p)) n_c_workName work
      CoreEval.lookup replacementEnv n_c_replacementWantedName = some o_wantedValue ∧
      CoreEval.lookup replacementEnv n_c_replacementParentName = some n_f_parent)
    (n_c_childBindings : ∀ (middle : Store), CommitFrame o_start middle → ∀ (s : Store) (p : Nat), CommitFrame middle s → ∀ work,
      let appendEnv := extend (extend ((List.zip n_f_commitNames (n_f_commitNodes.map n_f_commitFieldValue)).reverse ++ extend n_f_commitCaptureEnv.reverse n_f_commitParameter (.location p)) n_c_workName work) n_c_replacementTuple.contextBinder .context
      CoreEval.lookup appendEnv n_c_childCallName = some (.location n_c_childSelfAddress) ∧
      CoreEval.lookup appendEnv n_c_childListName = some n_f_children ∧
      CoreEval.lookup appendEnv n_c_childIdName = some work ∧
      CoreEval.lookup appendEnv n_c_childDestinationName = some n_c_destination)
    (n_c_childSelfBinding : CoreEval.lookup n_c_childCaptureEnv.reverse n_c_childChecked.functionName = some (.location n_c_childSelfAddress))
    (n_c_childCaptureBindings : CaptureBindings o_program n_c_childChecked.captureNodes n_c_childCaptureValues n_c_childCaptureEnv)
    (n_c_childSelfResolution : ∀ (middle : Store), CommitFrame o_start middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → Resolve s n_c_childSelfAddress n_c_childSelfResolved)
    (n_c_childSelfCell : ∀ (middle : Store), CommitFrame o_start middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → readCell s n_c_childSelfResolved = some (.closureCode n_c_childChecked.code :: n_c_childCaptureValues))
    (n_c_childListRep : ∀ (middle : Store), CommitFrame o_start middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → Children n_c_ids s n_f_children n_c_children)
    (n_c_childLocated : Ash.NetworkLedger.CoreGenericInsert.LocatedEntries n_c_children)
    (n_c_updateChecked : Ash.NetworkLedger.CoreRecordUpdate.CheckedRecordUpdate o_recordsList o_program)
    (n_c_updateProjection : RecordProjectionShape o_program n_c_updateChecked.projection)
    (n_c_updateProjectionName : n_c_updateProjection.functionName = n_c_updateChecked.projectionName)
    (n_c_updateEntryName : n_c_updateProjection.recordName = n_c_updateChecked.entryName)
    (n_c_updateProjectionCode : n_c_updateProjection.code = n_c_updateChecked.projectionCode)
    (n_c_updateFunction : NodeId)
    (n_c_updateArgument : NodeId)
    (n_c_updateWantedNode : NodeId)
    (n_c_updateReplacementNode : NodeId)
    (n_c_updateListNode : NodeId)
    (n_c_updateCallName : Binder)
    (n_c_updateWantedName : Binder)
    (n_c_updateReplacementName : Binder)
    (n_c_updateListName : Binder)
    (n_c_updateSelfAddress : Nat)
    (n_c_updateSelfResolved : Nat)
    (n_c_updateComparisonAddress : Nat)
    (n_c_updateComparisonResolved : Nat)
    (n_c_updateProjectionAddress : Nat)
    (n_c_updateProjectionResolved : Nat)
    (n_c_updateCaptureValues : List Value)
    (n_c_updateCaptureEnv : Environment)
    (n_c_updateTriple : CheckedTuple o_program n_c_updateArgument none [n_c_updateWantedNode, n_c_updateReplacementNode, n_c_updateListNode])
    (n_c_updateCallShape : o_program n_c_updateNode = some (.apply n_c_updateFunction n_c_updateArgument))
    (n_c_updateFunctionShape : o_program n_c_updateFunction = some (.variable n_c_updateCallName))
    (n_c_updateWantedShape : o_program n_c_updateWantedNode = some (.variable n_c_updateWantedName))
    (n_c_updateReplacementShape : o_program n_c_updateReplacementNode = some (.variable n_c_updateReplacementName))
    (n_c_updateListShape : o_program n_c_updateListNode = some (.variable n_c_updateListName))
    (n_c_updateWantedFresh : n_c_updateWantedName ≠ n_c_updateTriple.contextBinder)
    (n_c_updateReplacementFresh : n_c_updateReplacementName ≠ n_c_updateTriple.contextBinder)
    (n_c_updateListFresh : n_c_updateListName ≠ n_c_updateTriple.contextBinder)
    (n_c_updateList : Value)
    (n_c_updateBindings : ∀ (middle : Store), CommitFrame o_start middle → ∀ (s : Store) (p : Nat), CommitFrame middle s → ∀ work replacement,
      let updateEnv := extend (extend ((List.zip n_f_commitNames (n_f_commitNodes.map n_f_commitFieldValue)).reverse ++ extend n_f_commitCaptureEnv.reverse n_f_commitParameter (.location p)) n_c_workName work) n_c_replacementName replacement
      CoreEval.lookup updateEnv n_c_updateCallName = some (.location n_c_updateSelfAddress) ∧
      CoreEval.lookup updateEnv n_c_updateWantedName = some o_wantedValue ∧
      CoreEval.lookup updateEnv n_c_updateReplacementName = some replacement ∧
      CoreEval.lookup updateEnv n_c_updateListName = some n_c_updateList)
    (n_c_updateSelfBinding : CoreEval.lookup n_c_updateCaptureEnv.reverse n_c_updateChecked.functionName = some (.location n_c_updateSelfAddress))
    (n_c_updateComparisonBinding : CoreEval.lookup n_c_updateCaptureEnv.reverse n_c_updateChecked.comparisonName = some (.location n_c_updateComparisonAddress))
    (n_c_updateProjectionBinding : CoreEval.lookup n_c_updateCaptureEnv.reverse n_c_updateChecked.projectionName = some (.location n_c_updateProjectionAddress))
    (n_c_updateCaptureBindings : CaptureBindings o_program n_c_updateChecked.captureNodes n_c_updateCaptureValues n_c_updateCaptureEnv)
    (n_c_updateSelfResolution : ∀ (middle : Store), CommitFrame o_start middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → Resolve s n_c_updateSelfAddress n_c_updateSelfResolved)
    (n_c_updateSelfCell : ∀ (middle : Store), CommitFrame o_start middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → readCell s n_c_updateSelfResolved = some (.closureCode n_c_updateChecked.code :: n_c_updateCaptureValues))
    (n_c_updateComparisonResolution : ∀ (middle : Store), CommitFrame o_start middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → Resolve s n_c_updateComparisonAddress n_c_updateComparisonResolved)
    (n_c_updateComparisonCell : ∀ (middle : Store), CommitFrame o_start middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → readCell s n_c_updateComparisonResolved = some [.closureCode n_c_updateChecked.comparator.code])
    (n_c_updateProjectionResolution : ∀ (middle : Store), CommitFrame o_start middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → Resolve s n_c_updateProjectionAddress n_c_updateProjectionResolved)
    (n_c_updateProjectionCell : ∀ (middle : Store), CommitFrame o_start middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → readCell s n_c_updateProjectionResolved = some [.closureCode n_c_updateChecked.projectionCode])
    (n_c_updateWantedRep : ∀ (middle : Store), CommitFrame o_start middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → Ident o_recordsList s o_wantedValue o_wanted)
    (n_c_updateListRep : ∀ (middle : Store), CommitFrame o_start middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → Children o_recordsList s n_c_updateList o_records)
    (n_c_updateKeys : ∀ (middle : Store), CommitFrame o_start middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → RepresentedEntries o_recordsList (RecordEntry n_c_updateProjection.record) s o_key o_records)
    (n_c_outputChecked : Ash.NetworkLedger.CoreInsert.CheckedInsert n_c_outputsList o_program)
    (n_c_outputFunction : NodeId)
    (n_c_outputArgument : NodeId)
    (n_c_outputCall : NodeId)
    (n_c_outputListNode : NodeId)
    (n_c_outputConstructorFunction : NodeId)
    (n_c_outputConstructorArgument : NodeId)
    (n_c_outputChildNode : NodeId)
    (n_c_outputParentCall : NodeId)
    (n_c_outputDestinationNode : NodeId)
    (n_c_outputPayloadNode : NodeId)
    (n_c_outputParentFunction : NodeId)
    (n_c_outputParentArguments : NodeId)
    (n_c_outputOwnerNode : NodeId)
    (n_c_outputWantedNode : NodeId)
    (n_c_outputParentOperand : NodeId)
    (n_c_outputOperand : NodeId)
    (n_c_outputCallName : Binder)
    (n_c_outputListName : Binder)
    (n_c_outputChildName : Binder)
    (n_c_outputOwnerName : Binder)
    (n_c_outputWantedName : Binder)
    (n_c_outputDestinationName : Binder)
    (n_c_outputBytesName : Binder)
    (n_c_outputSelfAddress : Nat)
    (n_c_outputSelfResolved : Nat)
    (n_c_outputCaptureValues : List Value)
    (n_c_outputCaptureEnv : Environment)
    (n_c_outputOuterPair : CheckedTuple o_program n_c_outputArgument none [n_c_outputCall, n_c_outputListNode])
    (n_c_outputClosure : CheckedClosure o_program n_c_outputConstructorFunction)
    (n_c_outputConstructor : CheckedTuple o_program n_c_outputClosure.body (some n_c_workOutTag) [n_c_outputOperand])
    (n_c_outputTuple : CheckedTuple o_program n_c_outputConstructorArgument none [n_c_outputChildNode, n_c_outputParentCall, n_c_outputDestinationNode, n_c_outputPayloadNode])
    (n_c_outputParentClosure : CheckedClosure o_program n_c_outputParentFunction)
    (n_c_outputParentPair : CheckedTuple o_program n_c_outputParentArguments none [n_c_outputOwnerNode, n_c_outputWantedNode])
    (n_c_outputParentConstructor : CheckedTuple o_program n_c_outputParentClosure.body (some n_c_parentTag) [n_c_outputParentOperand])
    (n_c_outputCallShape : o_program n_c_outputNode = some (.apply n_c_outputFunction n_c_outputArgument))
    (n_c_outputFunctionShape : o_program n_c_outputFunction = some (.variable n_c_outputCallName))
    (n_c_outputListShape : o_program n_c_outputListNode = some (.variable n_c_outputListName))
    (n_c_outputListFresh : n_c_outputListName ≠ n_c_outputOuterPair.contextBinder)
    (n_c_outputShape : o_program n_c_outputCall = some (.apply n_c_outputConstructorFunction n_c_outputConstructorArgument))
    (n_c_outputOperandShape : o_program n_c_outputOperand = some (.variable n_c_outputClosure.parameter))
    (n_c_outputOperandFresh : n_c_outputClosure.parameter ≠ n_c_outputConstructor.contextBinder)
    (n_c_outputChildShape : o_program n_c_outputChildNode = some (.variable n_c_outputChildName))
    (n_c_outputParentShape : o_program n_c_outputParentCall = some (.apply n_c_outputParentFunction n_c_outputParentArguments))
    (n_c_outputOwnerShape : o_program n_c_outputOwnerNode = some (.variable n_c_outputOwnerName))
    (n_c_outputWantedShape : o_program n_c_outputWantedNode = some (.variable n_c_outputWantedName))
    (n_c_outputDestinationShape : o_program n_c_outputDestinationNode = some (.variable n_c_outputDestinationName))
    (n_c_outputBytesShape : o_program n_c_outputPayloadNode = some (.variable n_c_outputBytesName))
    (n_c_outputChildOuterFresh : n_c_outputChildName ≠ n_c_outputOuterPair.contextBinder)
    (n_c_outputOwnerOuterFresh : n_c_outputOwnerName ≠ n_c_outputOuterPair.contextBinder)
    (n_c_outputWantedOuterFresh : n_c_outputWantedName ≠ n_c_outputOuterPair.contextBinder)
    (n_c_outputDestinationOuterFresh : n_c_outputDestinationName ≠ n_c_outputOuterPair.contextBinder)
    (n_c_outputBytesOuterFresh : n_c_outputBytesName ≠ n_c_outputOuterPair.contextBinder)
    (n_c_outputChildFresh : n_c_outputChildName ≠ n_c_outputTuple.contextBinder)
    (n_c_outputOwnerFresh : n_c_outputOwnerName ≠ n_c_outputTuple.contextBinder)
    (n_c_outputWantedFresh : n_c_outputWantedName ≠ n_c_outputTuple.contextBinder)
    (n_c_outputDestinationFresh : n_c_outputDestinationName ≠ n_c_outputTuple.contextBinder)
    (n_c_outputBytesFresh : n_c_outputBytesName ≠ n_c_outputTuple.contextBinder)
    (n_c_outputOwnerParentFresh : n_c_outputOwnerName ≠ n_c_outputParentPair.contextBinder)
    (n_c_outputWantedParentFresh : n_c_outputWantedName ≠ n_c_outputParentPair.contextBinder)
    (n_c_outputParentOperandShape : o_program n_c_outputParentOperand = some (.variable n_c_outputParentClosure.parameter))
    (n_c_outputParentOperandFresh : n_c_outputParentClosure.parameter ≠ n_c_outputParentConstructor.contextBinder)
    (n_c_outputList : Value)
    (n_c_outputBindings : ∀ (middle : Store), CommitFrame o_start middle → ∀ (s : Store) (p : Nat), CommitFrame middle s → ∀ work replacement remaining,
      let outputEnv := extend (extend (extend ((List.zip n_f_commitNames (n_f_commitNodes.map n_f_commitFieldValue)).reverse ++ extend n_f_commitCaptureEnv.reverse n_f_commitParameter (.location p)) n_c_workName work) n_c_replacementName replacement) n_c_remainingName remaining
      CoreEval.lookup outputEnv n_c_outputCallName = some (.location n_c_outputSelfAddress) ∧
      CoreEval.lookup outputEnv n_c_outputListName = some n_c_outputList ∧
      CoreEval.lookup outputEnv n_c_outputChildName = some work ∧
      CoreEval.lookup outputEnv n_c_outputOwnerName = some (.integer (Int.ofNat n_c_owner)) ∧
      CoreEval.lookup outputEnv n_c_outputWantedName = some o_wantedValue ∧
      CoreEval.lookup outputEnv n_c_outputDestinationName = some n_c_destination ∧
      CoreEval.lookup outputEnv n_c_outputBytesName = some n_c_bytes)
    (n_c_outputSelfBinding : CoreEval.lookup n_c_outputCaptureEnv.reverse n_c_outputChecked.functionName = some (.location n_c_outputSelfAddress))
    (n_c_outputCaptureBindings : CaptureBindings o_program n_c_outputChecked.captureNodes n_c_outputCaptureValues n_c_outputCaptureEnv)
    (n_c_outputSelfResolution : ∀ (middle : Store), CommitFrame o_start middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → Resolve s n_c_outputSelfAddress n_c_outputSelfResolved)
    (n_c_outputSelfCell : ∀ (middle : Store), CommitFrame o_start middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → readCell s n_c_outputSelfResolved = some (.closureCode n_c_outputChecked.code :: n_c_outputCaptureValues))
    (n_c_outputListRep : ∀ (middle : Store), CommitFrame o_start middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → Children n_c_outputsList s n_c_outputList n_c_outputs)
    (n_c_outputLocated : Ash.NetworkLedger.CoreGenericInsert.LocatedEntries n_c_outputs)
    (n_c_counterBinding : ∀ (middle : Store), CommitFrame o_start middle → ∀ (s : Store) (p : Nat), CommitFrame middle s → CoreEval.lookup ((List.zip n_f_commitNames (n_f_commitNodes.map n_f_commitFieldValue)).reverse ++ extend n_f_commitCaptureEnv.reverse n_f_commitParameter (.location p)) n_c_checkedResult.increment.counterBinder = some (.integer n_c_counter))
    (n_c_remainingBinder : n_c_checkedResult.remainingName = n_c_remainingName)
    (n_c_outgoingBinder : n_c_checkedResult.outgoingName = n_c_outgoingName)
    (n_c_childBinder : n_c_checkedResult.childName = n_c_workName)
    (n_c_counterWork : n_c_checkedResult.increment.counterBinder ≠ n_c_workName)
    (n_c_counterReplacement : n_c_checkedResult.increment.counterBinder ≠ n_c_replacementName)
    (n_c_counterRemaining : n_c_checkedResult.increment.counterBinder ≠ n_c_remainingName)
    (n_c_counterOutgoing : n_c_checkedResult.increment.counterBinder ≠ n_c_outgoingName)
    (n_c_workReplacement : n_c_workName ≠ n_c_replacementName)
    (n_c_workRemaining : n_c_workName ≠ n_c_remainingName)
    (n_c_workOutgoing : n_c_workName ≠ n_c_outgoingName)
    (n_c_remainingOutgoing : n_c_remainingName ≠ n_c_outgoingName)
    (n_c_noParent : Constructor)
    (n_c_ackOutTag : Constructor)
    (n_c_rejectedTag : Constructor)
    (n_c_bytesRep : Value → List UInt8 → Prop)
    (n_c_ledger : Ledger)
    (n_c_destinationNat : Nat)
    (n_c_payload : List UInt8)
    (n_c_ownerEq : n_c_ledger.owner = n_c_owner)
    (n_c_counterEq : n_c_ledger.next = n_c_counter)
    (n_c_destinationEq : n_c_destination = .integer (Int.ofNat n_c_destinationNat))
    (n_c_rootSame : o_recordsList.root = n_c_ids.root)
    (n_c_workSame : o_recordsList.work = n_c_ids.work)
    (n_c_recordTagSame : n_c_updateProjection.record = n_f_recordTag)
    (n_c_semanticRecords : ∀ (middle : Store), CommitFrame o_start middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → RelatedValues (DecodedRecord n_c_ids n_f_recordTag n_c_noParent n_c_parentTag n_f_openTag n_f_closedTag s) o_records n_c_ledger.records)
    (n_c_semanticOutputs : ∀ (middle : Store), CommitFrame o_start middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → RelatedValues (DecodedOutput n_c_ids n_c_noParent n_c_parentTag n_c_workOutTag n_c_ackOutTag n_c_bytesRep s) n_c_outputs n_c_ledger.outputs)
    (n_c_bytesMeaning : n_c_bytesRep n_c_bytes n_c_payload)
    :
    DecodedRegistrationResult n_c_ids o_recordsList n_c_outputsList n_c_checkedResult.ledgerTag n_f_recordTag n_c_noParent n_c_parentTag n_f_openTag n_f_closedTag
      n_c_workOutTag n_c_ackOutTag n_c_rejectedTag n_c_checkedResult.registeredTag n_c_bytesRep o_finish o_result
      (Ash.NetworkLedger.register n_c_ledger o_wanted n_c_destinationNat n_c_payload) := by
  obtain ⟨middle, frame, bodyEval⟩ := checked_lookup_hit_branch o_recordsList o_program o_absent o_present o_checked o_projection o_projectionFunctionName o_projectionEntryName o_projectionCode o_branch o_call o_missingBody o_foundBody o_function o_argument o_wantedNode o_listNode o_name o_callName o_wantedName o_listName o_env o_start o_finish o_result o_wantedValue o_list o_found o_wanted o_records o_key o_selfAddress o_selfResolved o_comparisonAddress o_comparisonResolved o_projectionAddress o_projectionResolved o_captureValues o_captureEnv o_branchShape o_lookupPair o_callShape o_functionShape o_functionBinding o_wantedShape o_listShape o_wantedFresh o_listFresh o_wantedBinding o_listBinding o_selfBinding o_comparisonBinding o_projectionBinding o_captureBindings o_selfResolution o_selfCell o_comparisonResolution o_comparisonCell o_projectionResolution o_projectionCell o_bounded o_wantedRep o_listRep o_lookupKeys o_actualLookup o_evaluation
  exact checked_finish_open_registration o_program o_foundBody n_f_function n_f_argument n_f_nodes (extend o_env o_name o_found) middle o_finish o_result n_f_functionName n_f_address n_f_resolved n_f_code n_f_context n_f_storage n_f_parameter n_f_body n_f_captureNodes n_f_captureValues n_f_captureEnv n_f_fieldValue n_f_tuple n_f_callShape n_f_functionShape n_f_functionBinding (n_f_resolution middle frame) (n_f_cell middle frame) n_f_closureShape n_f_captureBindings n_f_fieldShapes n_f_scrutinee n_f_recordMatch n_f_recordScrutinee n_f_phaseBranch n_f_names n_f_recordNames n_f_recordName n_f_recordTag n_f_openTag n_f_closedTag o_found n_f_foundKey n_f_parent n_f_phase n_f_children n_f_bodyShape n_f_scrutineeShape n_f_arity n_f_plain n_f_recordShape n_f_recordScrutineeShape n_f_recordBinding n_f_recordArity (n_f_recordRep middle frame) n_f_recordPlain n_f_phaseAddress n_f_phaseResolved n_f_phaseEq (n_f_phaseResolution middle frame) (n_f_phaseCell middle frame) n_f_different n_f_phaseNode n_f_closedBody n_f_commitCall n_f_phaseName n_f_phaseShape n_f_phaseNodeShape n_f_phaseBinding n_f_commitFunction n_f_commitArgument n_f_commitScrutinee n_f_commitArm n_f_commitNodes n_f_commitName n_f_commitAddress n_f_commitResolved n_f_commitCode n_f_commitContext n_f_commitStorage n_f_commitParameter n_f_commitBody n_f_commitCaptureNodes n_f_commitCaptureValues n_f_commitCaptureEnv n_f_commitFieldValue n_f_commitTuple n_f_commitCallShape n_f_commitFunctionShape n_f_commitBinding (n_f_commitResolution middle frame) (n_f_commitCell middle frame) n_f_commitClosureShape n_f_commitCaptureBindings n_f_commitFieldShapes n_f_commitNames n_f_commitBodyShape n_f_commitScrutineeShape n_f_commitArity n_f_commitPlain (n_f_bounded middle frame) bodyEval n_c_ids o_recordsList n_c_outputsList n_c_buffers n_c_checkedResult n_c_second n_c_third n_c_fourth n_c_workNode n_c_replacementNode n_c_updateNode n_c_outputNode n_c_workName n_c_replacementName n_c_remainingName n_c_outgoingName n_c_workOutTag n_c_parentTag o_wantedValue n_c_destination n_c_bytes n_c_owner n_c_counter o_wanted o_key n_c_children o_records n_c_outputs n_c_firstShape n_c_secondShape n_c_thirdShape n_c_fourthShape n_c_nonnegative n_c_workFunction n_c_workArgument n_c_workOwnerNode n_c_workCounterNode n_c_workOperand n_c_workOwnerName n_c_workClosure n_c_workPair n_c_workConstructor n_c_workCallShape n_c_workOwnerShape n_c_workCounterShape n_c_workOwnerFresh n_c_workCounterFresh (n_c_workOwnerBinding middle frame) n_c_workOperandShape n_c_workOperandFresh n_c_childChecked n_c_replacementFunction n_c_replacementArgument n_c_replacementWantedNode n_c_replacementParentNode n_c_replacementOpenNode n_c_childAppendNode n_c_replacementOperand n_c_childFunction n_c_childArgument n_c_childCall n_c_childListNode n_c_childConstructorFunction n_c_childConstructorArgument n_c_childIdNode n_c_childDestinationNode n_c_childOperand n_c_replacementWantedName n_c_replacementParentName n_c_childCallName n_c_childListName n_c_childIdName n_c_childDestinationName n_c_childSelfAddress n_c_childSelfResolved n_c_childCaptureValues n_c_childCaptureEnv n_c_replacementClosure n_c_replacementConstructor n_c_replacementTuple n_c_replacementOpenTuple n_c_childOuterPair n_c_childClosure n_c_childPair n_c_childConstructor n_c_replacementCallShape n_c_replacementOperandShape n_c_replacementOperandFresh n_c_replacementWantedShape n_c_replacementParentShape n_c_replacementWantedFresh n_c_replacementParentFresh n_c_childAppendShape n_c_childFunctionShape n_c_childListShape n_c_childListFresh n_c_childCallShape n_c_childIdShape n_c_childDestinationShape n_c_childIdOuterFresh n_c_childDestinationOuterFresh n_c_childIdFresh n_c_childDestinationFresh n_c_childOperandShape n_c_childOperandFresh (n_c_replacementBindings middle frame) (n_c_childBindings middle frame) n_c_childSelfBinding n_c_childCaptureBindings (n_c_childSelfResolution middle frame) (n_c_childSelfCell middle frame) (n_c_childListRep middle frame) n_c_childLocated n_c_updateChecked n_c_updateProjection n_c_updateProjectionName n_c_updateEntryName n_c_updateProjectionCode n_c_updateFunction n_c_updateArgument n_c_updateWantedNode n_c_updateReplacementNode n_c_updateListNode n_c_updateCallName n_c_updateWantedName n_c_updateReplacementName n_c_updateListName n_c_updateSelfAddress n_c_updateSelfResolved n_c_updateComparisonAddress n_c_updateComparisonResolved n_c_updateProjectionAddress n_c_updateProjectionResolved n_c_updateCaptureValues n_c_updateCaptureEnv n_c_updateTriple n_c_updateCallShape n_c_updateFunctionShape n_c_updateWantedShape n_c_updateReplacementShape n_c_updateListShape n_c_updateWantedFresh n_c_updateReplacementFresh n_c_updateListFresh n_c_updateList (n_c_updateBindings middle frame) n_c_updateSelfBinding n_c_updateComparisonBinding n_c_updateProjectionBinding n_c_updateCaptureBindings (n_c_updateSelfResolution middle frame) (n_c_updateSelfCell middle frame) (n_c_updateComparisonResolution middle frame) (n_c_updateComparisonCell middle frame) (n_c_updateProjectionResolution middle frame) (n_c_updateProjectionCell middle frame) (n_c_updateWantedRep middle frame) (n_c_updateListRep middle frame) (n_c_updateKeys middle frame) n_c_outputChecked n_c_outputFunction n_c_outputArgument n_c_outputCall n_c_outputListNode n_c_outputConstructorFunction n_c_outputConstructorArgument n_c_outputChildNode n_c_outputParentCall n_c_outputDestinationNode n_c_outputPayloadNode n_c_outputParentFunction n_c_outputParentArguments n_c_outputOwnerNode n_c_outputWantedNode n_c_outputParentOperand n_c_outputOperand n_c_outputCallName n_c_outputListName n_c_outputChildName n_c_outputOwnerName n_c_outputWantedName n_c_outputDestinationName n_c_outputBytesName n_c_outputSelfAddress n_c_outputSelfResolved n_c_outputCaptureValues n_c_outputCaptureEnv n_c_outputOuterPair n_c_outputClosure n_c_outputConstructor n_c_outputTuple n_c_outputParentClosure n_c_outputParentPair n_c_outputParentConstructor n_c_outputCallShape n_c_outputFunctionShape n_c_outputListShape n_c_outputListFresh n_c_outputShape n_c_outputOperandShape n_c_outputOperandFresh n_c_outputChildShape n_c_outputParentShape n_c_outputOwnerShape n_c_outputWantedShape n_c_outputDestinationShape n_c_outputBytesShape n_c_outputChildOuterFresh n_c_outputOwnerOuterFresh n_c_outputWantedOuterFresh n_c_outputDestinationOuterFresh n_c_outputBytesOuterFresh n_c_outputChildFresh n_c_outputOwnerFresh n_c_outputWantedFresh n_c_outputDestinationFresh n_c_outputBytesFresh n_c_outputOwnerParentFresh n_c_outputWantedParentFresh n_c_outputParentOperandShape n_c_outputParentOperandFresh n_c_outputList (n_c_outputBindings middle frame) n_c_outputSelfBinding n_c_outputCaptureBindings (n_c_outputSelfResolution middle frame) (n_c_outputSelfCell middle frame) (n_c_outputListRep middle frame) n_c_outputLocated (n_c_counterBinding middle frame) n_c_remainingBinder n_c_outgoingBinder n_c_childBinder n_c_counterWork n_c_counterReplacement n_c_counterRemaining n_c_counterOutgoing n_c_workReplacement n_c_workRemaining n_c_workOutgoing n_c_remainingOutgoing n_c_noParent n_c_ackOutTag n_c_rejectedTag n_c_bytesRep n_c_ledger n_c_destinationNat n_c_payload n_c_ownerEq n_c_counterEq n_c_destinationEq n_c_rootSame n_c_workSame n_c_recordTagSame (n_c_semanticRecords middle frame) (n_c_semanticOutputs middle frame) n_c_bytesMeaning o_actualLookup

/-- The actual lookup hit and stored finish call return the closed registration result. -/
theorem checked_lookup_finish_closed_registration
    (o_recordsList : Constructors)
    (o_program : Program)
    (o_absent o_present : Constructor)
    (o_checked : CheckedLookupBase o_recordsList o_program o_absent o_present)
    (o_projection : RecordProjectionShape o_program o_checked.projection)
    (o_projectionFunctionName : o_projection.functionName = o_checked.projectionName)
    (o_projectionEntryName : o_projection.recordName = o_checked.entryName)
    (o_projectionCode : o_projection.code = o_checked.projectionCode)
    (o_branch o_call o_missingBody o_foundBody o_function o_argument o_wantedNode o_listNode : NodeId)
    (o_name o_callName o_wantedName o_listName : Binder)
    (o_env : Environment)
    (o_start o_finish : Store)
    (o_result o_wantedValue o_list o_found : Value)
    (o_wanted : Id)
    (o_records : List Value)
    (o_key : Value → Id)
    (o_selfAddress o_selfResolved o_comparisonAddress o_comparisonResolved o_projectionAddress o_projectionResolved : Nat)
    (o_captureValues : List Value)
    (o_captureEnv : Environment)
    (o_branchShape : o_program o_branch = some (.caseMatch o_call
      [(.constructor o_absent none, o_missingBody), (.constructor o_present (some (.binder o_name)), o_foundBody)]))
    (o_lookupPair : CheckedTuple o_program o_argument none [o_wantedNode, o_listNode])
    (o_callShape : o_program o_call = some (.apply o_function o_argument))
    (o_functionShape : o_program o_function = some (.variable o_callName))
    (o_functionBinding : CoreEval.lookup o_env o_callName = some (.location o_selfAddress))
    (o_wantedShape : o_program o_wantedNode = some (.variable o_wantedName))
    (o_listShape : o_program o_listNode = some (.variable o_listName))
    (o_wantedFresh : o_wantedName ≠ o_lookupPair.contextBinder)
    (o_listFresh : o_listName ≠ o_lookupPair.contextBinder)
    (o_wantedBinding : CoreEval.lookup o_env o_wantedName = some o_wantedValue)
    (o_listBinding : CoreEval.lookup o_env o_listName = some o_list)
    (o_selfBinding : CoreEval.lookup o_captureEnv.reverse o_checked.functionName = some (.location o_selfAddress))
    (o_comparisonBinding : CoreEval.lookup o_captureEnv.reverse o_checked.comparisonName = some (.location o_comparisonAddress))
    (o_projectionBinding : CoreEval.lookup o_captureEnv.reverse o_checked.projectionName = some (.location o_projectionAddress))
    (o_captureBindings : CaptureBindings o_program o_checked.captureNodes o_captureValues o_captureEnv)
    (o_selfResolution : Resolve o_start o_selfAddress o_selfResolved)
    (o_selfCell : readCell o_start o_selfResolved = some (.closureCode o_checked.code :: o_captureValues))
    (o_comparisonResolution : Resolve o_start o_comparisonAddress o_comparisonResolved)
    (o_comparisonCell : readCell o_start o_comparisonResolved = some [.closureCode o_checked.comparator.code])
    (o_projectionResolution : Resolve o_start o_projectionAddress o_projectionResolved)
    (o_projectionCell : readCell o_start o_projectionResolved = some [.closureCode o_checked.projectionCode])
    (o_bounded : BoundedLocations o_start)
    (o_wantedRep : Ident o_recordsList o_start o_wantedValue o_wanted)
    (o_listRep : Children o_recordsList o_start o_list o_records)
    (o_lookupKeys : RepresentedEntries o_recordsList (RecordEntry o_projection.record) o_start o_key o_records)
    (o_actualLookup : Ash.NetworkLedger.lookup o_key o_wanted o_records = some o_found)
    (o_evaluation : Eval o_program o_env o_branch o_start o_result o_finish)
    (n_ids : Constructors)
    (n_outputsList : Constructors)
    (n_ledgerTag : Constructor)
    (n_recordTag : Constructor)
    (n_noParent : Constructor)
    (n_parentTag : Constructor)
    (n_openTag : Constructor)
    (n_closedTag : Constructor)
    (n_workOutTag : Constructor)
    (n_ackOutTag : Constructor)
    (n_rejectedTag : Constructor)
    (n_registeredTag : Constructor)
    (n_bytesRep : Value → List UInt8 → Prop)
    (n_function : NodeId)
    (n_argument : NodeId)
    (n_nodes : List NodeId)
    (n_functionName : Binder)
    (n_address : Nat)
    (n_resolved : Nat)
    (n_code : Nat)
    (n_context : Nat)
    (n_storage : Nat)
    (n_parameter : Nat)
    (n_body : Nat)
    (n_captureNodes : List NodeId)
    (n_captureValues : List Value)
    (n_captureEnv : Environment)
    (n_fieldValue : NodeId → Value)
    (n_tuple : CheckedTuple o_program n_argument none n_nodes)
    (n_callShape : o_program o_foundBody = some (.apply n_function n_argument))
    (n_functionShape : o_program n_function = some (.variable n_functionName))
    (n_functionBinding : CoreEval.lookup (extend o_env o_name o_found) n_functionName = some (.location n_address))
    (n_resolution : ∀ (middle : Store), CommitFrame o_start middle → Resolve middle n_address n_resolved)
    (n_cell : ∀ (middle : Store), CommitFrame o_start middle → readCell middle n_resolved = some (.closureCode n_code :: n_captureValues))
    (n_closureShape : o_program n_code = some (.closure n_context n_captureNodes n_storage n_parameter n_body))
    (n_captureBindings : CaptureBindings o_program n_captureNodes n_captureValues n_captureEnv)
    (n_fieldShapes : ∀ node ∈ n_nodes, ∃ name, o_program node = some (.variable name) ∧
      CoreEval.lookup (extend (extend o_env o_name o_found) n_tuple.contextBinder .context) name = some (n_fieldValue node))
    (n_scrutinee : NodeId)
    (n_recordMatch : NodeId)
    (n_recordScrutinee : NodeId)
    (n_phaseBranch : NodeId)
    (n_names : List Binder)
    (n_recordNames : List Binder)
    (n_recordName : Binder)
    (n_foundKey : Value)
    (n_parent : Value)
    (n_phase : Value)
    (n_childList : Value)
    (n_ledgerValue : Value)
    (n_ledger : Ledger)
    (n_bodyShape : o_program n_body = some (.caseMatch n_scrutinee [(.tuple (n_names.map Pattern.binder), n_recordMatch)]))
    (n_scrutineeShape : o_program n_scrutinee = some (.variable n_parameter))
    (n_arity : n_names.length = (n_nodes.map n_fieldValue).length)
    (n_plain : tupleFields (n_nodes.map n_fieldValue) = some (n_nodes.map n_fieldValue))
    (n_recordShape : o_program n_recordMatch = some (.caseMatch n_recordScrutinee
      [(.constructor n_recordTag (some (.tuple (n_recordNames.map Pattern.binder))), n_phaseBranch)]))
    (n_recordScrutineeShape : o_program n_recordScrutinee = some (.variable n_recordName))
    (n_recordBinding : ∀ payload, CoreEval.lookup ((List.zip n_names (n_nodes.map n_fieldValue)).reverse ++
      extend n_captureEnv.reverse n_parameter (.location payload)) n_recordName = some o_found)
    (n_recordArity : n_recordNames.length = 4)
    (n_recordRep : ∀ (middle : Store), CommitFrame o_start middle → NominalFields n_recordTag middle o_found [n_foundKey, n_parent, n_phase, n_childList])
    (n_recordPlain : tupleFields [n_foundKey, n_parent, n_phase, n_childList] = some [n_foundKey, n_parent, n_phase, n_childList])
    (n_destination : Nat)
    (n_payloadBytes : List UInt8)
    (n_phaseAddress : Nat)
    (n_phaseResolved : Nat)
    (n_phaseEq : n_phase = .location n_phaseAddress)
    (n_phaseResolution : ∀ (middle : Store), CommitFrame o_start middle → Resolve middle n_phaseAddress n_phaseResolved)
    (n_phaseCell : ∀ (middle : Store), CommitFrame o_start middle → readCell middle n_phaseResolved = some [.tag n_closedTag])
    (n_rootSame : o_recordsList.root = n_ids.root)
    (n_workSame : o_recordsList.work = n_ids.work)
    (n_different : n_openTag ≠ n_closedTag)
    (n_represented : ∀ (middle : Store), CommitFrame o_start middle → RepresentedEntries o_recordsList (RecordEntry n_recordTag) middle o_key o_records)
    (n_recordValues : ∀ (middle : Store), CommitFrame o_start middle → RelatedValues (DecodedRecord n_ids n_recordTag n_noParent n_parentTag n_openTag n_closedTag middle) o_records n_ledger.records)
    (n_phaseNode : NodeId)
    (n_closedBody : NodeId)
    (n_openBody : NodeId)
    (n_ledgerNode : NodeId)
    (n_statusNode : NodeId)
    (n_phaseName : Binder)
    (n_ledgerName : Binder)
    (n_phaseShape : o_program n_phaseBranch = some (.caseMatch n_phaseNode
      [(.constructor n_closedTag none, n_closedBody), (.constructor n_openTag none, n_openBody)]))
    (n_phaseNodeShape : o_program n_phaseNode = some (.variable n_phaseName))
    (n_phaseBinding : ∀ payload, CoreEval.lookup ((List.zip n_recordNames [n_foundKey, n_parent, n_phase, n_childList]).reverse ++
      ((List.zip n_names (n_nodes.map n_fieldValue)).reverse ++ extend n_captureEnv.reverse n_parameter (.location payload))) n_phaseName = some n_phase)
    (n_resultPair : CheckedTuple o_program n_closedBody none [n_ledgerNode, n_statusNode])
    (n_status : CheckedTuple o_program n_statusNode (some n_rejectedTag) [])
    (n_ledgerShape : o_program n_ledgerNode = some (.variable n_ledgerName))
    (n_ledgerFresh : n_ledgerName ≠ n_resultPair.contextBinder)
    (n_ledgerBinding : ∀ payload, CoreEval.lookup ((List.zip n_recordNames [n_foundKey, n_parent, n_phase, n_childList]).reverse ++
      ((List.zip n_names (n_nodes.map n_fieldValue)).reverse ++ extend n_captureEnv.reverse n_parameter (.location payload))) n_ledgerName = some n_ledgerValue)
    (n_ledgerRep : ∀ (middle : Store), CommitFrame o_start middle → DecodedLedger n_ids o_recordsList n_outputsList n_ledgerTag n_recordTag n_noParent n_parentTag n_openTag n_closedTag n_workOutTag n_ackOutTag
      n_bytesRep middle n_ledgerValue n_ledger)
    :
    DecodedRegistrationResult n_ids o_recordsList n_outputsList n_ledgerTag n_recordTag n_noParent n_parentTag n_openTag n_closedTag n_workOutTag n_ackOutTag
      n_rejectedTag n_registeredTag n_bytesRep o_finish o_result (Ash.NetworkLedger.register n_ledger o_wanted n_destination n_payloadBytes) := by
  obtain ⟨middle, frame, bodyEval⟩ := checked_lookup_hit_branch o_recordsList o_program o_absent o_present o_checked o_projection o_projectionFunctionName o_projectionEntryName o_projectionCode o_branch o_call o_missingBody o_foundBody o_function o_argument o_wantedNode o_listNode o_name o_callName o_wantedName o_listName o_env o_start o_finish o_result o_wantedValue o_list o_found o_wanted o_records o_key o_selfAddress o_selfResolved o_comparisonAddress o_comparisonResolved o_projectionAddress o_projectionResolved o_captureValues o_captureEnv o_branchShape o_lookupPair o_callShape o_functionShape o_functionBinding o_wantedShape o_listShape o_wantedFresh o_listFresh o_wantedBinding o_listBinding o_selfBinding o_comparisonBinding o_projectionBinding o_captureBindings o_selfResolution o_selfCell o_comparisonResolution o_comparisonCell o_projectionResolution o_projectionCell o_bounded o_wantedRep o_listRep o_lookupKeys o_actualLookup o_evaluation
  exact checked_finish_closed n_ids o_recordsList n_outputsList n_ledgerTag n_recordTag n_noParent n_parentTag n_openTag n_closedTag n_workOutTag n_ackOutTag n_rejectedTag n_registeredTag n_bytesRep o_program o_foundBody n_function n_argument n_nodes (extend o_env o_name o_found) middle o_finish o_result n_functionName n_address n_resolved n_code n_context n_storage n_parameter n_body n_captureNodes n_captureValues n_captureEnv n_fieldValue n_tuple n_callShape n_functionShape n_functionBinding (n_resolution middle frame) (n_cell middle frame) n_closureShape n_captureBindings n_fieldShapes n_scrutinee n_recordMatch n_recordScrutinee n_phaseBranch n_names n_recordNames n_recordName o_found n_foundKey n_parent n_phase n_childList n_ledgerValue n_ledger n_bodyShape n_scrutineeShape n_arity n_plain n_recordShape n_recordScrutineeShape n_recordBinding n_recordArity (n_recordRep middle frame) n_recordPlain o_wanted n_destination n_payloadBytes o_records o_key n_phaseAddress n_phaseResolved n_phaseEq (n_phaseResolution middle frame) (n_phaseCell middle frame) n_rootSame n_workSame n_different (n_represented middle frame) (n_recordValues middle frame) o_actualLookup n_phaseNode n_closedBody n_openBody n_ledgerNode n_statusNode n_phaseName n_ledgerName n_phaseShape n_phaseNodeShape n_phaseBinding n_resultPair n_status n_ledgerShape n_ledgerFresh n_ledgerBinding frame.2.1 (n_ledgerRep middle frame) bodyEval

/-- The stored entry call matches the actual three-field Ledger before lookup. -/
theorem checked_registration_entry_call (program : Program) (call function argument : NodeId)
    (nodes : List NodeId) (env : Environment) (start finish : Store) (result : Value)
    (functionName : Binder) (address resolved code context storage parameter body : Nat)
    (captureNodes : List NodeId) (captureValues : List Value) (captureEnv : Environment)
    (fieldValue : NodeId → Value) (tuple : CheckedTuple program argument none nodes)
    (callShape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable functionName))
    (functionBinding : CoreEval.lookup env functionName = some (.location address))
    (resolution : Resolve start address resolved)
    (cell : readCell start resolved = some (.closureCode code :: captureValues))
    (closureShape : program code = some (.closure context captureNodes storage parameter body))
    (captureBindings : CaptureBindings program captureNodes captureValues captureEnv)
    (fieldShapes : ∀ node ∈ nodes, ∃ name, program node = some (.variable name) ∧
      CoreEval.lookup (extend env tuple.contextBinder .context) name = some (fieldValue node))
    (scrutinee ledgerMatch ledgerScrutinee lookupBranch : NodeId) (names ledgerNames : List Binder)
    (ledgerName : Binder) (ledgerTag : Constructor) (ledger nextValue recordsValue outputsValue : Value)
    (bodyShape : program body = some (.caseMatch scrutinee [(.tuple (names.map Pattern.binder), ledgerMatch)]))
    (scrutineeShape : program scrutinee = some (.variable parameter))
    (arity : names.length = (nodes.map fieldValue).length)
    (plain : tupleFields (nodes.map fieldValue) = some (nodes.map fieldValue))
    (ledgerShape : program ledgerMatch = some (.caseMatch ledgerScrutinee
      [(.constructor ledgerTag (some (.tuple (ledgerNames.map Pattern.binder))), lookupBranch)]))
    (ledgerScrutineeShape : program ledgerScrutinee = some (.variable ledgerName))
    (ledgerBinding : ∀ payload,
      CoreEval.lookup ((List.zip names (nodes.map fieldValue)).reverse ++
        extend captureEnv.reverse parameter (.location payload)) ledgerName = some ledger)
    (ledgerArity : ledgerNames.length = 3)
    (ledgerRep : NominalFields ledgerTag start ledger [nextValue, recordsValue, outputsValue])
    (ledgerPlain : tupleFields [nextValue, recordsValue, outputsValue] = some [nextValue, recordsValue, outputsValue])
    (bounded : BoundedLocations start) (evaluation : Eval program env call start result finish) :
    ∃ afterArgument payload, CommitFrame start afterArgument ∧
      Eval program ((List.zip ledgerNames [nextValue, recordsValue, outputsValue]).reverse ++
        ((List.zip names (nodes.map fieldValue)).reverse ++ extend captureEnv.reverse parameter (.location payload)))
        lookupBranch afterArgument result finish := by
  obtain ⟨afterArgument, payload, frame, ledgerEval⟩ :=
    checked_forwarded_body program call function argument nodes env start finish result functionName address resolved code context storage
      parameter body captureNodes captureValues captureEnv fieldValue tuple callShape functionShape functionBinding resolution cell closureShape
      captureBindings fieldShapes scrutinee ledgerMatch names bodyShape scrutineeShape arity plain bounded evaluation
  have retainedLedger := nominal_fields_retained ledgerTag start afterArgument ledger _ frame.1 frame.2.2 ledgerRep
  refine ⟨afterArgument, payload, frame, ?_⟩
  exact checked_nominal_match program ledgerMatch ledgerScrutinee lookupBranch ledgerName ledgerTag ledgerNames
    [nextValue, recordsValue, outputsValue] _ afterArgument finish result ledger ledgerShape ledgerScrutineeShape (ledgerBinding payload)
    (by simpa using ledgerArity) retainedLedger ledgerPlain ledgerEval

/-- The actual entry and missing lookup branch return the decoded rejection. -/
theorem checked_entry_missing_registration
    (e_program : Program)
    (e_call e_function e_argument : NodeId)
    (e_nodes : List NodeId)
    (e_env : Environment)
    (e_start e_finish : Store)
    (e_result : Value)
    (e_functionName : Binder)
    (e_address e_resolved e_code e_context e_storage e_parameter e_body : Nat)
    (e_captureNodes : List NodeId)
    (e_captureValues : List Value)
    (e_captureEnv : Environment)
    (e_fieldValue : NodeId → Value)
    (e_tuple : CheckedTuple e_program e_argument none e_nodes)
    (e_callShape : e_program e_call = some (.apply e_function e_argument))
    (e_functionShape : e_program e_function = some (.variable e_functionName))
    (e_functionBinding : CoreEval.lookup e_env e_functionName = some (.location e_address))
    (e_resolution : Resolve e_start e_address e_resolved)
    (e_cell : readCell e_start e_resolved = some (.closureCode e_code :: e_captureValues))
    (e_closureShape : e_program e_code = some (.closure e_context e_captureNodes e_storage e_parameter e_body))
    (e_captureBindings : CaptureBindings e_program e_captureNodes e_captureValues e_captureEnv)
    (e_fieldShapes : ∀ node ∈ e_nodes, ∃ name, e_program node = some (.variable name) ∧
      CoreEval.lookup (extend e_env e_tuple.contextBinder .context) name = some (e_fieldValue node))
    (e_scrutinee e_ledgerMatch e_ledgerScrutinee e_lookupBranch : NodeId)
    (e_names e_ledgerNames : List Binder)
    (e_ledgerName : Binder)
    (e_ledgerTag : Constructor)
    (e_ledger e_nextValue e_recordsValue e_outputsValue : Value)
    (e_bodyShape : e_program e_body = some (.caseMatch e_scrutinee [(.tuple (e_names.map Pattern.binder), e_ledgerMatch)]))
    (e_scrutineeShape : e_program e_scrutinee = some (.variable e_parameter))
    (e_arity : e_names.length = (e_nodes.map e_fieldValue).length)
    (e_plain : tupleFields (e_nodes.map e_fieldValue) = some (e_nodes.map e_fieldValue))
    (e_ledgerShape : e_program e_ledgerMatch = some (.caseMatch e_ledgerScrutinee
      [(.constructor e_ledgerTag (some (.tuple (e_ledgerNames.map Pattern.binder))), e_lookupBranch)]))
    (e_ledgerScrutineeShape : e_program e_ledgerScrutinee = some (.variable e_ledgerName))
    (e_ledgerBinding : ∀ payload,
      CoreEval.lookup ((List.zip e_names (e_nodes.map e_fieldValue)).reverse ++
        extend e_captureEnv.reverse e_parameter (.location payload)) e_ledgerName = some e_ledger)
    (e_ledgerArity : e_ledgerNames.length = 3)
    (e_ledgerRep : NominalFields e_ledgerTag e_start e_ledger [e_nextValue, e_recordsValue, e_outputsValue])
    (e_ledgerPlain : tupleFields [e_nextValue, e_recordsValue, e_outputsValue] = some [e_nextValue, e_recordsValue, e_outputsValue])
    (e_bounded : BoundedLocations e_start)
    (e_evaluation : Eval e_program e_env e_call e_start e_result e_finish)
    (m_ids : Constructors)
    (m_recordsList : Constructors)
    (m_outputsList : Constructors)
    (m_recordTag : Constructor)
    (m_noParent : Constructor)
    (m_parentTag : Constructor)
    (m_openTag : Constructor)
    (m_closedTag : Constructor)
    (m_workOutTag : Constructor)
    (m_ackOutTag : Constructor)
    (m_rejectedTag : Constructor)
    (m_registeredTag : Constructor)
    (m_absent : Constructor)
    (m_present : Constructor)
    (m_bytesRep : Value → List UInt8 → Prop)
    (m_checked : CheckedLookupBase m_recordsList e_program m_absent m_present)
    (m_projection : RecordProjectionShape e_program m_checked.projection)
    (m_projectionFunctionName : m_projection.functionName = m_checked.projectionName)
    (m_projectionEntryName : m_projection.recordName = m_checked.entryName)
    (m_projectionCode : m_projection.code = m_checked.projectionCode)
    (m_projectionRecordTag : m_projection.record = m_recordTag)
    (m_call : NodeId)
    (m_missingBody : NodeId)
    (m_foundBody : NodeId)
    (m_ledgerNode : NodeId)
    (m_statusNode : NodeId)
    (m_function : NodeId)
    (m_argument : NodeId)
    (m_wantedNode : NodeId)
    (m_listNode : NodeId)
    (m_name : Binder)
    (m_ledgerName : Binder)
    (m_callName : Binder)
    (m_wantedName : Binder)
    (m_listName : Binder)
    (m_wantedValue : Value)
    (m_ledger : Ledger)
    (m_wanted : Id)
    (m_destination : Nat)
    (m_payload : List UInt8)
    (m_records : List Value)
    (m_key : Value → Id)
    (m_selfAddress : Nat)
    (m_selfResolved : Nat)
    (m_comparisonAddress : Nat)
    (m_comparisonResolved : Nat)
    (m_projectionAddress : Nat)
    (m_projectionResolved : Nat)
    (m_captureValues : List Value)
    (m_captureEnv : Environment)
    (m_branchShape : e_program e_lookupBranch = some (.caseMatch m_call
      [(.constructor m_absent none, m_missingBody), (.constructor m_present (some (.binder m_name)), m_foundBody)]))
    (m_lookupPair : CheckedTuple e_program m_argument none [m_wantedNode, m_listNode])
    (m_callShape : e_program m_call = some (.apply m_function m_argument))
    (m_functionShape : e_program m_function = some (.variable m_callName))
    (m_functionBinding : ∀ (middle : Store) (entryPayload : Nat), CommitFrame e_start middle → CoreEval.lookup ((List.zip e_ledgerNames [e_nextValue, e_recordsValue, e_outputsValue]).reverse ++ ((List.zip e_names (e_nodes.map e_fieldValue)).reverse ++ extend e_captureEnv.reverse e_parameter (.location entryPayload))) m_callName = some (.location m_selfAddress))
    (m_wantedShape : e_program m_wantedNode = some (.variable m_wantedName))
    (m_listShape : e_program m_listNode = some (.variable m_listName))
    (m_wantedFresh : m_wantedName ≠ m_lookupPair.contextBinder)
    (m_listFresh : m_listName ≠ m_lookupPair.contextBinder)
    (m_wantedBinding : ∀ (middle : Store) (entryPayload : Nat), CommitFrame e_start middle → CoreEval.lookup ((List.zip e_ledgerNames [e_nextValue, e_recordsValue, e_outputsValue]).reverse ++ ((List.zip e_names (e_nodes.map e_fieldValue)).reverse ++ extend e_captureEnv.reverse e_parameter (.location entryPayload))) m_wantedName = some m_wantedValue)
    (m_listBinding : ∀ (middle : Store) (entryPayload : Nat), CommitFrame e_start middle → CoreEval.lookup ((List.zip e_ledgerNames [e_nextValue, e_recordsValue, e_outputsValue]).reverse ++ ((List.zip e_names (e_nodes.map e_fieldValue)).reverse ++ extend e_captureEnv.reverse e_parameter (.location entryPayload))) m_listName = some e_recordsValue)
    (m_selfBinding : CoreEval.lookup m_captureEnv.reverse m_checked.functionName = some (.location m_selfAddress))
    (m_comparisonBinding : CoreEval.lookup m_captureEnv.reverse m_checked.comparisonName = some (.location m_comparisonAddress))
    (m_projectionBinding : CoreEval.lookup m_captureEnv.reverse m_checked.projectionName = some (.location m_projectionAddress))
    (m_captureBindings : CaptureBindings e_program m_checked.captureNodes m_captureValues m_captureEnv)
    (m_selfResolution : ∀ (middle : Store) (_entryPayload : Nat), CommitFrame e_start middle → Resolve middle m_selfAddress m_selfResolved)
    (m_selfCell : ∀ (middle : Store) (_entryPayload : Nat), CommitFrame e_start middle → readCell middle m_selfResolved = some (.closureCode m_checked.code :: m_captureValues))
    (m_comparisonResolution : ∀ (middle : Store) (_entryPayload : Nat), CommitFrame e_start middle → Resolve middle m_comparisonAddress m_comparisonResolved)
    (m_comparisonCell : ∀ (middle : Store) (_entryPayload : Nat), CommitFrame e_start middle → readCell middle m_comparisonResolved = some [.closureCode m_checked.comparator.code])
    (m_projectionResolution : ∀ (middle : Store) (_entryPayload : Nat), CommitFrame e_start middle → Resolve middle m_projectionAddress m_projectionResolved)
    (m_projectionCell : ∀ (middle : Store) (_entryPayload : Nat), CommitFrame e_start middle → readCell middle m_projectionResolved = some [.closureCode m_checked.projectionCode])
    (m_wantedRep : ∀ (middle : Store) (_entryPayload : Nat), CommitFrame e_start middle → Ident m_recordsList middle m_wantedValue m_wanted)
    (m_listRep : ∀ (middle : Store) (_entryPayload : Nat), CommitFrame e_start middle → Children m_recordsList middle e_recordsValue m_records)
    (m_lookupKeys : ∀ (middle : Store) (_entryPayload : Nat), CommitFrame e_start middle → RepresentedEntries m_recordsList (RecordEntry m_projection.record) middle m_key m_records)
    (m_resultPair : CheckedTuple e_program m_missingBody none [m_ledgerNode, m_statusNode])
    (m_status : CheckedTuple e_program m_statusNode (some m_rejectedTag) [])
    (m_ledgerShape : e_program m_ledgerNode = some (.variable m_ledgerName))
    (m_ledgerFresh : m_ledgerName ≠ m_resultPair.contextBinder)
    (m_ledgerBinding : ∀ (middle : Store) (entryPayload : Nat), CommitFrame e_start middle → CoreEval.lookup ((List.zip e_ledgerNames [e_nextValue, e_recordsValue, e_outputsValue]).reverse ++ ((List.zip e_names (e_nodes.map e_fieldValue)).reverse ++ extend e_captureEnv.reverse e_parameter (.location entryPayload))) m_ledgerName = some e_ledger)
    (m_actualLookup : Ash.NetworkLedger.lookup m_key m_wanted m_records = none)
    (m_recordsRep : ∀ (middle : Store) (_entryPayload : Nat), CommitFrame e_start middle → RelatedValues (DecodedRecord m_ids m_recordTag m_noParent m_parentTag m_openTag m_closedTag middle) m_records m_ledger.records)
    (m_rootSame : m_recordsList.root = m_ids.root)
    (m_workSame : m_recordsList.work = m_ids.work)
    (m_ledgerRep : DecodedLedger m_ids m_recordsList m_outputsList e_ledgerTag m_recordTag m_noParent m_parentTag m_openTag m_closedTag m_workOutTag m_ackOutTag
      m_bytesRep e_start e_ledger m_ledger)
    :
    DecodedRegistrationResult m_ids m_recordsList m_outputsList e_ledgerTag m_recordTag m_noParent m_parentTag m_openTag m_closedTag m_workOutTag m_ackOutTag
      m_rejectedTag m_registeredTag m_bytesRep e_finish e_result (Ash.NetworkLedger.register m_ledger m_wanted m_destination m_payload) := by
  obtain ⟨middle, entryPayload, frame, bodyEval⟩ := checked_registration_entry_call e_program e_call e_function e_argument e_nodes e_env e_start e_finish e_result e_functionName e_address e_resolved e_code e_context e_storage e_parameter e_body e_captureNodes e_captureValues e_captureEnv e_fieldValue e_tuple e_callShape e_functionShape e_functionBinding e_resolution e_cell e_closureShape e_captureBindings e_fieldShapes e_scrutinee e_ledgerMatch e_ledgerScrutinee e_lookupBranch e_names e_ledgerNames e_ledgerName e_ledgerTag e_ledger e_nextValue e_recordsValue e_outputsValue e_bodyShape e_scrutineeShape e_arity e_plain e_ledgerShape e_ledgerScrutineeShape e_ledgerBinding e_ledgerArity e_ledgerRep e_ledgerPlain e_bounded e_evaluation
  exact registration_missing_checked m_ids m_recordsList m_outputsList e_ledgerTag m_recordTag m_noParent m_parentTag m_openTag m_closedTag m_workOutTag m_ackOutTag m_rejectedTag m_registeredTag m_absent m_present m_bytesRep e_program m_checked m_projection m_projectionFunctionName m_projectionEntryName m_projectionCode m_projectionRecordTag e_lookupBranch m_call m_missingBody m_foundBody m_ledgerNode m_statusNode m_function m_argument m_wantedNode m_listNode m_name m_ledgerName m_callName m_wantedName m_listName ((List.zip e_ledgerNames [e_nextValue, e_recordsValue, e_outputsValue]).reverse ++ ((List.zip e_names (e_nodes.map e_fieldValue)).reverse ++ extend e_captureEnv.reverse e_parameter (.location entryPayload))) middle e_finish e_result e_ledger m_wantedValue e_recordsValue m_ledger m_wanted m_destination m_payload m_records m_key m_selfAddress m_selfResolved m_comparisonAddress m_comparisonResolved m_projectionAddress m_projectionResolved m_captureValues m_captureEnv m_branchShape m_lookupPair m_callShape m_functionShape (m_functionBinding middle entryPayload frame) m_wantedShape m_listShape m_wantedFresh m_listFresh (m_wantedBinding middle entryPayload frame) (m_listBinding middle entryPayload frame) m_selfBinding m_comparisonBinding m_projectionBinding m_captureBindings (m_selfResolution middle entryPayload frame) (m_selfCell middle entryPayload frame) (m_comparisonResolution middle entryPayload frame) (m_comparisonCell middle entryPayload frame) (m_projectionResolution middle entryPayload frame) (m_projectionCell middle entryPayload frame) frame.2.1 (m_wantedRep middle entryPayload frame) (m_listRep middle entryPayload frame) (m_lookupKeys middle entryPayload frame) m_resultPair m_status m_ledgerShape m_ledgerFresh (m_ledgerBinding middle entryPayload frame) m_actualLookup (m_recordsRep middle entryPayload frame) m_rootSame m_workSame (decoded_ledger_retained m_ids m_recordsList m_outputsList e_ledgerTag m_recordTag m_noParent m_parentTag m_openTag m_closedTag m_workOutTag m_ackOutTag m_bytesRep e_start middle e_ledger m_ledger frame.1 frame.2.2 m_ledgerRep) bodyEval

/-- The checked Ledger fields uniquely determine its counter and finite decoded sequences. -/
theorem decoded_ledger_fields (ids recordsList outputsList : Constructors)
    (ledgerTag recordTag noParent parentTag openTag closedTag workOutTag ackOutTag : Constructor)
    (bytesRep : Value → List UInt8 → Prop) (store : Store) (value recordList outputList : Value)
    (counter : Int) (ledger : Ledger) (records outputs : List Value)
    (fields : NominalFields ledgerTag store value [.integer counter, recordList, outputList])
    (decoded : DecodedLedger ids recordsList outputsList ledgerTag recordTag noParent parentTag openTag closedTag
      workOutTag ackOutTag bytesRep store value ledger)
    (recordSpine : Children recordsList store recordList records)
    (outputSpine : Children outputsList store outputList outputs) :
    ledger.next = counter ∧
    RelatedValues (DecodedRecord ids recordTag noParent parentTag openTag closedTag store) records ledger.records ∧
    RelatedValues (DecodedOutput ids noParent parentTag workOutTag ackOutTag bytesRep store) outputs ledger.outputs := by
  obtain ⟨actualRecords, actualOutputs, recordEntries, outputEntries, actualFields, actualRecordSpine,
    recordValues, actualOutputSpine, outputValues⟩ := decoded
  have same := nominal_fields_unique ledgerTag store value _ _ fields actualFields
  simp only [List.cons.injEq, and_true, Value.integer.injEq] at same
  obtain ⟨counterEq, recordEq, outputEq⟩ := same
  subst actualRecords
  subst actualOutputs
  have recordEntriesEq := children_sequence_unique recordsList store recordList records recordEntries recordSpine actualRecordSpine
  have outputEntriesEq := children_sequence_unique outputsList store outputList outputs outputEntries outputSpine actualOutputSpine
  subst recordEntries
  subst outputEntries
  exact ⟨counterEq.symm, recordValues, outputValues⟩

/-- The actual entry, lookup hit, finish and commit return the decoded open registration. -/
theorem checked_entry_open_registration
    (e_program : Program)
    (e_call e_function e_argument : NodeId)
    (e_nodes : List NodeId)
    (e_env : Environment)
    (e_start e_finish : Store)
    (e_result : Value)
    (e_functionName : Binder)
    (e_address e_resolved e_code e_context e_storage e_parameter e_body : Nat)
    (e_captureNodes : List NodeId)
    (e_captureValues : List Value)
    (e_captureEnv : Environment)
    (e_fieldValue : NodeId → Value)
    (e_tuple : CheckedTuple e_program e_argument none e_nodes)
    (e_callShape : e_program e_call = some (.apply e_function e_argument))
    (e_functionShape : e_program e_function = some (.variable e_functionName))
    (e_functionBinding : CoreEval.lookup e_env e_functionName = some (.location e_address))
    (e_resolution : Resolve e_start e_address e_resolved)
    (e_cell : readCell e_start e_resolved = some (.closureCode e_code :: e_captureValues))
    (e_closureShape : e_program e_code = some (.closure e_context e_captureNodes e_storage e_parameter e_body))
    (e_captureBindings : CaptureBindings e_program e_captureNodes e_captureValues e_captureEnv)
    (e_fieldShapes : ∀ node ∈ e_nodes, ∃ name, e_program node = some (.variable name) ∧
      CoreEval.lookup (extend e_env e_tuple.contextBinder .context) name = some (e_fieldValue node))
    (e_scrutinee e_ledgerMatch e_ledgerScrutinee e_lookupBranch : NodeId)
    (e_names e_ledgerNames : List Binder)
    (e_ledgerName : Binder)
    (e_ledgerTag : Constructor)
    (e_ledger e_nextValue e_recordsValue e_outputsValue : Value)
    (e_bodyShape : e_program e_body = some (.caseMatch e_scrutinee [(.tuple (e_names.map Pattern.binder), e_ledgerMatch)]))
    (e_scrutineeShape : e_program e_scrutinee = some (.variable e_parameter))
    (e_arity : e_names.length = (e_nodes.map e_fieldValue).length)
    (e_plain : tupleFields (e_nodes.map e_fieldValue) = some (e_nodes.map e_fieldValue))
    (e_ledgerShape : e_program e_ledgerMatch = some (.caseMatch e_ledgerScrutinee
      [(.constructor e_ledgerTag (some (.tuple (e_ledgerNames.map Pattern.binder))), e_lookupBranch)]))
    (e_ledgerScrutineeShape : e_program e_ledgerScrutinee = some (.variable e_ledgerName))
    (e_ledgerBinding : ∀ payload,
      CoreEval.lookup ((List.zip e_names (e_nodes.map e_fieldValue)).reverse ++
        extend e_captureEnv.reverse e_parameter (.location payload)) e_ledgerName = some e_ledger)
    (e_ledgerArity : e_ledgerNames.length = 3)
    (e_ledgerRep : NominalFields e_ledgerTag e_start e_ledger [e_nextValue, e_recordsValue, e_outputsValue])
    (e_ledgerPlain : tupleFields [e_nextValue, e_recordsValue, e_outputsValue] = some [e_nextValue, e_recordsValue, e_outputsValue])
    (e_bounded : BoundedLocations e_start)
    (e_evaluation : Eval e_program e_env e_call e_start e_result e_finish)
    (n_o_recordsList : Constructors)
    (n_o_absent : Constructor)
    (n_o_present : Constructor)
    (n_o_checked : CheckedLookupBase n_o_recordsList e_program n_o_absent n_o_present)
    (n_o_projection : RecordProjectionShape e_program n_o_checked.projection)
    (n_o_projectionFunctionName : n_o_projection.functionName = n_o_checked.projectionName)
    (n_o_projectionEntryName : n_o_projection.recordName = n_o_checked.entryName)
    (n_o_projectionCode : n_o_projection.code = n_o_checked.projectionCode)
    (n_o_call : NodeId)
    (n_o_missingBody : NodeId)
    (n_o_foundBody : NodeId)
    (n_o_function : NodeId)
    (n_o_argument : NodeId)
    (n_o_wantedNode : NodeId)
    (n_o_listNode : NodeId)
    (n_o_name : Binder)
    (n_o_callName : Binder)
    (n_o_wantedName : Binder)
    (n_o_listName : Binder)
    (n_o_wantedValue : Value)
    (n_o_found : Value)
    (n_o_wanted : Id)
    (n_o_records : List Value)
    (n_o_key : Value → Id)
    (n_o_selfAddress : Nat)
    (n_o_selfResolved : Nat)
    (n_o_comparisonAddress : Nat)
    (n_o_comparisonResolved : Nat)
    (n_o_projectionAddress : Nat)
    (n_o_projectionResolved : Nat)
    (n_o_captureValues : List Value)
    (n_o_captureEnv : Environment)
    (n_o_branchShape : e_program e_lookupBranch = some (.caseMatch n_o_call
      [(.constructor n_o_absent none, n_o_missingBody), (.constructor n_o_present (some (.binder n_o_name)), n_o_foundBody)]))
    (n_o_lookupPair : CheckedTuple e_program n_o_argument none [n_o_wantedNode, n_o_listNode])
    (n_o_callShape : e_program n_o_call = some (.apply n_o_function n_o_argument))
    (n_o_functionShape : e_program n_o_function = some (.variable n_o_callName))
    (n_o_functionBinding : ∀ (entryStore : Store) (entryPayload : Nat), CommitFrame e_start entryStore → CoreEval.lookup ((List.zip e_ledgerNames [e_nextValue, e_recordsValue, e_outputsValue]).reverse ++ ((List.zip e_names (e_nodes.map e_fieldValue)).reverse ++ extend e_captureEnv.reverse e_parameter (.location entryPayload))) n_o_callName = some (.location n_o_selfAddress))
    (n_o_wantedShape : e_program n_o_wantedNode = some (.variable n_o_wantedName))
    (n_o_listShape : e_program n_o_listNode = some (.variable n_o_listName))
    (n_o_wantedFresh : n_o_wantedName ≠ n_o_lookupPair.contextBinder)
    (n_o_listFresh : n_o_listName ≠ n_o_lookupPair.contextBinder)
    (n_o_wantedBinding : ∀ (entryStore : Store) (entryPayload : Nat), CommitFrame e_start entryStore → CoreEval.lookup ((List.zip e_ledgerNames [e_nextValue, e_recordsValue, e_outputsValue]).reverse ++ ((List.zip e_names (e_nodes.map e_fieldValue)).reverse ++ extend e_captureEnv.reverse e_parameter (.location entryPayload))) n_o_wantedName = some n_o_wantedValue)
    (n_o_listBinding : ∀ (entryStore : Store) (entryPayload : Nat), CommitFrame e_start entryStore → CoreEval.lookup ((List.zip e_ledgerNames [e_nextValue, e_recordsValue, e_outputsValue]).reverse ++ ((List.zip e_names (e_nodes.map e_fieldValue)).reverse ++ extend e_captureEnv.reverse e_parameter (.location entryPayload))) n_o_listName = some e_recordsValue)
    (n_o_selfBinding : CoreEval.lookup n_o_captureEnv.reverse n_o_checked.functionName = some (.location n_o_selfAddress))
    (n_o_comparisonBinding : CoreEval.lookup n_o_captureEnv.reverse n_o_checked.comparisonName = some (.location n_o_comparisonAddress))
    (n_o_projectionBinding : CoreEval.lookup n_o_captureEnv.reverse n_o_checked.projectionName = some (.location n_o_projectionAddress))
    (n_o_captureBindings : CaptureBindings e_program n_o_checked.captureNodes n_o_captureValues n_o_captureEnv)
    (n_o_selfResolution : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → Resolve entryStore n_o_selfAddress n_o_selfResolved)
    (n_o_selfCell : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → readCell entryStore n_o_selfResolved = some (.closureCode n_o_checked.code :: n_o_captureValues))
    (n_o_comparisonResolution : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → Resolve entryStore n_o_comparisonAddress n_o_comparisonResolved)
    (n_o_comparisonCell : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → readCell entryStore n_o_comparisonResolved = some [.closureCode n_o_checked.comparator.code])
    (n_o_projectionResolution : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → Resolve entryStore n_o_projectionAddress n_o_projectionResolved)
    (n_o_projectionCell : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → readCell entryStore n_o_projectionResolved = some [.closureCode n_o_checked.projectionCode])
    (n_o_wantedRep : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → Ident n_o_recordsList entryStore n_o_wantedValue n_o_wanted)
    (n_o_listRep : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → Children n_o_recordsList entryStore e_recordsValue n_o_records)
    (n_o_lookupKeys : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → RepresentedEntries n_o_recordsList (RecordEntry n_o_projection.record) entryStore n_o_key n_o_records)
    (n_o_actualLookup : Ash.NetworkLedger.lookup n_o_key n_o_wanted n_o_records = some n_o_found)
    (n_n_f_function : NodeId)
    (n_n_f_argument : NodeId)
    (n_n_f_nodes : List NodeId)
    (n_n_f_functionName : Binder)
    (n_n_f_address : Nat)
    (n_n_f_resolved : Nat)
    (n_n_f_code : Nat)
    (n_n_f_context : Nat)
    (n_n_f_storage : Nat)
    (n_n_f_parameter : Nat)
    (n_n_f_body : Nat)
    (n_n_f_captureNodes : List NodeId)
    (n_n_f_captureValues : List Value)
    (n_n_f_captureEnv : Environment)
    (n_n_f_fieldValue : NodeId → Value)
    (n_n_f_tuple : CheckedTuple e_program n_n_f_argument none n_n_f_nodes)
    (n_n_f_callShape : e_program n_o_foundBody = some (.apply n_n_f_function n_n_f_argument))
    (n_n_f_functionShape : e_program n_n_f_function = some (.variable n_n_f_functionName))
    (n_n_f_functionBinding : ∀ (entryStore : Store) (entryPayload : Nat), CommitFrame e_start entryStore → CoreEval.lookup (extend ((List.zip e_ledgerNames [e_nextValue, e_recordsValue, e_outputsValue]).reverse ++ ((List.zip e_names (e_nodes.map e_fieldValue)).reverse ++ extend e_captureEnv.reverse e_parameter (.location entryPayload))) n_o_name n_o_found) n_n_f_functionName = some (.location n_n_f_address))
    (n_n_f_resolution : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → Resolve middle n_n_f_address n_n_f_resolved)
    (n_n_f_cell : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → readCell middle n_n_f_resolved = some (.closureCode n_n_f_code :: n_n_f_captureValues))
    (n_n_f_closureShape : e_program n_n_f_code = some (.closure n_n_f_context n_n_f_captureNodes n_n_f_storage n_n_f_parameter n_n_f_body))
    (n_n_f_captureBindings : CaptureBindings e_program n_n_f_captureNodes n_n_f_captureValues n_n_f_captureEnv)
    (n_n_f_fieldShapes : ∀ (entryStore : Store) (entryPayload : Nat), CommitFrame e_start entryStore → ∀ node ∈ n_n_f_nodes, ∃ name, e_program node = some (.variable name) ∧
      CoreEval.lookup (extend (extend ((List.zip e_ledgerNames [e_nextValue, e_recordsValue, e_outputsValue]).reverse ++ ((List.zip e_names (e_nodes.map e_fieldValue)).reverse ++ extend e_captureEnv.reverse e_parameter (.location entryPayload))) n_o_name n_o_found) n_n_f_tuple.contextBinder .context) name = some (n_n_f_fieldValue node))
    (n_n_f_scrutinee : NodeId)
    (n_n_f_recordMatch : NodeId)
    (n_n_f_recordScrutinee : NodeId)
    (n_n_f_phaseBranch : NodeId)
    (n_n_f_names : List Binder)
    (n_n_f_recordNames : List Binder)
    (n_n_f_recordName : Binder)
    (n_n_f_recordTag : Constructor)
    (n_n_f_openTag : Constructor)
    (n_n_f_closedTag : Constructor)
    (n_n_f_foundKey : Value)
    (n_n_f_parent : Value)
    (n_n_f_phase : Value)
    (n_n_f_children : Value)
    (n_n_f_bodyShape : e_program n_n_f_body = some (.caseMatch n_n_f_scrutinee [(.tuple (n_n_f_names.map Pattern.binder), n_n_f_recordMatch)]))
    (n_n_f_scrutineeShape : e_program n_n_f_scrutinee = some (.variable n_n_f_parameter))
    (n_n_f_arity : n_n_f_names.length = (n_n_f_nodes.map n_n_f_fieldValue).length)
    (n_n_f_plain : tupleFields (n_n_f_nodes.map n_n_f_fieldValue) = some (n_n_f_nodes.map n_n_f_fieldValue))
    (n_n_f_recordShape : e_program n_n_f_recordMatch = some (.caseMatch n_n_f_recordScrutinee
      [(.constructor n_n_f_recordTag (some (.tuple (n_n_f_recordNames.map Pattern.binder))), n_n_f_phaseBranch)]))
    (n_n_f_recordScrutineeShape : e_program n_n_f_recordScrutinee = some (.variable n_n_f_recordName))
    (n_n_f_recordBinding : ∀ payload, CoreEval.lookup ((List.zip n_n_f_names (n_n_f_nodes.map n_n_f_fieldValue)).reverse ++
      extend n_n_f_captureEnv.reverse n_n_f_parameter (.location payload)) n_n_f_recordName = some n_o_found)
    (n_n_f_recordArity : n_n_f_recordNames.length = 4)
    (n_n_f_recordRep : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → NominalFields n_n_f_recordTag middle n_o_found [n_n_f_foundKey, n_n_f_parent, n_n_f_phase, n_n_f_children])
    (n_n_f_recordPlain : tupleFields [n_n_f_foundKey, n_n_f_parent, n_n_f_phase, n_n_f_children] = some [n_n_f_foundKey, n_n_f_parent, n_n_f_phase, n_n_f_children])
    (n_n_f_phaseAddress : Nat)
    (n_n_f_phaseResolved : Nat)
    (n_n_f_phaseEq : n_n_f_phase = .location n_n_f_phaseAddress)
    (n_n_f_phaseResolution : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → Resolve middle n_n_f_phaseAddress n_n_f_phaseResolved)
    (n_n_f_phaseCell : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → readCell middle n_n_f_phaseResolved = some [.tag n_n_f_openTag])
    (n_n_f_different : n_n_f_openTag ≠ n_n_f_closedTag)
    (n_n_f_phaseNode : NodeId)
    (n_n_f_closedBody : NodeId)
    (n_n_f_commitCall : NodeId)
    (n_n_f_phaseName : Binder)
    (n_n_f_phaseShape : e_program n_n_f_phaseBranch = some (.caseMatch n_n_f_phaseNode
      [(.constructor n_n_f_closedTag none, n_n_f_closedBody), (.constructor n_n_f_openTag none, n_n_f_commitCall)]))
    (n_n_f_phaseNodeShape : e_program n_n_f_phaseNode = some (.variable n_n_f_phaseName))
    (n_n_f_phaseBinding : ∀ payload, CoreEval.lookup ((List.zip n_n_f_recordNames [n_n_f_foundKey, n_n_f_parent, n_n_f_phase, n_n_f_children]).reverse ++
      ((List.zip n_n_f_names (n_n_f_nodes.map n_n_f_fieldValue)).reverse ++ extend n_n_f_captureEnv.reverse n_n_f_parameter (.location payload))) n_n_f_phaseName = some n_n_f_phase)
    (n_n_f_commitFunction : NodeId)
    (n_n_f_commitArgument : NodeId)
    (n_n_f_commitScrutinee : NodeId)
    (n_n_f_commitArm : NodeId)
    (n_n_f_commitNodes : List NodeId)
    (n_n_f_commitName : Binder)
    (n_n_f_commitAddress : Nat)
    (n_n_f_commitResolved : Nat)
    (n_n_f_commitCode : Nat)
    (n_n_f_commitContext : Nat)
    (n_n_f_commitStorage : Nat)
    (n_n_f_commitParameter : Nat)
    (n_n_f_commitBody : Nat)
    (n_n_f_commitCaptureNodes : List NodeId)
    (n_n_f_commitCaptureValues : List Value)
    (n_n_f_commitCaptureEnv : Environment)
    (n_n_f_commitFieldValue : NodeId → Value)
    (n_n_f_commitTuple : CheckedTuple e_program n_n_f_commitArgument none n_n_f_commitNodes)
    (n_n_f_commitCallShape : e_program n_n_f_commitCall = some (.apply n_n_f_commitFunction n_n_f_commitArgument))
    (n_n_f_commitFunctionShape : e_program n_n_f_commitFunction = some (.variable n_n_f_commitName))
    (n_n_f_commitBinding : ∀ payload, CoreEval.lookup ((List.zip n_n_f_recordNames [n_n_f_foundKey, n_n_f_parent, n_n_f_phase, n_n_f_children]).reverse ++
      ((List.zip n_n_f_names (n_n_f_nodes.map n_n_f_fieldValue)).reverse ++ extend n_n_f_captureEnv.reverse n_n_f_parameter (.location payload))) n_n_f_commitName =
      some (.location n_n_f_commitAddress))
    (n_n_f_commitResolution : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → Resolve middle n_n_f_commitAddress n_n_f_commitResolved)
    (n_n_f_commitCell : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → readCell middle n_n_f_commitResolved = some (.closureCode n_n_f_commitCode :: n_n_f_commitCaptureValues))
    (n_n_f_commitClosureShape : e_program n_n_f_commitCode = some (.closure n_n_f_commitContext n_n_f_commitCaptureNodes n_n_f_commitStorage n_n_f_commitParameter n_n_f_commitBody))
    (n_n_f_commitCaptureBindings : CaptureBindings e_program n_n_f_commitCaptureNodes n_n_f_commitCaptureValues n_n_f_commitCaptureEnv)
    (n_n_f_commitFieldShapes : ∀ payload node, node ∈ n_n_f_commitNodes → ∃ name, e_program node = some (.variable name) ∧
      CoreEval.lookup (extend ((List.zip n_n_f_recordNames [n_n_f_foundKey, n_n_f_parent, n_n_f_phase, n_n_f_children]).reverse ++
        ((List.zip n_n_f_names (n_n_f_nodes.map n_n_f_fieldValue)).reverse ++ extend n_n_f_captureEnv.reverse n_n_f_parameter (.location payload)))
        n_n_f_commitTuple.contextBinder .context) name = some (n_n_f_commitFieldValue node))
    (n_n_f_commitNames : List Binder)
    (n_n_f_commitBodyShape : e_program n_n_f_commitBody = some (.caseMatch n_n_f_commitScrutinee [(.tuple (n_n_f_commitNames.map Pattern.binder), n_n_f_commitArm)]))
    (n_n_f_commitScrutineeShape : e_program n_n_f_commitScrutinee = some (.variable n_n_f_commitParameter))
    (n_n_f_commitArity : n_n_f_commitNames.length = (n_n_f_commitNodes.map n_n_f_commitFieldValue).length)
    (n_n_f_commitPlain : tupleFields (n_n_f_commitNodes.map n_n_f_commitFieldValue) = some (n_n_f_commitNodes.map n_n_f_commitFieldValue))
    (n_n_f_bounded : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → BoundedLocations middle)
    (n_n_c_ids : Constructors)
    (n_n_c_outputsList : Constructors)
    (n_n_c_buffers : Ash.NetworkLedger.CoreIncrement.Buffers)
    (n_n_c_checkedResult : CheckedSuccessFields e_program n_n_c_buffers)
    (n_n_c_second : NodeId)
    (n_n_c_third : NodeId)
    (n_n_c_fourth : NodeId)
    (n_n_c_workNode : NodeId)
    (n_n_c_replacementNode : NodeId)
    (n_n_c_updateNode : NodeId)
    (n_n_c_outputNode : NodeId)
    (n_n_c_workName : Binder)
    (n_n_c_replacementName : Binder)
    (n_n_c_remainingName : Binder)
    (n_n_c_outgoingName : Binder)
    (n_n_c_workOutTag : Constructor)
    (n_n_c_parentTag : Constructor)
    (n_n_c_destination : Value)
    (n_n_c_bytes : Value)
    (n_n_c_owner : Nat)
    (n_n_c_counter : Int)
    (n_n_c_children : List Value)
    (n_n_c_outputs : List Value)
    (n_n_c_firstShape : e_program n_n_f_commitArm = some (.bind n_n_c_workName n_n_c_workNode n_n_c_second))
    (n_n_c_secondShape : e_program n_n_c_second = some (.bind n_n_c_replacementName n_n_c_replacementNode n_n_c_third))
    (n_n_c_thirdShape : e_program n_n_c_third = some (.bind n_n_c_remainingName n_n_c_updateNode n_n_c_fourth))
    (n_n_c_fourthShape : e_program n_n_c_fourth = some (.bind n_n_c_outgoingName n_n_c_outputNode n_n_c_checkedResult.root))
    (n_n_c_nonnegative : 0 ≤ n_n_c_counter)
    (n_n_c_workFunction : NodeId)
    (n_n_c_workArgument : NodeId)
    (n_n_c_workOwnerNode : NodeId)
    (n_n_c_workCounterNode : NodeId)
    (n_n_c_workOperand : NodeId)
    (n_n_c_workOwnerName : Binder)
    (n_n_c_workClosure : CheckedClosure e_program n_n_c_workFunction)
    (n_n_c_workPair : CheckedTuple e_program n_n_c_workArgument none [n_n_c_workOwnerNode, n_n_c_workCounterNode])
    (n_n_c_workConstructor : CheckedTuple e_program n_n_c_workClosure.body (some n_n_c_ids.work) [n_n_c_workOperand])
    (n_n_c_workCallShape : e_program n_n_c_workNode = some (.apply n_n_c_workFunction n_n_c_workArgument))
    (n_n_c_workOwnerShape : e_program n_n_c_workOwnerNode = some (.variable n_n_c_workOwnerName))
    (n_n_c_workCounterShape : e_program n_n_c_workCounterNode = some (.variable n_n_c_checkedResult.increment.counterBinder))
    (n_n_c_workOwnerFresh : n_n_c_workOwnerName ≠ n_n_c_workPair.contextBinder)
    (n_n_c_workCounterFresh : n_n_c_checkedResult.increment.counterBinder ≠ n_n_c_workPair.contextBinder)
    (n_n_c_workOwnerBinding : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → ∀ (s : Store) (p : Nat), CommitFrame middle s → CoreEval.lookup ((List.zip n_n_f_commitNames (n_n_f_commitNodes.map n_n_f_commitFieldValue)).reverse ++ extend n_n_f_commitCaptureEnv.reverse n_n_f_commitParameter (.location p)) n_n_c_workOwnerName = some (.integer (Int.ofNat n_n_c_owner)))
    (n_n_c_workOperandShape : e_program n_n_c_workOperand = some (.variable n_n_c_workClosure.parameter))
    (n_n_c_workOperandFresh : n_n_c_workClosure.parameter ≠ n_n_c_workConstructor.contextBinder)
    (n_n_c_childChecked : Ash.NetworkLedger.CoreInsert.CheckedInsert n_n_c_ids e_program)
    (n_n_c_replacementFunction : NodeId)
    (n_n_c_replacementArgument : NodeId)
    (n_n_c_replacementWantedNode : NodeId)
    (n_n_c_replacementParentNode : NodeId)
    (n_n_c_replacementOpenNode : NodeId)
    (n_n_c_childAppendNode : NodeId)
    (n_n_c_replacementOperand : NodeId)
    (n_n_c_childFunction : NodeId)
    (n_n_c_childArgument : NodeId)
    (n_n_c_childCall : NodeId)
    (n_n_c_childListNode : NodeId)
    (n_n_c_childConstructorFunction : NodeId)
    (n_n_c_childConstructorArgument : NodeId)
    (n_n_c_childIdNode : NodeId)
    (n_n_c_childDestinationNode : NodeId)
    (n_n_c_childOperand : NodeId)
    (n_n_c_replacementWantedName : Binder)
    (n_n_c_replacementParentName : Binder)
    (n_n_c_childCallName : Binder)
    (n_n_c_childListName : Binder)
    (n_n_c_childIdName : Binder)
    (n_n_c_childDestinationName : Binder)
    (n_n_c_childSelfAddress : Nat)
    (n_n_c_childSelfResolved : Nat)
    (n_n_c_childCaptureValues : List Value)
    (n_n_c_childCaptureEnv : Environment)
    (n_n_c_replacementClosure : CheckedClosure e_program n_n_c_replacementFunction)
    (n_n_c_replacementConstructor : CheckedTuple e_program n_n_c_replacementClosure.body (some n_n_f_recordTag) [n_n_c_replacementOperand])
    (n_n_c_replacementTuple : CheckedTuple e_program n_n_c_replacementArgument none
      [n_n_c_replacementWantedNode, n_n_c_replacementParentNode, n_n_c_replacementOpenNode, n_n_c_childAppendNode])
    (n_n_c_replacementOpenTuple : CheckedTuple e_program n_n_c_replacementOpenNode (some n_n_f_openTag) [])
    (n_n_c_childOuterPair : CheckedTuple e_program n_n_c_childArgument none [n_n_c_childCall, n_n_c_childListNode])
    (n_n_c_childClosure : CheckedClosure e_program n_n_c_childConstructorFunction)
    (n_n_c_childPair : CheckedTuple e_program n_n_c_childConstructorArgument none [n_n_c_childIdNode, n_n_c_childDestinationNode])
    (n_n_c_childConstructor : CheckedTuple e_program n_n_c_childClosure.body (some n_n_c_ids.child) [n_n_c_childOperand])
    (n_n_c_replacementCallShape : e_program n_n_c_replacementNode = some (.apply n_n_c_replacementFunction n_n_c_replacementArgument))
    (n_n_c_replacementOperandShape : e_program n_n_c_replacementOperand = some (.variable n_n_c_replacementClosure.parameter))
    (n_n_c_replacementOperandFresh : n_n_c_replacementClosure.parameter ≠ n_n_c_replacementConstructor.contextBinder)
    (n_n_c_replacementWantedShape : e_program n_n_c_replacementWantedNode = some (.variable n_n_c_replacementWantedName))
    (n_n_c_replacementParentShape : e_program n_n_c_replacementParentNode = some (.variable n_n_c_replacementParentName))
    (n_n_c_replacementWantedFresh : n_n_c_replacementWantedName ≠ n_n_c_replacementTuple.contextBinder)
    (n_n_c_replacementParentFresh : n_n_c_replacementParentName ≠ n_n_c_replacementTuple.contextBinder)
    (n_n_c_childAppendShape : e_program n_n_c_childAppendNode = some (.apply n_n_c_childFunction n_n_c_childArgument))
    (n_n_c_childFunctionShape : e_program n_n_c_childFunction = some (.variable n_n_c_childCallName))
    (n_n_c_childListShape : e_program n_n_c_childListNode = some (.variable n_n_c_childListName))
    (n_n_c_childListFresh : n_n_c_childListName ≠ n_n_c_childOuterPair.contextBinder)
    (n_n_c_childCallShape : e_program n_n_c_childCall = some (.apply n_n_c_childConstructorFunction n_n_c_childConstructorArgument))
    (n_n_c_childIdShape : e_program n_n_c_childIdNode = some (.variable n_n_c_childIdName))
    (n_n_c_childDestinationShape : e_program n_n_c_childDestinationNode = some (.variable n_n_c_childDestinationName))
    (n_n_c_childIdOuterFresh : n_n_c_childIdName ≠ n_n_c_childOuterPair.contextBinder)
    (n_n_c_childDestinationOuterFresh : n_n_c_childDestinationName ≠ n_n_c_childOuterPair.contextBinder)
    (n_n_c_childIdFresh : n_n_c_childIdName ≠ n_n_c_childPair.contextBinder)
    (n_n_c_childDestinationFresh : n_n_c_childDestinationName ≠ n_n_c_childPair.contextBinder)
    (n_n_c_childOperandShape : e_program n_n_c_childOperand = some (.variable n_n_c_childClosure.parameter))
    (n_n_c_childOperandFresh : n_n_c_childClosure.parameter ≠ n_n_c_childConstructor.contextBinder)
    (n_n_c_replacementBindings : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → ∀ (s : Store) (p : Nat), CommitFrame middle s → ∀ work,
      let replacementEnv := extend ((List.zip n_n_f_commitNames (n_n_f_commitNodes.map n_n_f_commitFieldValue)).reverse ++ extend n_n_f_commitCaptureEnv.reverse n_n_f_commitParameter (.location p)) n_n_c_workName work
      CoreEval.lookup replacementEnv n_n_c_replacementWantedName = some n_o_wantedValue ∧
      CoreEval.lookup replacementEnv n_n_c_replacementParentName = some n_n_f_parent)
    (n_n_c_childBindings : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → ∀ (s : Store) (p : Nat), CommitFrame middle s → ∀ work,
      let appendEnv := extend (extend ((List.zip n_n_f_commitNames (n_n_f_commitNodes.map n_n_f_commitFieldValue)).reverse ++ extend n_n_f_commitCaptureEnv.reverse n_n_f_commitParameter (.location p)) n_n_c_workName work) n_n_c_replacementTuple.contextBinder .context
      CoreEval.lookup appendEnv n_n_c_childCallName = some (.location n_n_c_childSelfAddress) ∧
      CoreEval.lookup appendEnv n_n_c_childListName = some n_n_f_children ∧
      CoreEval.lookup appendEnv n_n_c_childIdName = some work ∧
      CoreEval.lookup appendEnv n_n_c_childDestinationName = some n_n_c_destination)
    (n_n_c_childSelfBinding : CoreEval.lookup n_n_c_childCaptureEnv.reverse n_n_c_childChecked.functionName = some (.location n_n_c_childSelfAddress))
    (n_n_c_childCaptureBindings : CaptureBindings e_program n_n_c_childChecked.captureNodes n_n_c_childCaptureValues n_n_c_childCaptureEnv)
    (n_n_c_childSelfResolution : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → Resolve s n_n_c_childSelfAddress n_n_c_childSelfResolved)
    (n_n_c_childSelfCell : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → readCell s n_n_c_childSelfResolved = some (.closureCode n_n_c_childChecked.code :: n_n_c_childCaptureValues))
    (n_n_c_childListRep : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → Children n_n_c_ids s n_n_f_children n_n_c_children)
    (n_n_c_childLocated : Ash.NetworkLedger.CoreGenericInsert.LocatedEntries n_n_c_children)
    (n_n_c_updateChecked : Ash.NetworkLedger.CoreRecordUpdate.CheckedRecordUpdate n_o_recordsList e_program)
    (n_n_c_updateProjection : RecordProjectionShape e_program n_n_c_updateChecked.projection)
    (n_n_c_updateProjectionName : n_n_c_updateProjection.functionName = n_n_c_updateChecked.projectionName)
    (n_n_c_updateEntryName : n_n_c_updateProjection.recordName = n_n_c_updateChecked.entryName)
    (n_n_c_updateProjectionCode : n_n_c_updateProjection.code = n_n_c_updateChecked.projectionCode)
    (n_n_c_updateFunction : NodeId)
    (n_n_c_updateArgument : NodeId)
    (n_n_c_updateWantedNode : NodeId)
    (n_n_c_updateReplacementNode : NodeId)
    (n_n_c_updateListNode : NodeId)
    (n_n_c_updateCallName : Binder)
    (n_n_c_updateWantedName : Binder)
    (n_n_c_updateReplacementName : Binder)
    (n_n_c_updateListName : Binder)
    (n_n_c_updateSelfAddress : Nat)
    (n_n_c_updateSelfResolved : Nat)
    (n_n_c_updateComparisonAddress : Nat)
    (n_n_c_updateComparisonResolved : Nat)
    (n_n_c_updateProjectionAddress : Nat)
    (n_n_c_updateProjectionResolved : Nat)
    (n_n_c_updateCaptureValues : List Value)
    (n_n_c_updateCaptureEnv : Environment)
    (n_n_c_updateTriple : CheckedTuple e_program n_n_c_updateArgument none [n_n_c_updateWantedNode, n_n_c_updateReplacementNode, n_n_c_updateListNode])
    (n_n_c_updateCallShape : e_program n_n_c_updateNode = some (.apply n_n_c_updateFunction n_n_c_updateArgument))
    (n_n_c_updateFunctionShape : e_program n_n_c_updateFunction = some (.variable n_n_c_updateCallName))
    (n_n_c_updateWantedShape : e_program n_n_c_updateWantedNode = some (.variable n_n_c_updateWantedName))
    (n_n_c_updateReplacementShape : e_program n_n_c_updateReplacementNode = some (.variable n_n_c_updateReplacementName))
    (n_n_c_updateListShape : e_program n_n_c_updateListNode = some (.variable n_n_c_updateListName))
    (n_n_c_updateWantedFresh : n_n_c_updateWantedName ≠ n_n_c_updateTriple.contextBinder)
    (n_n_c_updateReplacementFresh : n_n_c_updateReplacementName ≠ n_n_c_updateTriple.contextBinder)
    (n_n_c_updateListFresh : n_n_c_updateListName ≠ n_n_c_updateTriple.contextBinder)
    (n_n_c_updateList : Value)
    (n_n_c_updateBindings : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → ∀ (s : Store) (p : Nat), CommitFrame middle s → ∀ work replacement,
      let updateEnv := extend (extend ((List.zip n_n_f_commitNames (n_n_f_commitNodes.map n_n_f_commitFieldValue)).reverse ++ extend n_n_f_commitCaptureEnv.reverse n_n_f_commitParameter (.location p)) n_n_c_workName work) n_n_c_replacementName replacement
      CoreEval.lookup updateEnv n_n_c_updateCallName = some (.location n_n_c_updateSelfAddress) ∧
      CoreEval.lookup updateEnv n_n_c_updateWantedName = some n_o_wantedValue ∧
      CoreEval.lookup updateEnv n_n_c_updateReplacementName = some replacement ∧
      CoreEval.lookup updateEnv n_n_c_updateListName = some n_n_c_updateList)
    (n_n_c_updateSelfBinding : CoreEval.lookup n_n_c_updateCaptureEnv.reverse n_n_c_updateChecked.functionName = some (.location n_n_c_updateSelfAddress))
    (n_n_c_updateComparisonBinding : CoreEval.lookup n_n_c_updateCaptureEnv.reverse n_n_c_updateChecked.comparisonName = some (.location n_n_c_updateComparisonAddress))
    (n_n_c_updateProjectionBinding : CoreEval.lookup n_n_c_updateCaptureEnv.reverse n_n_c_updateChecked.projectionName = some (.location n_n_c_updateProjectionAddress))
    (n_n_c_updateCaptureBindings : CaptureBindings e_program n_n_c_updateChecked.captureNodes n_n_c_updateCaptureValues n_n_c_updateCaptureEnv)
    (n_n_c_updateSelfResolution : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → Resolve s n_n_c_updateSelfAddress n_n_c_updateSelfResolved)
    (n_n_c_updateSelfCell : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → readCell s n_n_c_updateSelfResolved = some (.closureCode n_n_c_updateChecked.code :: n_n_c_updateCaptureValues))
    (n_n_c_updateComparisonResolution : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → Resolve s n_n_c_updateComparisonAddress n_n_c_updateComparisonResolved)
    (n_n_c_updateComparisonCell : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → readCell s n_n_c_updateComparisonResolved = some [.closureCode n_n_c_updateChecked.comparator.code])
    (n_n_c_updateProjectionResolution : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → Resolve s n_n_c_updateProjectionAddress n_n_c_updateProjectionResolved)
    (n_n_c_updateProjectionCell : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → readCell s n_n_c_updateProjectionResolved = some [.closureCode n_n_c_updateChecked.projectionCode])
    (n_n_c_updateWantedRep : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → Ident n_o_recordsList s n_o_wantedValue n_o_wanted)
    (n_n_c_updateListRep : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → Children n_o_recordsList s n_n_c_updateList n_o_records)
    (n_n_c_updateKeys : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → RepresentedEntries n_o_recordsList (RecordEntry n_n_c_updateProjection.record) s n_o_key n_o_records)
    (n_n_c_outputChecked : Ash.NetworkLedger.CoreInsert.CheckedInsert n_n_c_outputsList e_program)
    (n_n_c_outputFunction : NodeId)
    (n_n_c_outputArgument : NodeId)
    (n_n_c_outputCall : NodeId)
    (n_n_c_outputListNode : NodeId)
    (n_n_c_outputConstructorFunction : NodeId)
    (n_n_c_outputConstructorArgument : NodeId)
    (n_n_c_outputChildNode : NodeId)
    (n_n_c_outputParentCall : NodeId)
    (n_n_c_outputDestinationNode : NodeId)
    (n_n_c_outputPayloadNode : NodeId)
    (n_n_c_outputParentFunction : NodeId)
    (n_n_c_outputParentArguments : NodeId)
    (n_n_c_outputOwnerNode : NodeId)
    (n_n_c_outputWantedNode : NodeId)
    (n_n_c_outputParentOperand : NodeId)
    (n_n_c_outputOperand : NodeId)
    (n_n_c_outputCallName : Binder)
    (n_n_c_outputListName : Binder)
    (n_n_c_outputChildName : Binder)
    (n_n_c_outputOwnerName : Binder)
    (n_n_c_outputWantedName : Binder)
    (n_n_c_outputDestinationName : Binder)
    (n_n_c_outputBytesName : Binder)
    (n_n_c_outputSelfAddress : Nat)
    (n_n_c_outputSelfResolved : Nat)
    (n_n_c_outputCaptureValues : List Value)
    (n_n_c_outputCaptureEnv : Environment)
    (n_n_c_outputOuterPair : CheckedTuple e_program n_n_c_outputArgument none [n_n_c_outputCall, n_n_c_outputListNode])
    (n_n_c_outputClosure : CheckedClosure e_program n_n_c_outputConstructorFunction)
    (n_n_c_outputConstructor : CheckedTuple e_program n_n_c_outputClosure.body (some n_n_c_workOutTag) [n_n_c_outputOperand])
    (n_n_c_outputTuple : CheckedTuple e_program n_n_c_outputConstructorArgument none [n_n_c_outputChildNode, n_n_c_outputParentCall, n_n_c_outputDestinationNode, n_n_c_outputPayloadNode])
    (n_n_c_outputParentClosure : CheckedClosure e_program n_n_c_outputParentFunction)
    (n_n_c_outputParentPair : CheckedTuple e_program n_n_c_outputParentArguments none [n_n_c_outputOwnerNode, n_n_c_outputWantedNode])
    (n_n_c_outputParentConstructor : CheckedTuple e_program n_n_c_outputParentClosure.body (some n_n_c_parentTag) [n_n_c_outputParentOperand])
    (n_n_c_outputCallShape : e_program n_n_c_outputNode = some (.apply n_n_c_outputFunction n_n_c_outputArgument))
    (n_n_c_outputFunctionShape : e_program n_n_c_outputFunction = some (.variable n_n_c_outputCallName))
    (n_n_c_outputListShape : e_program n_n_c_outputListNode = some (.variable n_n_c_outputListName))
    (n_n_c_outputListFresh : n_n_c_outputListName ≠ n_n_c_outputOuterPair.contextBinder)
    (n_n_c_outputShape : e_program n_n_c_outputCall = some (.apply n_n_c_outputConstructorFunction n_n_c_outputConstructorArgument))
    (n_n_c_outputOperandShape : e_program n_n_c_outputOperand = some (.variable n_n_c_outputClosure.parameter))
    (n_n_c_outputOperandFresh : n_n_c_outputClosure.parameter ≠ n_n_c_outputConstructor.contextBinder)
    (n_n_c_outputChildShape : e_program n_n_c_outputChildNode = some (.variable n_n_c_outputChildName))
    (n_n_c_outputParentShape : e_program n_n_c_outputParentCall = some (.apply n_n_c_outputParentFunction n_n_c_outputParentArguments))
    (n_n_c_outputOwnerShape : e_program n_n_c_outputOwnerNode = some (.variable n_n_c_outputOwnerName))
    (n_n_c_outputWantedShape : e_program n_n_c_outputWantedNode = some (.variable n_n_c_outputWantedName))
    (n_n_c_outputDestinationShape : e_program n_n_c_outputDestinationNode = some (.variable n_n_c_outputDestinationName))
    (n_n_c_outputBytesShape : e_program n_n_c_outputPayloadNode = some (.variable n_n_c_outputBytesName))
    (n_n_c_outputChildOuterFresh : n_n_c_outputChildName ≠ n_n_c_outputOuterPair.contextBinder)
    (n_n_c_outputOwnerOuterFresh : n_n_c_outputOwnerName ≠ n_n_c_outputOuterPair.contextBinder)
    (n_n_c_outputWantedOuterFresh : n_n_c_outputWantedName ≠ n_n_c_outputOuterPair.contextBinder)
    (n_n_c_outputDestinationOuterFresh : n_n_c_outputDestinationName ≠ n_n_c_outputOuterPair.contextBinder)
    (n_n_c_outputBytesOuterFresh : n_n_c_outputBytesName ≠ n_n_c_outputOuterPair.contextBinder)
    (n_n_c_outputChildFresh : n_n_c_outputChildName ≠ n_n_c_outputTuple.contextBinder)
    (n_n_c_outputOwnerFresh : n_n_c_outputOwnerName ≠ n_n_c_outputTuple.contextBinder)
    (n_n_c_outputWantedFresh : n_n_c_outputWantedName ≠ n_n_c_outputTuple.contextBinder)
    (n_n_c_outputDestinationFresh : n_n_c_outputDestinationName ≠ n_n_c_outputTuple.contextBinder)
    (n_n_c_outputBytesFresh : n_n_c_outputBytesName ≠ n_n_c_outputTuple.contextBinder)
    (n_n_c_outputOwnerParentFresh : n_n_c_outputOwnerName ≠ n_n_c_outputParentPair.contextBinder)
    (n_n_c_outputWantedParentFresh : n_n_c_outputWantedName ≠ n_n_c_outputParentPair.contextBinder)
    (n_n_c_outputParentOperandShape : e_program n_n_c_outputParentOperand = some (.variable n_n_c_outputParentClosure.parameter))
    (n_n_c_outputParentOperandFresh : n_n_c_outputParentClosure.parameter ≠ n_n_c_outputParentConstructor.contextBinder)
    (n_n_c_outputBindings : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → ∀ (s : Store) (p : Nat), CommitFrame middle s → ∀ work replacement remaining,
      let outputEnv := extend (extend (extend ((List.zip n_n_f_commitNames (n_n_f_commitNodes.map n_n_f_commitFieldValue)).reverse ++ extend n_n_f_commitCaptureEnv.reverse n_n_f_commitParameter (.location p)) n_n_c_workName work) n_n_c_replacementName replacement) n_n_c_remainingName remaining
      CoreEval.lookup outputEnv n_n_c_outputCallName = some (.location n_n_c_outputSelfAddress) ∧
      CoreEval.lookup outputEnv n_n_c_outputListName = some e_outputsValue ∧
      CoreEval.lookup outputEnv n_n_c_outputChildName = some work ∧
      CoreEval.lookup outputEnv n_n_c_outputOwnerName = some (.integer (Int.ofNat n_n_c_owner)) ∧
      CoreEval.lookup outputEnv n_n_c_outputWantedName = some n_o_wantedValue ∧
      CoreEval.lookup outputEnv n_n_c_outputDestinationName = some n_n_c_destination ∧
      CoreEval.lookup outputEnv n_n_c_outputBytesName = some n_n_c_bytes)
    (n_n_c_outputSelfBinding : CoreEval.lookup n_n_c_outputCaptureEnv.reverse n_n_c_outputChecked.functionName = some (.location n_n_c_outputSelfAddress))
    (n_n_c_outputCaptureBindings : CaptureBindings e_program n_n_c_outputChecked.captureNodes n_n_c_outputCaptureValues n_n_c_outputCaptureEnv)
    (n_n_c_outputSelfResolution : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → Resolve s n_n_c_outputSelfAddress n_n_c_outputSelfResolved)
    (n_n_c_outputSelfCell : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → readCell s n_n_c_outputSelfResolved = some (.closureCode n_n_c_outputChecked.code :: n_n_c_outputCaptureValues))
    (n_n_c_outputListRep : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → ∀ (s : Store) (_p : Nat), CommitFrame middle s → Children n_n_c_outputsList s e_outputsValue n_n_c_outputs)
    (n_n_c_outputLocated : Ash.NetworkLedger.CoreGenericInsert.LocatedEntries n_n_c_outputs)
    (n_n_c_counterBinding : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → ∀ (s : Store) (p : Nat), CommitFrame middle s → CoreEval.lookup ((List.zip n_n_f_commitNames (n_n_f_commitNodes.map n_n_f_commitFieldValue)).reverse ++ extend n_n_f_commitCaptureEnv.reverse n_n_f_commitParameter (.location p)) n_n_c_checkedResult.increment.counterBinder = some (.integer n_n_c_counter))
    (n_n_c_remainingBinder : n_n_c_checkedResult.remainingName = n_n_c_remainingName)
    (n_n_c_outgoingBinder : n_n_c_checkedResult.outgoingName = n_n_c_outgoingName)
    (n_n_c_childBinder : n_n_c_checkedResult.childName = n_n_c_workName)
    (n_n_c_counterWork : n_n_c_checkedResult.increment.counterBinder ≠ n_n_c_workName)
    (n_n_c_counterReplacement : n_n_c_checkedResult.increment.counterBinder ≠ n_n_c_replacementName)
    (n_n_c_counterRemaining : n_n_c_checkedResult.increment.counterBinder ≠ n_n_c_remainingName)
    (n_n_c_counterOutgoing : n_n_c_checkedResult.increment.counterBinder ≠ n_n_c_outgoingName)
    (n_n_c_workReplacement : n_n_c_workName ≠ n_n_c_replacementName)
    (n_n_c_workRemaining : n_n_c_workName ≠ n_n_c_remainingName)
    (n_n_c_workOutgoing : n_n_c_workName ≠ n_n_c_outgoingName)
    (n_n_c_remainingOutgoing : n_n_c_remainingName ≠ n_n_c_outgoingName)
    (n_n_c_noParent : Constructor)
    (n_n_c_ackOutTag : Constructor)
    (n_n_c_rejectedTag : Constructor)
    (n_n_c_bytesRep : Value → List UInt8 → Prop)
    (n_n_c_ledger : Ledger)
    (n_n_c_destinationNat : Nat)
    (n_n_c_payload : List UInt8)
    (n_n_c_ownerEq : n_n_c_ledger.owner = n_n_c_owner)
    (n_n_c_destinationEq : n_n_c_destination = .integer (Int.ofNat n_n_c_destinationNat))
    (n_n_c_rootSame : n_o_recordsList.root = n_n_c_ids.root)
    (n_n_c_workSame : n_o_recordsList.work = n_n_c_ids.work)
    (n_n_c_recordTagSame : n_n_c_updateProjection.record = n_n_f_recordTag)
    (n_n_c_bytesMeaning : n_n_c_bytesRep n_n_c_bytes n_n_c_payload)
    (entryLedgerTag : e_ledgerTag = n_n_c_checkedResult.ledgerTag)
    (entryCounter : e_nextValue = .integer n_n_c_counter)
    (entryRecords : Children n_o_recordsList e_start e_recordsValue n_o_records)
    (entryOutputs : Children n_n_c_outputsList e_start e_outputsValue n_n_c_outputs)
    (entryLedger : DecodedLedger n_n_c_ids n_o_recordsList n_n_c_outputsList n_n_c_checkedResult.ledgerTag n_n_f_recordTag n_n_c_noParent n_n_c_parentTag n_n_f_openTag n_n_f_closedTag n_n_c_workOutTag n_n_c_ackOutTag n_n_c_bytesRep e_start e_ledger n_n_c_ledger)
    :
    DecodedRegistrationResult n_n_c_ids n_o_recordsList n_n_c_outputsList n_n_c_checkedResult.ledgerTag n_n_f_recordTag n_n_c_noParent n_n_c_parentTag n_n_f_openTag n_n_f_closedTag
      n_n_c_workOutTag n_n_c_ackOutTag n_n_c_rejectedTag n_n_c_checkedResult.registeredTag n_n_c_bytesRep e_finish e_result
      (Ash.NetworkLedger.register n_n_c_ledger n_o_wanted n_n_c_destinationNat n_n_c_payload) := by
  obtain ⟨entryStore, entryPayload, frame, bodyEval⟩ := checked_registration_entry_call e_program e_call e_function e_argument e_nodes e_env e_start e_finish e_result e_functionName e_address e_resolved e_code e_context e_storage e_parameter e_body e_captureNodes e_captureValues e_captureEnv e_fieldValue e_tuple e_callShape e_functionShape e_functionBinding e_resolution e_cell e_closureShape e_captureBindings e_fieldShapes e_scrutinee e_ledgerMatch e_ledgerScrutinee e_lookupBranch e_names e_ledgerNames e_ledgerName e_ledgerTag e_ledger e_nextValue e_recordsValue e_outputsValue e_bodyShape e_scrutineeShape e_arity e_plain e_ledgerShape e_ledgerScrutineeShape e_ledgerBinding e_ledgerArity e_ledgerRep e_ledgerPlain e_bounded e_evaluation
  have inputFields : NominalFields n_n_c_checkedResult.ledgerTag e_start e_ledger [.integer n_n_c_counter, e_recordsValue, e_outputsValue] := by
    simpa [entryLedgerTag, entryCounter] using e_ledgerRep
  obtain ⟨counterEq, originalRecords, originalOutputs⟩ := decoded_ledger_fields n_n_c_ids n_o_recordsList n_n_c_outputsList
    n_n_c_checkedResult.ledgerTag n_n_f_recordTag n_n_c_noParent n_n_c_parentTag n_n_f_openTag n_n_f_closedTag
    n_n_c_workOutTag n_n_c_ackOutTag n_n_c_bytesRep e_start e_ledger e_recordsValue e_outputsValue n_n_c_counter n_n_c_ledger
    n_o_records n_n_c_outputs inputFields entryLedger entryRecords entryOutputs
  have recordLaw : ∀ middle, CommitFrame e_start middle → ∀ s (_p : Nat), CommitFrame middle s →
      RelatedValues (DecodedRecord n_n_c_ids n_n_f_recordTag n_n_c_noParent n_n_c_parentTag n_n_f_openTag n_n_f_closedTag s)
        n_o_records n_n_c_ledger.records := by
    intro mid first s _ second
    have retained := commit_frame_trans e_start mid s first second
    exact related_values_preserved _ _ _ _ originalRecords (fun value semantic rep =>
      decoded_record_retained _ _ _ _ _ _ _ _ value semantic retained.1 retained.2.2 rep)
  have outputLaw : ∀ middle, CommitFrame e_start middle → ∀ s (_p : Nat), CommitFrame middle s →
      RelatedValues (DecodedOutput n_n_c_ids n_n_c_noParent n_n_c_parentTag n_n_c_workOutTag n_n_c_ackOutTag n_n_c_bytesRep s)
        n_n_c_outputs n_n_c_ledger.outputs := by
    intro mid first s _ second
    have retained := commit_frame_trans e_start mid s first second
    exact related_values_preserved _ _ _ _ originalOutputs (fun value semantic rep =>
      decoded_output_retained _ _ _ _ _ _ _ _ value semantic retained.1 retained.2.2 rep)
  exact checked_lookup_finish_open_registration n_o_recordsList e_program n_o_absent n_o_present n_o_checked n_o_projection n_o_projectionFunctionName n_o_projectionEntryName n_o_projectionCode e_lookupBranch n_o_call n_o_missingBody n_o_foundBody n_o_function n_o_argument n_o_wantedNode n_o_listNode n_o_name n_o_callName n_o_wantedName n_o_listName ((List.zip e_ledgerNames [e_nextValue, e_recordsValue, e_outputsValue]).reverse ++ ((List.zip e_names (e_nodes.map e_fieldValue)).reverse ++ extend e_captureEnv.reverse e_parameter (.location entryPayload))) entryStore e_finish e_result n_o_wantedValue e_recordsValue n_o_found n_o_wanted n_o_records n_o_key n_o_selfAddress n_o_selfResolved n_o_comparisonAddress n_o_comparisonResolved n_o_projectionAddress n_o_projectionResolved n_o_captureValues n_o_captureEnv n_o_branchShape n_o_lookupPair n_o_callShape n_o_functionShape (n_o_functionBinding entryStore entryPayload frame) n_o_wantedShape n_o_listShape n_o_wantedFresh n_o_listFresh (n_o_wantedBinding entryStore entryPayload frame) (n_o_listBinding entryStore entryPayload frame) n_o_selfBinding n_o_comparisonBinding n_o_projectionBinding n_o_captureBindings (n_o_selfResolution entryStore entryPayload frame) (n_o_selfCell entryStore entryPayload frame) (n_o_comparisonResolution entryStore entryPayload frame) (n_o_comparisonCell entryStore entryPayload frame) (n_o_projectionResolution entryStore entryPayload frame) (n_o_projectionCell entryStore entryPayload frame) frame.2.1 (n_o_wantedRep entryStore entryPayload frame) (n_o_listRep entryStore entryPayload frame) (n_o_lookupKeys entryStore entryPayload frame) n_o_actualLookup bodyEval n_n_f_function n_n_f_argument n_n_f_nodes n_n_f_functionName n_n_f_address n_n_f_resolved n_n_f_code n_n_f_context n_n_f_storage n_n_f_parameter n_n_f_body n_n_f_captureNodes n_n_f_captureValues n_n_f_captureEnv n_n_f_fieldValue n_n_f_tuple n_n_f_callShape n_n_f_functionShape (n_n_f_functionBinding entryStore entryPayload frame) (n_n_f_resolution entryStore entryPayload frame) (n_n_f_cell entryStore entryPayload frame) n_n_f_closureShape n_n_f_captureBindings (n_n_f_fieldShapes entryStore entryPayload frame) n_n_f_scrutinee n_n_f_recordMatch n_n_f_recordScrutinee n_n_f_phaseBranch n_n_f_names n_n_f_recordNames n_n_f_recordName n_n_f_recordTag n_n_f_openTag n_n_f_closedTag n_n_f_foundKey n_n_f_parent n_n_f_phase n_n_f_children n_n_f_bodyShape n_n_f_scrutineeShape n_n_f_arity n_n_f_plain n_n_f_recordShape n_n_f_recordScrutineeShape n_n_f_recordBinding n_n_f_recordArity (n_n_f_recordRep entryStore entryPayload frame) n_n_f_recordPlain n_n_f_phaseAddress n_n_f_phaseResolved n_n_f_phaseEq (n_n_f_phaseResolution entryStore entryPayload frame) (n_n_f_phaseCell entryStore entryPayload frame) n_n_f_different n_n_f_phaseNode n_n_f_closedBody n_n_f_commitCall n_n_f_phaseName n_n_f_phaseShape n_n_f_phaseNodeShape n_n_f_phaseBinding n_n_f_commitFunction n_n_f_commitArgument n_n_f_commitScrutinee n_n_f_commitArm n_n_f_commitNodes n_n_f_commitName n_n_f_commitAddress n_n_f_commitResolved n_n_f_commitCode n_n_f_commitContext n_n_f_commitStorage n_n_f_commitParameter n_n_f_commitBody n_n_f_commitCaptureNodes n_n_f_commitCaptureValues n_n_f_commitCaptureEnv n_n_f_commitFieldValue n_n_f_commitTuple n_n_f_commitCallShape n_n_f_commitFunctionShape n_n_f_commitBinding (n_n_f_commitResolution entryStore entryPayload frame) (n_n_f_commitCell entryStore entryPayload frame) n_n_f_commitClosureShape n_n_f_commitCaptureBindings n_n_f_commitFieldShapes n_n_f_commitNames n_n_f_commitBodyShape n_n_f_commitScrutineeShape n_n_f_commitArity n_n_f_commitPlain (n_n_f_bounded entryStore entryPayload frame) n_n_c_ids n_n_c_outputsList n_n_c_buffers n_n_c_checkedResult n_n_c_second n_n_c_third n_n_c_fourth n_n_c_workNode n_n_c_replacementNode n_n_c_updateNode n_n_c_outputNode n_n_c_workName n_n_c_replacementName n_n_c_remainingName n_n_c_outgoingName n_n_c_workOutTag n_n_c_parentTag n_n_c_destination n_n_c_bytes n_n_c_owner n_n_c_counter n_n_c_children n_n_c_outputs n_n_c_firstShape n_n_c_secondShape n_n_c_thirdShape n_n_c_fourthShape n_n_c_nonnegative n_n_c_workFunction n_n_c_workArgument n_n_c_workOwnerNode n_n_c_workCounterNode n_n_c_workOperand n_n_c_workOwnerName n_n_c_workClosure n_n_c_workPair n_n_c_workConstructor n_n_c_workCallShape n_n_c_workOwnerShape n_n_c_workCounterShape n_n_c_workOwnerFresh n_n_c_workCounterFresh (n_n_c_workOwnerBinding entryStore entryPayload frame) n_n_c_workOperandShape n_n_c_workOperandFresh n_n_c_childChecked n_n_c_replacementFunction n_n_c_replacementArgument n_n_c_replacementWantedNode n_n_c_replacementParentNode n_n_c_replacementOpenNode n_n_c_childAppendNode n_n_c_replacementOperand n_n_c_childFunction n_n_c_childArgument n_n_c_childCall n_n_c_childListNode n_n_c_childConstructorFunction n_n_c_childConstructorArgument n_n_c_childIdNode n_n_c_childDestinationNode n_n_c_childOperand n_n_c_replacementWantedName n_n_c_replacementParentName n_n_c_childCallName n_n_c_childListName n_n_c_childIdName n_n_c_childDestinationName n_n_c_childSelfAddress n_n_c_childSelfResolved n_n_c_childCaptureValues n_n_c_childCaptureEnv n_n_c_replacementClosure n_n_c_replacementConstructor n_n_c_replacementTuple n_n_c_replacementOpenTuple n_n_c_childOuterPair n_n_c_childClosure n_n_c_childPair n_n_c_childConstructor n_n_c_replacementCallShape n_n_c_replacementOperandShape n_n_c_replacementOperandFresh n_n_c_replacementWantedShape n_n_c_replacementParentShape n_n_c_replacementWantedFresh n_n_c_replacementParentFresh n_n_c_childAppendShape n_n_c_childFunctionShape n_n_c_childListShape n_n_c_childListFresh n_n_c_childCallShape n_n_c_childIdShape n_n_c_childDestinationShape n_n_c_childIdOuterFresh n_n_c_childDestinationOuterFresh n_n_c_childIdFresh n_n_c_childDestinationFresh n_n_c_childOperandShape n_n_c_childOperandFresh (n_n_c_replacementBindings entryStore entryPayload frame) (n_n_c_childBindings entryStore entryPayload frame) n_n_c_childSelfBinding n_n_c_childCaptureBindings (n_n_c_childSelfResolution entryStore entryPayload frame) (n_n_c_childSelfCell entryStore entryPayload frame) (n_n_c_childListRep entryStore entryPayload frame) n_n_c_childLocated n_n_c_updateChecked n_n_c_updateProjection n_n_c_updateProjectionName n_n_c_updateEntryName n_n_c_updateProjectionCode n_n_c_updateFunction n_n_c_updateArgument n_n_c_updateWantedNode n_n_c_updateReplacementNode n_n_c_updateListNode n_n_c_updateCallName n_n_c_updateWantedName n_n_c_updateReplacementName n_n_c_updateListName n_n_c_updateSelfAddress n_n_c_updateSelfResolved n_n_c_updateComparisonAddress n_n_c_updateComparisonResolved n_n_c_updateProjectionAddress n_n_c_updateProjectionResolved n_n_c_updateCaptureValues n_n_c_updateCaptureEnv n_n_c_updateTriple n_n_c_updateCallShape n_n_c_updateFunctionShape n_n_c_updateWantedShape n_n_c_updateReplacementShape n_n_c_updateListShape n_n_c_updateWantedFresh n_n_c_updateReplacementFresh n_n_c_updateListFresh n_n_c_updateList (n_n_c_updateBindings entryStore entryPayload frame) n_n_c_updateSelfBinding n_n_c_updateComparisonBinding n_n_c_updateProjectionBinding n_n_c_updateCaptureBindings (n_n_c_updateSelfResolution entryStore entryPayload frame) (n_n_c_updateSelfCell entryStore entryPayload frame) (n_n_c_updateComparisonResolution entryStore entryPayload frame) (n_n_c_updateComparisonCell entryStore entryPayload frame) (n_n_c_updateProjectionResolution entryStore entryPayload frame) (n_n_c_updateProjectionCell entryStore entryPayload frame) (n_n_c_updateWantedRep entryStore entryPayload frame) (n_n_c_updateListRep entryStore entryPayload frame) (n_n_c_updateKeys entryStore entryPayload frame) n_n_c_outputChecked n_n_c_outputFunction n_n_c_outputArgument n_n_c_outputCall n_n_c_outputListNode n_n_c_outputConstructorFunction n_n_c_outputConstructorArgument n_n_c_outputChildNode n_n_c_outputParentCall n_n_c_outputDestinationNode n_n_c_outputPayloadNode n_n_c_outputParentFunction n_n_c_outputParentArguments n_n_c_outputOwnerNode n_n_c_outputWantedNode n_n_c_outputParentOperand n_n_c_outputOperand n_n_c_outputCallName n_n_c_outputListName n_n_c_outputChildName n_n_c_outputOwnerName n_n_c_outputWantedName n_n_c_outputDestinationName n_n_c_outputBytesName n_n_c_outputSelfAddress n_n_c_outputSelfResolved n_n_c_outputCaptureValues n_n_c_outputCaptureEnv n_n_c_outputOuterPair n_n_c_outputClosure n_n_c_outputConstructor n_n_c_outputTuple n_n_c_outputParentClosure n_n_c_outputParentPair n_n_c_outputParentConstructor n_n_c_outputCallShape n_n_c_outputFunctionShape n_n_c_outputListShape n_n_c_outputListFresh n_n_c_outputShape n_n_c_outputOperandShape n_n_c_outputOperandFresh n_n_c_outputChildShape n_n_c_outputParentShape n_n_c_outputOwnerShape n_n_c_outputWantedShape n_n_c_outputDestinationShape n_n_c_outputBytesShape n_n_c_outputChildOuterFresh n_n_c_outputOwnerOuterFresh n_n_c_outputWantedOuterFresh n_n_c_outputDestinationOuterFresh n_n_c_outputBytesOuterFresh n_n_c_outputChildFresh n_n_c_outputOwnerFresh n_n_c_outputWantedFresh n_n_c_outputDestinationFresh n_n_c_outputBytesFresh n_n_c_outputOwnerParentFresh n_n_c_outputWantedParentFresh n_n_c_outputParentOperandShape n_n_c_outputParentOperandFresh e_outputsValue (n_n_c_outputBindings entryStore entryPayload frame) n_n_c_outputSelfBinding n_n_c_outputCaptureBindings (n_n_c_outputSelfResolution entryStore entryPayload frame) (n_n_c_outputSelfCell entryStore entryPayload frame) (n_n_c_outputListRep entryStore entryPayload frame) n_n_c_outputLocated (n_n_c_counterBinding entryStore entryPayload frame) n_n_c_remainingBinder n_n_c_outgoingBinder n_n_c_childBinder n_n_c_counterWork n_n_c_counterReplacement n_n_c_counterRemaining n_n_c_counterOutgoing n_n_c_workReplacement n_n_c_workRemaining n_n_c_workOutgoing n_n_c_remainingOutgoing n_n_c_noParent n_n_c_ackOutTag n_n_c_rejectedTag n_n_c_bytesRep n_n_c_ledger n_n_c_destinationNat n_n_c_payload n_n_c_ownerEq counterEq n_n_c_destinationEq n_n_c_rootSame n_n_c_workSame n_n_c_recordTagSame (fun inner innerFrame s p afterFrame => recordLaw inner (commit_frame_trans e_start entryStore inner frame innerFrame) s p afterFrame) (fun inner innerFrame s p afterFrame => outputLaw inner (commit_frame_trans e_start entryStore inner frame innerFrame) s p afterFrame) n_n_c_bytesMeaning

/-- The actual entry, lookup hit and stored finish return the decoded closed rejection. -/
theorem checked_entry_closed_registration
    (e_program : Program)
    (e_call e_function e_argument : NodeId)
    (e_nodes : List NodeId)
    (e_env : Environment)
    (e_start e_finish : Store)
    (e_result : Value)
    (e_functionName : Binder)
    (e_address e_resolved e_code e_context e_storage e_parameter e_body : Nat)
    (e_captureNodes : List NodeId)
    (e_captureValues : List Value)
    (e_captureEnv : Environment)
    (e_fieldValue : NodeId → Value)
    (e_tuple : CheckedTuple e_program e_argument none e_nodes)
    (e_callShape : e_program e_call = some (.apply e_function e_argument))
    (e_functionShape : e_program e_function = some (.variable e_functionName))
    (e_functionBinding : CoreEval.lookup e_env e_functionName = some (.location e_address))
    (e_resolution : Resolve e_start e_address e_resolved)
    (e_cell : readCell e_start e_resolved = some (.closureCode e_code :: e_captureValues))
    (e_closureShape : e_program e_code = some (.closure e_context e_captureNodes e_storage e_parameter e_body))
    (e_captureBindings : CaptureBindings e_program e_captureNodes e_captureValues e_captureEnv)
    (e_fieldShapes : ∀ node ∈ e_nodes, ∃ name, e_program node = some (.variable name) ∧
      CoreEval.lookup (extend e_env e_tuple.contextBinder .context) name = some (e_fieldValue node))
    (e_scrutinee e_ledgerMatch e_ledgerScrutinee e_lookupBranch : NodeId)
    (e_names e_ledgerNames : List Binder)
    (e_ledgerName : Binder)
    (e_ledgerTag : Constructor)
    (e_ledger e_nextValue e_recordsValue e_outputsValue : Value)
    (e_bodyShape : e_program e_body = some (.caseMatch e_scrutinee [(.tuple (e_names.map Pattern.binder), e_ledgerMatch)]))
    (e_scrutineeShape : e_program e_scrutinee = some (.variable e_parameter))
    (e_arity : e_names.length = (e_nodes.map e_fieldValue).length)
    (e_plain : tupleFields (e_nodes.map e_fieldValue) = some (e_nodes.map e_fieldValue))
    (e_ledgerShape : e_program e_ledgerMatch = some (.caseMatch e_ledgerScrutinee
      [(.constructor e_ledgerTag (some (.tuple (e_ledgerNames.map Pattern.binder))), e_lookupBranch)]))
    (e_ledgerScrutineeShape : e_program e_ledgerScrutinee = some (.variable e_ledgerName))
    (e_ledgerBinding : ∀ payload,
      CoreEval.lookup ((List.zip e_names (e_nodes.map e_fieldValue)).reverse ++
        extend e_captureEnv.reverse e_parameter (.location payload)) e_ledgerName = some e_ledger)
    (e_ledgerArity : e_ledgerNames.length = 3)
    (e_ledgerRep : NominalFields e_ledgerTag e_start e_ledger [e_nextValue, e_recordsValue, e_outputsValue])
    (e_ledgerPlain : tupleFields [e_nextValue, e_recordsValue, e_outputsValue] = some [e_nextValue, e_recordsValue, e_outputsValue])
    (e_bounded : BoundedLocations e_start)
    (e_evaluation : Eval e_program e_env e_call e_start e_result e_finish)
    (n_o_recordsList : Constructors)
    (n_o_absent : Constructor)
    (n_o_present : Constructor)
    (n_o_checked : CheckedLookupBase n_o_recordsList e_program n_o_absent n_o_present)
    (n_o_projection : RecordProjectionShape e_program n_o_checked.projection)
    (n_o_projectionFunctionName : n_o_projection.functionName = n_o_checked.projectionName)
    (n_o_projectionEntryName : n_o_projection.recordName = n_o_checked.entryName)
    (n_o_projectionCode : n_o_projection.code = n_o_checked.projectionCode)
    (n_o_call : NodeId)
    (n_o_missingBody : NodeId)
    (n_o_foundBody : NodeId)
    (n_o_function : NodeId)
    (n_o_argument : NodeId)
    (n_o_wantedNode : NodeId)
    (n_o_listNode : NodeId)
    (n_o_name : Binder)
    (n_o_callName : Binder)
    (n_o_wantedName : Binder)
    (n_o_listName : Binder)
    (n_o_wantedValue : Value)
    (n_o_found : Value)
    (n_o_wanted : Id)
    (n_o_records : List Value)
    (n_o_key : Value → Id)
    (n_o_selfAddress : Nat)
    (n_o_selfResolved : Nat)
    (n_o_comparisonAddress : Nat)
    (n_o_comparisonResolved : Nat)
    (n_o_projectionAddress : Nat)
    (n_o_projectionResolved : Nat)
    (n_o_captureValues : List Value)
    (n_o_captureEnv : Environment)
    (n_o_branchShape : e_program e_lookupBranch = some (.caseMatch n_o_call
      [(.constructor n_o_absent none, n_o_missingBody), (.constructor n_o_present (some (.binder n_o_name)), n_o_foundBody)]))
    (n_o_lookupPair : CheckedTuple e_program n_o_argument none [n_o_wantedNode, n_o_listNode])
    (n_o_callShape : e_program n_o_call = some (.apply n_o_function n_o_argument))
    (n_o_functionShape : e_program n_o_function = some (.variable n_o_callName))
    (n_o_functionBinding : ∀ (entryStore : Store) (entryPayload : Nat), CommitFrame e_start entryStore → CoreEval.lookup ((List.zip e_ledgerNames [e_nextValue, e_recordsValue, e_outputsValue]).reverse ++ ((List.zip e_names (e_nodes.map e_fieldValue)).reverse ++ extend e_captureEnv.reverse e_parameter (.location entryPayload))) n_o_callName = some (.location n_o_selfAddress))
    (n_o_wantedShape : e_program n_o_wantedNode = some (.variable n_o_wantedName))
    (n_o_listShape : e_program n_o_listNode = some (.variable n_o_listName))
    (n_o_wantedFresh : n_o_wantedName ≠ n_o_lookupPair.contextBinder)
    (n_o_listFresh : n_o_listName ≠ n_o_lookupPair.contextBinder)
    (n_o_wantedBinding : ∀ (entryStore : Store) (entryPayload : Nat), CommitFrame e_start entryStore → CoreEval.lookup ((List.zip e_ledgerNames [e_nextValue, e_recordsValue, e_outputsValue]).reverse ++ ((List.zip e_names (e_nodes.map e_fieldValue)).reverse ++ extend e_captureEnv.reverse e_parameter (.location entryPayload))) n_o_wantedName = some n_o_wantedValue)
    (n_o_listBinding : ∀ (entryStore : Store) (entryPayload : Nat), CommitFrame e_start entryStore → CoreEval.lookup ((List.zip e_ledgerNames [e_nextValue, e_recordsValue, e_outputsValue]).reverse ++ ((List.zip e_names (e_nodes.map e_fieldValue)).reverse ++ extend e_captureEnv.reverse e_parameter (.location entryPayload))) n_o_listName = some e_recordsValue)
    (n_o_selfBinding : CoreEval.lookup n_o_captureEnv.reverse n_o_checked.functionName = some (.location n_o_selfAddress))
    (n_o_comparisonBinding : CoreEval.lookup n_o_captureEnv.reverse n_o_checked.comparisonName = some (.location n_o_comparisonAddress))
    (n_o_projectionBinding : CoreEval.lookup n_o_captureEnv.reverse n_o_checked.projectionName = some (.location n_o_projectionAddress))
    (n_o_captureBindings : CaptureBindings e_program n_o_checked.captureNodes n_o_captureValues n_o_captureEnv)
    (n_o_selfResolution : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → Resolve entryStore n_o_selfAddress n_o_selfResolved)
    (n_o_selfCell : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → readCell entryStore n_o_selfResolved = some (.closureCode n_o_checked.code :: n_o_captureValues))
    (n_o_comparisonResolution : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → Resolve entryStore n_o_comparisonAddress n_o_comparisonResolved)
    (n_o_comparisonCell : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → readCell entryStore n_o_comparisonResolved = some [.closureCode n_o_checked.comparator.code])
    (n_o_projectionResolution : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → Resolve entryStore n_o_projectionAddress n_o_projectionResolved)
    (n_o_projectionCell : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → readCell entryStore n_o_projectionResolved = some [.closureCode n_o_checked.projectionCode])
    (n_o_wantedRep : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → Ident n_o_recordsList entryStore n_o_wantedValue n_o_wanted)
    (n_o_listRep : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → Children n_o_recordsList entryStore e_recordsValue n_o_records)
    (n_o_lookupKeys : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → RepresentedEntries n_o_recordsList (RecordEntry n_o_projection.record) entryStore n_o_key n_o_records)
    (n_o_actualLookup : Ash.NetworkLedger.lookup n_o_key n_o_wanted n_o_records = some n_o_found)
    (n_n_ids : Constructors)
    (n_n_outputsList : Constructors)
    (n_n_recordTag : Constructor)
    (n_n_noParent : Constructor)
    (n_n_parentTag : Constructor)
    (n_n_openTag : Constructor)
    (n_n_closedTag : Constructor)
    (n_n_workOutTag : Constructor)
    (n_n_ackOutTag : Constructor)
    (n_n_rejectedTag : Constructor)
    (n_n_registeredTag : Constructor)
    (n_n_bytesRep : Value → List UInt8 → Prop)
    (n_n_function : NodeId)
    (n_n_argument : NodeId)
    (n_n_nodes : List NodeId)
    (n_n_functionName : Binder)
    (n_n_address : Nat)
    (n_n_resolved : Nat)
    (n_n_code : Nat)
    (n_n_context : Nat)
    (n_n_storage : Nat)
    (n_n_parameter : Nat)
    (n_n_body : Nat)
    (n_n_captureNodes : List NodeId)
    (n_n_captureValues : List Value)
    (n_n_captureEnv : Environment)
    (n_n_fieldValue : NodeId → Value)
    (n_n_tuple : CheckedTuple e_program n_n_argument none n_n_nodes)
    (n_n_callShape : e_program n_o_foundBody = some (.apply n_n_function n_n_argument))
    (n_n_functionShape : e_program n_n_function = some (.variable n_n_functionName))
    (n_n_functionBinding : ∀ (entryStore : Store) (entryPayload : Nat), CommitFrame e_start entryStore → CoreEval.lookup (extend ((List.zip e_ledgerNames [e_nextValue, e_recordsValue, e_outputsValue]).reverse ++ ((List.zip e_names (e_nodes.map e_fieldValue)).reverse ++ extend e_captureEnv.reverse e_parameter (.location entryPayload))) n_o_name n_o_found) n_n_functionName = some (.location n_n_address))
    (n_n_resolution : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → Resolve middle n_n_address n_n_resolved)
    (n_n_cell : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → readCell middle n_n_resolved = some (.closureCode n_n_code :: n_n_captureValues))
    (n_n_closureShape : e_program n_n_code = some (.closure n_n_context n_n_captureNodes n_n_storage n_n_parameter n_n_body))
    (n_n_captureBindings : CaptureBindings e_program n_n_captureNodes n_n_captureValues n_n_captureEnv)
    (n_n_fieldShapes : ∀ (entryStore : Store) (entryPayload : Nat), CommitFrame e_start entryStore → ∀ node ∈ n_n_nodes, ∃ name, e_program node = some (.variable name) ∧
      CoreEval.lookup (extend (extend ((List.zip e_ledgerNames [e_nextValue, e_recordsValue, e_outputsValue]).reverse ++ ((List.zip e_names (e_nodes.map e_fieldValue)).reverse ++ extend e_captureEnv.reverse e_parameter (.location entryPayload))) n_o_name n_o_found) n_n_tuple.contextBinder .context) name = some (n_n_fieldValue node))
    (n_n_scrutinee : NodeId)
    (n_n_recordMatch : NodeId)
    (n_n_recordScrutinee : NodeId)
    (n_n_phaseBranch : NodeId)
    (n_n_names : List Binder)
    (n_n_recordNames : List Binder)
    (n_n_recordName : Binder)
    (n_n_foundKey : Value)
    (n_n_parent : Value)
    (n_n_phase : Value)
    (n_n_childList : Value)
    (n_n_ledger : Ledger)
    (n_n_bodyShape : e_program n_n_body = some (.caseMatch n_n_scrutinee [(.tuple (n_n_names.map Pattern.binder), n_n_recordMatch)]))
    (n_n_scrutineeShape : e_program n_n_scrutinee = some (.variable n_n_parameter))
    (n_n_arity : n_n_names.length = (n_n_nodes.map n_n_fieldValue).length)
    (n_n_plain : tupleFields (n_n_nodes.map n_n_fieldValue) = some (n_n_nodes.map n_n_fieldValue))
    (n_n_recordShape : e_program n_n_recordMatch = some (.caseMatch n_n_recordScrutinee
      [(.constructor n_n_recordTag (some (.tuple (n_n_recordNames.map Pattern.binder))), n_n_phaseBranch)]))
    (n_n_recordScrutineeShape : e_program n_n_recordScrutinee = some (.variable n_n_recordName))
    (n_n_recordBinding : ∀ payload, CoreEval.lookup ((List.zip n_n_names (n_n_nodes.map n_n_fieldValue)).reverse ++
      extend n_n_captureEnv.reverse n_n_parameter (.location payload)) n_n_recordName = some n_o_found)
    (n_n_recordArity : n_n_recordNames.length = 4)
    (n_n_recordRep : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → NominalFields n_n_recordTag middle n_o_found [n_n_foundKey, n_n_parent, n_n_phase, n_n_childList])
    (n_n_recordPlain : tupleFields [n_n_foundKey, n_n_parent, n_n_phase, n_n_childList] = some [n_n_foundKey, n_n_parent, n_n_phase, n_n_childList])
    (n_n_destination : Nat)
    (n_n_payloadBytes : List UInt8)
    (n_n_phaseAddress : Nat)
    (n_n_phaseResolved : Nat)
    (n_n_phaseEq : n_n_phase = .location n_n_phaseAddress)
    (n_n_phaseResolution : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → Resolve middle n_n_phaseAddress n_n_phaseResolved)
    (n_n_phaseCell : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → readCell middle n_n_phaseResolved = some [.tag n_n_closedTag])
    (n_n_rootSame : n_o_recordsList.root = n_n_ids.root)
    (n_n_workSame : n_o_recordsList.work = n_n_ids.work)
    (n_n_different : n_n_openTag ≠ n_n_closedTag)
    (n_n_represented : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → RepresentedEntries n_o_recordsList (RecordEntry n_n_recordTag) middle n_o_key n_o_records)
    (n_n_recordValues : ∀ (entryStore : Store) (_entryPayload : Nat), CommitFrame e_start entryStore → ∀ (middle : Store), CommitFrame entryStore middle → RelatedValues (DecodedRecord n_n_ids n_n_recordTag n_n_noParent n_n_parentTag n_n_openTag n_n_closedTag middle) n_o_records n_n_ledger.records)
    (n_n_phaseNode : NodeId)
    (n_n_closedBody : NodeId)
    (n_n_openBody : NodeId)
    (n_n_ledgerNode : NodeId)
    (n_n_statusNode : NodeId)
    (n_n_phaseName : Binder)
    (n_n_ledgerName : Binder)
    (n_n_phaseShape : e_program n_n_phaseBranch = some (.caseMatch n_n_phaseNode
      [(.constructor n_n_closedTag none, n_n_closedBody), (.constructor n_n_openTag none, n_n_openBody)]))
    (n_n_phaseNodeShape : e_program n_n_phaseNode = some (.variable n_n_phaseName))
    (n_n_phaseBinding : ∀ payload, CoreEval.lookup ((List.zip n_n_recordNames [n_n_foundKey, n_n_parent, n_n_phase, n_n_childList]).reverse ++
      ((List.zip n_n_names (n_n_nodes.map n_n_fieldValue)).reverse ++ extend n_n_captureEnv.reverse n_n_parameter (.location payload))) n_n_phaseName = some n_n_phase)
    (n_n_resultPair : CheckedTuple e_program n_n_closedBody none [n_n_ledgerNode, n_n_statusNode])
    (n_n_status : CheckedTuple e_program n_n_statusNode (some n_n_rejectedTag) [])
    (n_n_ledgerShape : e_program n_n_ledgerNode = some (.variable n_n_ledgerName))
    (n_n_ledgerFresh : n_n_ledgerName ≠ n_n_resultPair.contextBinder)
    (n_n_ledgerBinding : ∀ payload, CoreEval.lookup ((List.zip n_n_recordNames [n_n_foundKey, n_n_parent, n_n_phase, n_n_childList]).reverse ++
      ((List.zip n_n_names (n_n_nodes.map n_n_fieldValue)).reverse ++ extend n_n_captureEnv.reverse n_n_parameter (.location payload))) n_n_ledgerName = some e_ledger)
    (entryLedger : DecodedLedger n_n_ids n_o_recordsList n_n_outputsList e_ledgerTag n_n_recordTag n_n_noParent n_n_parentTag n_n_openTag n_n_closedTag n_n_workOutTag n_n_ackOutTag n_n_bytesRep e_start e_ledger n_n_ledger)
    :
    DecodedRegistrationResult n_n_ids n_o_recordsList n_n_outputsList e_ledgerTag n_n_recordTag n_n_noParent n_n_parentTag n_n_openTag n_n_closedTag n_n_workOutTag n_n_ackOutTag
      n_n_rejectedTag n_n_registeredTag n_n_bytesRep e_finish e_result (Ash.NetworkLedger.register n_n_ledger n_o_wanted n_n_destination n_n_payloadBytes) := by
  obtain ⟨entryStore, entryPayload, frame, bodyEval⟩ := checked_registration_entry_call e_program e_call e_function e_argument e_nodes e_env e_start e_finish e_result e_functionName e_address e_resolved e_code e_context e_storage e_parameter e_body e_captureNodes e_captureValues e_captureEnv e_fieldValue e_tuple e_callShape e_functionShape e_functionBinding e_resolution e_cell e_closureShape e_captureBindings e_fieldShapes e_scrutinee e_ledgerMatch e_ledgerScrutinee e_lookupBranch e_names e_ledgerNames e_ledgerName e_ledgerTag e_ledger e_nextValue e_recordsValue e_outputsValue e_bodyShape e_scrutineeShape e_arity e_plain e_ledgerShape e_ledgerScrutineeShape e_ledgerBinding e_ledgerArity e_ledgerRep e_ledgerPlain e_bounded e_evaluation
  exact checked_lookup_finish_closed_registration n_o_recordsList e_program n_o_absent n_o_present n_o_checked n_o_projection n_o_projectionFunctionName n_o_projectionEntryName n_o_projectionCode e_lookupBranch n_o_call n_o_missingBody n_o_foundBody n_o_function n_o_argument n_o_wantedNode n_o_listNode n_o_name n_o_callName n_o_wantedName n_o_listName ((List.zip e_ledgerNames [e_nextValue, e_recordsValue, e_outputsValue]).reverse ++ ((List.zip e_names (e_nodes.map e_fieldValue)).reverse ++ extend e_captureEnv.reverse e_parameter (.location entryPayload))) entryStore e_finish e_result n_o_wantedValue e_recordsValue n_o_found n_o_wanted n_o_records n_o_key n_o_selfAddress n_o_selfResolved n_o_comparisonAddress n_o_comparisonResolved n_o_projectionAddress n_o_projectionResolved n_o_captureValues n_o_captureEnv n_o_branchShape n_o_lookupPair n_o_callShape n_o_functionShape (n_o_functionBinding entryStore entryPayload frame) n_o_wantedShape n_o_listShape n_o_wantedFresh n_o_listFresh (n_o_wantedBinding entryStore entryPayload frame) (n_o_listBinding entryStore entryPayload frame) n_o_selfBinding n_o_comparisonBinding n_o_projectionBinding n_o_captureBindings (n_o_selfResolution entryStore entryPayload frame) (n_o_selfCell entryStore entryPayload frame) (n_o_comparisonResolution entryStore entryPayload frame) (n_o_comparisonCell entryStore entryPayload frame) (n_o_projectionResolution entryStore entryPayload frame) (n_o_projectionCell entryStore entryPayload frame) frame.2.1 (n_o_wantedRep entryStore entryPayload frame) (n_o_listRep entryStore entryPayload frame) (n_o_lookupKeys entryStore entryPayload frame) n_o_actualLookup bodyEval n_n_ids n_n_outputsList e_ledgerTag n_n_recordTag n_n_noParent n_n_parentTag n_n_openTag n_n_closedTag n_n_workOutTag n_n_ackOutTag n_n_rejectedTag n_n_registeredTag n_n_bytesRep n_n_function n_n_argument n_n_nodes n_n_functionName n_n_address n_n_resolved n_n_code n_n_context n_n_storage n_n_parameter n_n_body n_n_captureNodes n_n_captureValues n_n_captureEnv n_n_fieldValue n_n_tuple n_n_callShape n_n_functionShape (n_n_functionBinding entryStore entryPayload frame) (n_n_resolution entryStore entryPayload frame) (n_n_cell entryStore entryPayload frame) n_n_closureShape n_n_captureBindings (n_n_fieldShapes entryStore entryPayload frame) n_n_scrutinee n_n_recordMatch n_n_recordScrutinee n_n_phaseBranch n_n_names n_n_recordNames n_n_recordName n_n_foundKey n_n_parent n_n_phase n_n_childList e_ledger n_n_ledger n_n_bodyShape n_n_scrutineeShape n_n_arity n_n_plain n_n_recordShape n_n_recordScrutineeShape n_n_recordBinding n_n_recordArity (n_n_recordRep entryStore entryPayload frame) n_n_recordPlain n_n_destination n_n_payloadBytes n_n_phaseAddress n_n_phaseResolved n_n_phaseEq (n_n_phaseResolution entryStore entryPayload frame) (n_n_phaseCell entryStore entryPayload frame) n_n_rootSame n_n_workSame n_n_different (n_n_represented entryStore entryPayload frame) (n_n_recordValues entryStore entryPayload frame) n_n_phaseNode n_n_closedBody n_n_openBody n_n_ledgerNode n_n_statusNode n_n_phaseName n_n_ledgerName n_n_phaseShape n_n_phaseNodeShape n_n_phaseBinding n_n_resultPair n_n_status n_n_ledgerShape n_n_ledgerFresh n_n_ledgerBinding (fun inner innerFrame => decoded_ledger_retained n_n_ids n_o_recordsList n_n_outputsList e_ledgerTag n_n_recordTag n_n_noParent n_n_parentTag n_n_openTag n_n_closedTag n_n_workOutTag n_n_ackOutTag n_n_bytesRep e_start inner e_ledger n_n_ledger (commit_frame_trans e_start entryStore inner frame innerFrame).1 (commit_frame_trans e_start entryStore inner frame innerFrame).2.2 entryLedger)

end Ash.NetworkLedger.CoreRecordRegistration
