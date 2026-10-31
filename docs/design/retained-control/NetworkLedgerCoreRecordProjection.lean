import NetworkLedgerCoreValues

/- Exact normal execution of the four-field Record key projection. The linked
   body, actual heap representation and caller bindings remain premises. -/
namespace Ash.NetworkLedger.CoreRecordProjection

open Ash.NetworkLedger.CoreEval
open Ash.NetworkLedger.CoreValues

/-- The four actual fields bind in source order, retaining the entire values. -/
theorem record_fields_match (store : Store) (address resolved : Nat)
    (keyName parentName phaseName childrenName : Binder)
    (key parent phase children : Value)
    (resolution : Resolve store address resolved)
    (cell : readCell store resolved = some [key, parent, phase, children])
    (plain : tupleFields [key, parent, phase, children] = some [key, parent, phase, children])
    {result : Option Environment}
    (attempt : Attempt store (.tuple [.binder keyName, .binder parentName, .binder phaseName,
      .binder childrenName]) (.location address) result) :
    result = some [(keyName, key), (parentName, parent), (phaseName, phase),
      (childrenName, children)] := by
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
        cases tail with
        | hit _ _ _ _ third rest head tail =>
          cases head
          cases tail with
          | hit _ _ _ _ fourth rest head tail =>
            cases head
            cases tail
            rfl

/-- The selected Record constructor binds its original payload fields. -/
theorem record_constructor_match (store : Store) (tag : Constructor)
    (address resolved payload tuple keyAddress : Nat) (parent phase children : Value)
    (keyName parentName phaseName childrenName : Binder)
    (resolution : Resolve store address resolved)
    (cell : readCell store resolved = some [.tag tag, .location payload])
    (payloadResolution : Resolve store payload tuple)
    (fields : readCell store tuple = some [.location keyAddress, parent, phase, children])
    {result : Option Environment}
    (attempt : Attempt store (.constructor tag (some (.tuple [.binder keyName, .binder parentName,
      .binder phaseName, .binder childrenName]))) (.location address) result) :
    result = some [(keyName, .location keyAddress), (parentName, parent),
      (phaseName, phase), (childrenName, children)] := by
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
    exact record_fields_match store payload tuple keyName parentName phaseName childrenName
      (.location keyAddress) parent phase children payloadResolution fields rfl inner
  | constructorMissingPayload _ _ _ other stored otherResolution otherRead view =>
    have equal := resolved_fields_unique resolution otherResolution cell otherRead
    subst stored
    simp [constructorFields] at view

/-- Normal execution of the checked projection returns the original key and store. -/
theorem record_projection_returns_key (program : Program) (store finish : Store)
    (env : Environment) (node scrutinee body : NodeId)
    (parameter keyName parentName phaseName childrenName : Binder) (tag : Constructor)
    (address resolved payload tuple keyAddress : Nat) (parent phase children result : Value)
    (differentParent : keyName ≠ parentName) (differentPhase : keyName ≠ phaseName)
    (differentChildren : keyName ≠ childrenName)
    (shape : program node = some (.caseMatch scrutinee
      [(.constructor tag (some (.tuple [.binder keyName, .binder parentName, .binder phaseName,
        .binder childrenName])), body)]))
    (scrutineeShape : program scrutinee = some (.variable parameter))
    (bodyShape : program body = some (.variable keyName))
    (binding : CoreEval.lookup env parameter = some (.location address))
    (resolution : Resolve store address resolved)
    (cell : readCell store resolved = some [.tag tag, .location payload])
    (payloadResolution : Resolve store payload tuple)
    (fields : readCell store tuple = some [.location keyAddress, parent, phase, children])
    (evaluation : Eval program env node store result finish) :
    result = .location keyAddress ∧ finish = store := by
  obtain ⟨middle, value, chosen, bindings, scrutineeEval, selected, bodyEval⟩ :=
    case_match_inversion shape evaluation
  obtain ⟨actualBinding, sameStore⟩ := variable_inversion scrutineeShape scrutineeEval
  have sameValue : value = .location address := by simp_all
  subst value
  subst middle
  have selectedFacts : chosen = body ∧ bindings = [(keyName, .location keyAddress),
      (parentName, parent), (phaseName, phase), (childrenName, children)] := by
    cases selected with
    | first _ _ _ actual hit =>
      have same := record_constructor_match store tag address resolved payload tuple keyAddress
        parent phase children keyName parentName phaseName childrenName resolution cell
        payloadResolution fields hit
      cases same
      exact ⟨rfl, rfl⟩
    | later _ _ _ _ _ _ next => cases next
  rcases selectedFacts with ⟨rfl, rfl⟩
  obtain ⟨found, unchanged⟩ := variable_inversion bodyShape bodyEval
  simp [CoreEval.lookup, Ne.symm differentParent, Ne.symm differentPhase,
    Ne.symm differentChildren] at found
  exact ⟨found.symm, unchanged⟩

/-- An actual call through the checked stored projection preserves the same key and store. -/
theorem record_projection_call (program : Program) (store finish : Store) (env : Environment)
    (call function argument code context storage parameter body scrutinee returnKey : NodeId)
    (functionName recordName keyName parentName phaseName childrenName : Binder) (tag : Constructor)
    (functionAddress functionResolved recordAddress recordResolved payload tuple keyAddress : Nat)
    (parent phase children result : Value)
    (shape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable functionName))
    (argumentShape : program argument = some (.variable recordName))
    (functionBinding : CoreEval.lookup env functionName = some (.location functionAddress))
    (recordBinding : CoreEval.lookup env recordName = some (.location recordAddress))
    (functionResolution : Resolve store functionAddress functionResolved)
    (functionCell : readCell store functionResolved = some [.closureCode code])
    (closureShape : program code = some (.closure context [] storage parameter body))
    (differentParent : keyName ≠ parentName) (differentPhase : keyName ≠ phaseName)
    (differentChildren : keyName ≠ childrenName)
    (bodyShape : program body = some (.caseMatch scrutinee
      [(.constructor tag (some (.tuple [.binder keyName, .binder parentName, .binder phaseName,
        .binder childrenName])), returnKey)]))
    (scrutineeShape : program scrutinee = some (.variable parameter))
    (returnShape : program returnKey = some (.variable keyName))
    (recordResolution : Resolve store recordAddress recordResolved)
    (recordCell : readCell store recordResolved = some [.tag tag, .location payload])
    (payloadResolution : Resolve store payload tuple)
    (fields : readCell store tuple = some [.location keyAddress, parent, phase, children])
    (evaluation : Eval program env call store result finish) :
    result = .location keyAddress ∧ finish = store := by
  obtain ⟨afterFunction, afterArgument, callable, argumentValue, actualParameter, actualBody, captured,
    functionEval, target, argumentEval, bodyEval⟩ := apply_inversion shape evaluation
  obtain ⟨actualFunction, functionState⟩ := variable_inversion functionShape functionEval
  have sameFunction : callable = .location functionAddress := by
    simpa [functionBinding] using actualFunction.symm
  subst callable
  subst afterFunction
  obtain ⟨sameParameter, sameBody, sameCapture⟩ :=
    capture_free_target program store functionAddress functionResolved code context storage parameter body
      functionResolution functionCell closureShape target
  subst actualParameter
  subst actualBody
  subst captured
  obtain ⟨actualArgument, argumentState⟩ := variable_inversion argumentShape argumentEval
  have sameArgument : argumentValue = .location recordAddress := by
    simpa [recordBinding] using actualArgument.symm
  subst argumentValue
  subst afterArgument
  exact record_projection_returns_key program store finish (extend [] parameter (.location recordAddress))
    body scrutinee returnKey parameter keyName parentName phaseName childrenName tag recordAddress
    recordResolved payload tuple keyAddress parent phase children result differentParent differentPhase
    differentChildren bodyShape scrutineeShape returnShape (by simp [CoreEval.lookup, extend])
    recordResolution recordCell payloadResolution fields bodyEval

/-- The concrete Record helper supplies the projection law after the actual query. -/
theorem record_projection_after_query (program : Program) (env : Environment) (start : Store)
    (call function argument code context storage parameter body scrutinee returnKey : NodeId)
    (functionName recordName keyName parentName phaseName childrenName contextBinder : Binder)
    (tag : Constructor) (functionAddress functionResolved recordAddress recordResolved payload tuple keyAddress : Nat)
    (parent phase children : Value)
    (functionFresh : functionName ≠ contextBinder) (recordFresh : recordName ≠ contextBinder)
    (callShape : program call = some (.apply function argument))
    (functionShape : program function = some (.variable functionName))
    (argumentShape : program argument = some (.variable recordName))
    (functionBinding : CoreEval.lookup env functionName = some (.location functionAddress))
    (recordBinding : CoreEval.lookup env recordName = some (.location recordAddress))
    (functionResolution : Resolve start functionAddress functionResolved)
    (functionCell : readCell start functionResolved = some [.closureCode code])
    (closureShape : program code = some (.closure context [] storage parameter body))
    (differentParent : keyName ≠ parentName) (differentPhase : keyName ≠ phaseName)
    (differentChildren : keyName ≠ childrenName)
    (bodyShape : program body = some (.caseMatch scrutinee
      [(.constructor tag (some (.tuple [.binder keyName, .binder parentName, .binder phaseName,
        .binder childrenName])), returnKey)]))
    (scrutineeShape : program scrutinee = some (.variable parameter))
    (returnShape : program returnKey = some (.variable keyName))
    (recordResolution : Resolve start recordAddress recordResolved)
    (recordCell : readCell start recordResolved = some [.tag tag, .location payload])
    (payloadResolution : Resolve start payload tuple)
    (fields : readCell start tuple = some [.location keyAddress, parent, phase, children]) :
    ProjectionAfterQuery program call env contextBinder start keyAddress := by
  intro queried middle actual queryStep evaluation
  have functionBound : CoreEval.lookup (extend env contextBinder .context) functionName =
      some (.location functionAddress) := by
    rw [lookup_extended_other env contextBinder functionName functionFresh]
    exact functionBinding
  have recordBound : CoreEval.lookup (extend env contextBinder .context) recordName =
      some (.location recordAddress) := by
    rw [lookup_extended_other env contextBinder recordName recordFresh]
    exact recordBinding
  exact record_projection_call program queried middle (extend env contextBinder .context)
    call function argument code context storage parameter body scrutinee returnKey
    functionName recordName keyName parentName phaseName childrenName tag functionAddress functionResolved
    recordAddress recordResolved payload tuple keyAddress parent phase children actual
    callShape functionShape argumentShape functionBound recordBound
    (query_preserves_resolution queryStep functionResolution) (query_preserves_cell queryStep functionCell)
    closureShape differentParent differentPhase differentChildren bodyShape scrutineeShape returnShape
    (query_preserves_resolution queryStep recordResolution) (query_preserves_cell queryStep recordCell)
    (query_preserves_resolution queryStep payloadResolution) (query_preserves_cell queryStep fields) evaluation

end Ash.NetworkLedger.CoreRecordProjection
