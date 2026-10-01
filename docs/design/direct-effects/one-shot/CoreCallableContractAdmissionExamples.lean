import CoreCallableContractAdmission

/-! Finite effect-boundary gate for the indexed experimental judgment. All
functions and requests share one global exact operation contract. This does
not supply handler/capture/pending or full M4 admission. -/
namespace Ash.OneShot.CoreCallableContractAdmissionExamples
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractSource (Contract Environment sequenceRows)
open CoreCallableContractAdmission
open SourcePlannedChecks (Certified DeclarationPolicy)
open RecursiveRequirements (Requirements)
open CoreCallableRootRefinement (Refines)

private def effect : Instance := .user 9 []
private def request : Demand := ⟨effect, 0, false⟩
private def emptyReq : Requirements [] := .request [] []
private def operationReq : Requirements [] := .emitAfter emptyReq [] [request]
private def operationPlan : Plan (.sequence .pure (.request effect 0)) := .sequence .pure .request
private def operationRows : Rows (signature operationPlan) := sequenceRows Rows.pure Rows.request
private def action : Contract := .function .unit .unit [effect] [request] operationPlan operationRows
private def globals : Globals where
  operations := fun e operation => if e = effect ∧ operation = 0 then some (.unit, .unit) else none
  policy := fun _ => ⟨false, false⟩
  owners := fun _ => none
private def run : Code := .perform (Instantiation.freezeEffect effect) 0 .unit
private def simple : Code := .lambda 2 run
private def sequenced : Code := .lambda 2 (.bind 3 .unit run)

section
local instance : DeclarationPolicy := SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

private theorem planCertified : Certified outward world operationPlan := .sequence .pure .request
private theorem actionFormed : ScopedPorts.InWorld world action.port := by
  change [] ⊆ world
  intro identity member; cases member

private theorem run_source : Source globals outward world [effect] scope environment run .unit [] operationReq operationPlan operationRows :=
  .perform (by simp [globals, Globals.registry]) (by simp) .unit (by change [] ⊆ world; intro identity member; cases member)

private theorem operation_outward : RecursiveOutward.Outward operationReq (some [request]) := by
  exact .emitAfter (layers := []) (.request (layers := []))

private theorem simple_source : Source globals outward world allowed scope environment simple action [] emptyReq .pure Rows.pure :=
  .lambda run_source (Refines.identity operationRows) operation_outward (by simp [request]) planCertified actionFormed

private theorem sequenced_source : Source globals outward world allowed scope environment sequenced action [] emptyReq .pure Rows.pure := by
  refine .lambda (.bind .unit run_source) ?_ ?_ (by simp [request]) planCertified actionFormed
  · exact Refines.of_exact (CoreCallableRefinementTransport.Refines.pure_prefix CorePayloadRefinement.PurePlan.pure Rows.pure operationRows)
  · exact .sequence (.request (layers := [])) operation_outward

private def helperBody : Code := .app (.variable 0) .unit
private def helper : Code := .lambda 0 helperBody
private def helperPlan := Plan.sequence Plan.pure (Plan.sequence Plan.pure operationPlan)
private def helperRows : Rows (signature helperPlan) := sequenceRows Rows.pure (sequenceRows Rows.pure operationRows)
private def helperReq : Requirements [] := .emitAfter (.sequence emptyReq emptyReq) [] [request]
private def helperContract : Contract := .function action .unit [effect] [request] helperPlan helperRows
private theorem helperCertified : Certified outward world helperPlan := .sequence .pure (.sequence .pure planCertified)
private theorem helper_source : Source globals outward world allowed scope environment helper helperContract [] emptyReq .pure Rows.pure := by
  refine .lambda (.app (.variable (by simp [Environment.extend, action]) actionFormed) .unit (by simp) planCertified)
    (Refines.identity helperRows) ?_ (by simp [request]) helperCertified ?_
  · exact .emitAfter (layers := []) (.sequence (.request (layers := [])) (.request (layers := [])))
  · simp [Contract.port, Contract.value, SourcePlannedTyping.Value.erase,
      SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port, ScopedPorts.InWorld,
      ScopedPorts.Port.resources, List.flatMap, Instance.resources, effect,
      action]

private def callPlan := Plan.sequence Plan.pure (Plan.sequence Plan.pure helperPlan)
private def callRows : Rows (signature callPlan) := sequenceRows Rows.pure (sequenceRows Rows.pure helperRows)
private def callReq : Requirements [] := .emitAfter (.sequence emptyReq emptyReq) [] [request]
private def bothBody : Code := .bind 11 (.app (.variable 10) simple) (.app (.variable 10) sequenced)
private def both : Code := .bind 10 helper bothBody

/-- One helper is bound once and consumes two unchanged effectful closures
under the same public callable contract and exact global registry. -/
theorem both_source : Source globals outward world [effect] scope Environment.empty both .unit []
    (.sequence emptyReq (.sequence callReq callReq))
    (.sequence .pure (.sequence callPlan callPlan))
    (sequenceRows Rows.pure (sequenceRows callRows callRows)) := by
  have formed : ScopedPorts.InWorld world helperContract.port := by
    change [] ⊆ world
    intro identity member; cases member
  apply Source.bind helper_source
  unfold bothBody
  apply Source.bind (initialDemand := []) (bodyDemand := [])
  · exact .app (input := action) (output := Contract.unit) (requests := [effect]) (latent := [request])
      (.variable (by simp [Environment.extend, helperContract]) formed) simple_source (by simp) helperCertified
  · exact .app (input := action) (output := Contract.unit) (requests := [effect]) (latent := [request])
      (.variable (by simp [Environment.extend, helperContract]) formed) sequenced_source (by simp) helperCertified

/-- Actual operation argument/result contracts are read from that same table. -/
theorem exact_operation : globals.operations effect 0 = some (Contract.unit, Contract.unit) := by simp [globals]

/-- The fixed registry cannot be reselected by a request constructor. -/
theorem wrong_result_rejected : ¬ Source globals outward world [effect] scope environment run .boolean demand requirements plan rows := by
  intro source
  obtain ⟨input, known⟩ := (IndexedSource.request_contract source)
  simp [globals, Globals.registry] at known

/-- The same exact key cannot accept an integer where Unit is declared. -/
theorem wrong_input_rejected :
    ¬ Source globals outward world [effect] scope environment
      (.perform (Instantiation.freezeEffect effect) 0 (.integer 7)) .unit demand requirements plan rows := by
  intro source
  obtain ⟨input, operandDemand, operandReq, operandDeps, operandPlan, operandRows, known, operand⟩ := (IndexedSource.request_operand source)
  simp [globals, Globals.registry] at known
  subst input
  cases operand

/-- An absent operation key has no fabricated signature fallback. -/
theorem wrong_key_rejected :
    ¬ Source globals outward world [effect] scope environment
      (.perform (Instantiation.freezeEffect effect) 1 .unit) output demand requirements plan rows := by
  intro source
  obtain ⟨input, known⟩ := (IndexedSource.request_contract source)
  simp [globals, Globals.registry] at known

open CoreCallableReceiverRefinement (LexicalBounds)
open SourceScheduledCleanupInterfaces.Lexical.Recursive

private theorem run_authenticated (source : Source globals outward world [effect] scope environment
    run .unit [] operationReq operationPlan operationRows) :
    Authenticated globals.registry outward source lexical receiver := by
  refine .checked ?_ (.perform (known := by simp [globals, Globals.registry]) (admitted := by simp)
    (formed := by change [] ⊆ world; simp) (.checked ?_ .unit))
  all_goals apply SourceSupport.bounds_iff.mpr
  all_goals simp [run, effect, Code.dependencies, ScopedPorts.Support.evaluate,
    Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources]

private theorem simple_authenticated (source : Source globals outward world allowed scope environment
    simple action [] emptyReq .pure Rows.pure) :
    Authenticated globals.registry outward source lexical receiver := by
  refine .checked ?_ (.lambda (bodySource := run_source) (Refines.identity operationRows)
    operation_outward (by simp [request]) planCertified actionFormed ?_ ?_)
  · apply SourceSupport.bounds_iff.mpr
    simp [simple, run, effect, Code.dependencies, Syntax.without, ScopedPorts.Support.evaluate,
      Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources]
  · intro name member
    simp [run, effect, Code.dependencies, Syntax.without, Instantiation.freezeEffect,
      effectAtoms, Instantiation.Effect.resources] at member
  · intro nextLexical call _ _
    exact run_authenticated _

private theorem sequenced_authenticated (source : Source globals outward world allowed scope environment
    sequenced action [] emptyReq .pure Rows.pure) :
    Authenticated globals.registry outward source lexical receiver := by
  refine .checked ?_ (.lambda (bodySource := .bind .unit run_source)
    (Refines.of_exact (CoreCallableRefinementTransport.Refines.pure_prefix CorePayloadRefinement.PurePlan.pure Rows.pure operationRows))
    (.sequence (.request (layers := [])) operation_outward) (by simp [request]) planCertified actionFormed ?_ ?_)
  · apply SourceSupport.bounds_iff.mpr
    simp [sequenced, run, effect, Code.dependencies, Syntax.without, ScopedPorts.Support.evaluate,
      Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources]
  · intro name member
    simp [run, effect, Code.dependencies, Syntax.without, Instantiation.freezeEffect,
      effectAtoms, Instantiation.Effect.resources] at member
  · intro nextLexical call _ _
    refine .checked ?_ (.bind (initialSource := .unit)
      (bodySource := .perform (by simp [globals, Globals.registry]) (by simp) .unit (by change [] ⊆ call.world; simp))
      (.checked ?_ .unit) (run_authenticated _))
    all_goals apply SourceSupport.bounds_iff.mpr
    all_goals simp [run, effect, Code.dependencies, Syntax.without, ScopedPorts.Support.evaluate,
      Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources]

private theorem helper_authenticated (source : Source globals outward world allowed scope environment
    helper helperContract [] emptyReq .pure Rows.pure) :
    Authenticated globals.registry outward source lexical receiver := by
  let bodySource : Source globals outward world [effect] .none (environment.extend 0 action)
      helperBody .unit [] helperReq helperPlan helperRows :=
    .app (.variable (by simp [Environment.extend, action]) actionFormed) .unit (by simp) planCertified
  refine .checked ?_ (.lambda (bodySource := bodySource) (Refines.identity helperRows)
    (.emitAfter (layers := []) (.sequence (.request (layers := [])) (.request (layers := []))))
    (by simp [request]) helperCertified ?_ ?_ ?_)
  · apply SourceSupport.bounds_iff.mpr
    simp [helper, helperBody, Code.dependencies, Syntax.without, ScopedPorts.Support.evaluate]
  · change [] ⊆ world
    simp
  · intro name member
    simp [helperBody, Code.dependencies, Syntax.without] at member
  · intro nextLexical call _ _
    refine .checked ?_ (.app (admitted := by simp) (publicCertified := .sequence .pure .request)
      (functionSource := .variable (contract := action) (by simp [Environment.extend, action]) actionFormed) (argumentSource := .unit)
      (.checked ?_ (.variable (known := by simp [Environment.extend, action]) (formed := actionFormed)
        ⟨call.argument, by simp [LexicalBounds.lookup, LexicalBounds.extend]⟩)) (.checked ?_ .unit))
    all_goals apply SourceSupport.bounds_iff.mpr
    all_goals simp [helperBody, Code.dependencies, ScopedPorts.Support.evaluate,
      LexicalBounds.environment, LexicalBounds.lookup, LexicalBounds.extend, call.argumentReceived]

private theorem simple_supported : CoreCallableContractAdmission.Supported globals outward world [effect] scope Environment.empty
    ScopedPorts.Support.empty simple action [] emptyReq .pure Rows.pure [] [] :=
  ⟨simple_source, by apply SourceSupport.bounds_iff.mpr; simp [simple, run, effect, Code.dependencies,
      Syntax.without, ScopedPorts.Support.evaluate, Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources],
    by simp, ⟨[], rfl, simple_authenticated _⟩, by simp⟩
private theorem sequenced_supported : CoreCallableContractAdmission.Supported globals outward world [effect] scope Environment.empty
    ScopedPorts.Support.empty sequenced action [] emptyReq .pure Rows.pure [] [] :=
  ⟨sequenced_source, by apply SourceSupport.bounds_iff.mpr; simp [sequenced, run, effect, Code.dependencies,
      Syntax.without, ScopedPorts.Support.evaluate, Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources],
    by simp, ⟨[], rfl, sequenced_authenticated _⟩, by simp⟩

private theorem helper_body_supported : CoreCallableContractAdmission.Supported globals outward world [effect] .none (Environment.empty.extend 0 action)
    (ScopedPorts.Support.extend ScopedPorts.Support.empty 0 []) helperBody .unit [] helperReq helperPlan helperRows [] [] := by
  let source : Source globals outward world [effect] .none (Environment.empty.extend 0 action)
      helperBody .unit [] helperReq helperPlan helperRows :=
    .app (.variable (by simp [Environment.extend, action]) actionFormed) .unit (by simp) planCertified
  refine ⟨source, ?_, by simp, ⟨[(0, [])], ?_, .checked ?_ (.app (admitted := by simp) (publicCertified := planCertified)
      (functionSource := .variable (contract := action) (by simp [Environment.extend, action]) actionFormed) (argumentSource := .unit)
      (.checked ?_ (.variable (known := by simp [Environment.extend, action]) (formed := actionFormed)
        ⟨[], by simp [LexicalBounds.lookup]⟩)) (.checked ?_ .unit))⟩, by simp⟩
  · apply SourceSupport.bounds_iff.mpr
    simp [helperBody, Code.dependencies, ScopedPorts.Support.evaluate, ScopedPorts.Support.extend]
  · funext name; by_cases same : name = 0 <;> simp [same, LexicalBounds.environment, LexicalBounds.lookup, ScopedPorts.Support.extend, ScopedPorts.Support.empty]
  all_goals apply SourceSupport.bounds_iff.mpr
  all_goals simp [helperBody, Code.dependencies, ScopedPorts.Support.evaluate,
    LexicalBounds.environment, LexicalBounds.lookup]

/-- Closed substitution retains recursive private plans and their actual
certification for both payloads, not just their ordinary ports. -/
theorem helper_substitutions :
    Source globals outward world [effect] .none Environment.empty (.app simple .unit) .unit [] helperReq helperPlan helperRows ∧
    Source globals outward world [effect] .none Environment.empty (.app sequenced .unit) .unit [] helperReq helperPlan helperRows ∧
    Certified outward world helperPlan := by
  have body : Source globals outward world [effect] .none (Environment.empty.extend 0 action) helperBody .unit [] helperReq helperPlan helperRows :=
    .app (.variable (by simp [Environment.extend, action]) actionFormed) .unit (by simp) planCertified
  have simpleClosed : ClosedValue simple := by
    simp [simple, run, effect, ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Code.dependencies, Instantiation.freezeEffect, Instantiation.Effect.freeNames]
  have sequencedClosed : ClosedValue sequenced := by
    simp [sequenced, run, effect, ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Code.dependencies, Syntax.without, Instantiation.freezeEffect, Instantiation.Effect.freeNames]
  obtain ⟨simplePlan, simpleRows, simpleSource, simpleExact, _, simpleHEq⟩ :=
    CoreCallableContractAdmission.Supported.substitution helper_body_supported (simple_supported (scope := .none)) simpleClosed
  obtain ⟨sequencedPlan, sequencedRows, sequencedSource, sequencedExact, _, sequencedHEq⟩ :=
    CoreCallableContractAdmission.Supported.substitution helper_body_supported (sequenced_supported (scope := .none)) sequencedClosed
  have simpleSame : simplePlan = helperPlan := by rw [simpleExact]; rfl
  have sequencedSame : sequencedPlan = helperPlan := by rw [sequencedExact]; rfl
  cases simpleSame; cases eq_of_heq simpleHEq
  cases sequencedSame; cases eq_of_heq sequencedHEq
  exact ⟨by simpa [helperBody, Code.subst] using simpleSource.source,
    by simpa [helperBody, Code.subst] using sequencedSource.source, IndexedSource.certified body⟩


private theorem helper_closed : ClosedValue helper := by
  simp [helper, helperBody, ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames,
    Code.dependencies, Syntax.without]
private theorem simple_closed : ClosedValue simple := by
  simp [simple, run, effect, ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames,
    Code.dependencies, Instantiation.freezeEffect, Instantiation.Effect.freeNames]
private theorem sequenced_closed : ClosedValue sequenced := by
  simp [sequenced, run, effect, ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames,
    Code.dependencies, Syntax.without, Instantiation.freezeEffect, Instantiation.Effect.freeNames]

private theorem helper_supported : CoreCallableContractAdmission.Supported globals outward world [effect] scope Environment.empty
    ScopedPorts.Support.empty helper helperContract [] emptyReq .pure Rows.pure [] [] :=
  ⟨helper_source, by apply SourceSupport.bounds_iff.mpr; simp [helper, helperBody, Code.dependencies,
      Syntax.without, ScopedPorts.Support.evaluate], by simp, ⟨[], rfl, helper_authenticated _⟩, by simp⟩

private theorem both_body_supported : CoreCallableContractAdmission.Supported globals outward world [effect] scope
    (Environment.empty.extend 10 helperContract) (ScopedPorts.Support.extend ScopedPorts.Support.empty 10 [])
    bothBody .unit [] (.sequence callReq callReq) (.sequence callPlan callPlan) (sequenceRows callRows callRows) [] [] := by
  have formed : ScopedPorts.InWorld world helperContract.port := by change [] ⊆ world; simp
  let first : Source globals outward world [effect] scope (Environment.empty.extend 10 helperContract)
      (.app (.variable 10) simple) .unit [] callReq callPlan callRows :=
    .app (.variable (by simp [Environment.extend, helperContract]) formed) simple_source (by simp) helperCertified
  let second : Source globals outward world [effect] scope ((Environment.empty.extend 10 helperContract).extend 11 Contract.unit)
      (.app (.variable 10) sequenced) .unit [] callReq callPlan callRows :=
    .app (.variable (by simp [Environment.extend, helperContract]) formed) sequenced_source (by simp) helperCertified
  refine ⟨.bind first second, ?_, by simp, ⟨[(10, [])], ?_, .checked ?_ (.bind (initialSource := first) (bodySource := second)
    (.checked ?_ (.app (admitted := by simp) (publicCertified := helperCertified)
      (functionSource := .variable (contract := helperContract) (by simp [Environment.extend, helperContract]) formed)
      (argumentSource := simple_source) (.checked ?_ (.variable (known := by simp [Environment.extend, helperContract])
        (formed := formed) ⟨[], by simp [LexicalBounds.lookup]⟩)) (simple_authenticated _)))
    (.checked ?_ (.app (admitted := by simp) (publicCertified := helperCertified)
      (functionSource := .variable (contract := helperContract) (by simp [Environment.extend, helperContract]) formed)
      (argumentSource := sequenced_source) (.checked ?_ (.variable (known := by simp [Environment.extend, helperContract])
        (formed := formed) ⟨[], by simp [LexicalBounds.lookup, LexicalBounds.extend]⟩)) (sequenced_authenticated _))))⟩, by simp⟩
  · apply SourceSupport.bounds_iff.mpr
    simp [bothBody, simple, sequenced, run, effect, Code.dependencies, Syntax.without,
      ScopedPorts.Support.evaluate, ScopedPorts.Support.extend, Instantiation.freezeEffect,
      effectAtoms, Instantiation.Effect.resources]
  · funext name; by_cases same : name = 10 <;> simp [same, LexicalBounds.environment,
      LexicalBounds.lookup, ScopedPorts.Support.extend, ScopedPorts.Support.empty]
  all_goals apply SourceSupport.bounds_iff.mpr
  all_goals simp [bothBody, simple, sequenced, run, effect, Code.dependencies, Syntax.without,
    ScopedPorts.Support.evaluate, LexicalBounds.environment, LexicalBounds.lookup, LexicalBounds.extend,
    Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources]

/-- The first actual bind preserves private witnesses from both_source. -/
theorem both_bind (stack : Stack) :
    Source globals outward world [effect] scope Environment.empty (bothBody.subst 10 helper) .unit []
      (.sequence callReq callReq) (.sequence callPlan callPlan) (sequenceRows callRows callRows) ∧
    Certified outward world (.sequence callPlan callPlan) ∧
    RawStep ⟨both, scope, stack⟩ ⟨bothBody.subst 10 helper, scope, stack⟩ [] [] := by
  obtain ⟨nextPlan, nextRows, supported, exactPlan, _, sameRows⟩ :=
    CoreCallableContractAdmission.Supported.substitution both_body_supported helper_supported helper_closed
  have planSame : nextPlan = Plan.sequence callPlan callPlan := by
    rw [exactPlan]
    simp [bothBody, callPlan, CoreCallablePlanSubstitution.plan]
  cases planSame; cases eq_of_heq sameRows
  exact ⟨supported.source, IndexedSource.certified supported.source, .bind 10 helper bothBody scope stack helper_closed (by
    simp [bothBody, simple, sequenced, run, effect, ClosedExcept, Code.dependencies, Syntax.without,
      Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources])⟩

private def retaining (identity : Nat) : Code := .lambda 2 (.bind 3 (.resourceRef (.activation identity)) run)
private theorem retaining_source (issued : identity ∈ world) :
    Source globals outward world allowed scope environment (retaining identity) action [] emptyReq .pure Rows.pure := by
  refine .lambda (.bind (.reference issued) run_source) ?_ ?_ (by simp [request]) planCertified actionFormed
  · exact Refines.of_exact (CoreCallableRefinementTransport.Refines.pure_prefix CorePayloadRefinement.PurePlan.pure Rows.pure operationRows)
  · exact .sequence (.request (layers := [])) operation_outward

private theorem retaining_authenticated (issued : identity ∈ world) :
    Authenticated globals.registry outward (retaining_source (allowed := [effect]) (scope := scope) (environment := Environment.empty) issued) [] [identity] := by
  refine .checked ?_ ?_
  · apply SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr
    simp [retaining, run, effect, ScopedPorts.Support.evaluate, CoreCallableReceiverRefinement.LexicalBounds.environment,
      CoreCallableReceiverRefinement.LexicalBounds.lookup, Code.dependencies, Instantiation.freezeEffect,
      effectAtoms, Instantiation.Effect.resources, Syntax.without]
  · refine .lambda (bodySource := .bind (.reference issued) run_source)
      (Refines.of_exact (CoreCallableRefinementTransport.Refines.pure_prefix CorePayloadRefinement.PurePlan.pure Rows.pure operationRows))
      (.sequence (.request (layers := [])) operation_outward) (by simp [request]) planCertified actionFormed ?_ ?_
    · intro name member
      simp [run, effect, Code.dependencies, Syntax.without, Instantiation.freezeEffect,
        effectAtoms, Instantiation.Effect.resources] at member
    · intro lexical call _ received
      have identityReceived : identity ∈ call.receiver := by
        apply received
        simp [run, effect, Code.dependencies, Syntax.without, ScopedPorts.Support.evaluate,
          Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources]
      refine .checked ?_ (.bind (initialSource := .reference (call.worldExtended issued)) (bodySource := run_source)
        (.checked ?_ (.reference (issued := call.worldExtended issued))) (.checked ?_ (.perform (known := by simp [globals, Globals.registry])
          (admitted := by simp) (formed := by change [] ⊆ call.world; simp) (.checked ?_ .unit))))
      all_goals apply SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr
      all_goals simp [run, effect, Code.dependencies, Syntax.without, ScopedPorts.Support.evaluate,
        Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources, identityReceived]

/-- Exact request ports remain resource-free, but actual retained support does not. -/
theorem retaining_supported (issued : identity ∈ world) :
    CoreCallableContractAdmission.Supported globals outward world [effect] scope Environment.empty (fun _ => []) (retaining identity) action [] emptyReq .pure Rows.pure [identity] [identity] := by
  refine ⟨retaining_source issued, ?_, by simpa using issued,
    ⟨[], rfl, retaining_authenticated issued⟩, by simpa using issued⟩
  apply SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr
  simp [retaining, run, effect, ScopedPorts.Support.evaluate, Code.dependencies,
    Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources, Syntax.without]

/-- A resource-free port cannot justify a false empty actual capture bound. -/
theorem wrong_support_rejected :
    ¬ CoreCallableContractAdmission.Supported globals outward world [effect] scope Environment.empty (fun _ => []) (retaining identity) action [] emptyReq .pure Rows.pure [] receiver := by
  intro supported
  have member := supported.support.resources (show identity ∈ Syntax.resourceDependencies (retaining identity).dependencies from by
    simp [retaining, run, effect, Syntax.resourceDependencies, Code.dependencies, Syntax.without,
      Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources])
  cases member

private def payload (extra : Bool) : Code := if extra then sequenced else simple
private theorem payload_source : Source globals outward world [effect] scope Environment.empty (payload extra) action [] emptyReq .pure Rows.pure := by
  cases extra <;> first | exact simple_source | exact sequenced_source
private theorem payload_closed : ClosedValue (payload extra) := by
  cases extra <;> first | exact simple_closed | exact sequenced_closed

/-- Actual helper beta uses that same supplied global-indexed payload derivation,
recovering and certifying the private body through compositional substitution. -/
theorem helper_beta (extra : Bool) (stack : Stack) :
    ∃ (bodyDemand : List Nat) (bodyReq : Requirements bodyDemand) (actualDependencies : SourceDependencyAnnotations.Dependencies)
      (actualPlan : Plan actualDependencies) (actualRows : Rows (signature actualPlan)),
      Source globals outward world [effect] .none Environment.empty (helperBody.subst 0 (payload extra)) .unit bodyDemand bodyReq actualPlan actualRows ∧
      Certified outward world actualPlan ∧ Refines helperRows actualRows ∧ RecursiveOutward.Outward bodyReq (some [request]) ∧
      RawStep ⟨.app helper (payload extra), scope, stack⟩ ⟨helperBody.subst 0 (payload extra), .none, stack⟩ [] [] := by
  have source : Source globals outward world [effect] .none Environment.empty
      (helperBody.subst 0 (payload extra)) .unit [] helperReq helperPlan helperRows := by
    obtain ⟨simpleSource, sequencedSource, _⟩ := helper_substitutions (outward := outward) (world := world)
    cases extra
    · simpa [payload, helperBody, Code.subst] using simpleSource
    · simpa [payload, helperBody, Code.subst] using sequencedSource
  exact ⟨[], helperReq, _, helperPlan, helperRows, source, helperCertified, Refines.identity helperRows,
    .emitAfter (layers := []) (.sequence (.request (layers := [])) (.request (layers := []))),
    .beta 0 helperBody (payload extra) scope stack payload_closed helper_closed⟩

/-- Effect-boundary beta has actual source/certification and transports exact
current certificates plus checked roots. No successor admission is a premise. -/
theorem helper_current (extra : Bool) (stack : Stack)
    (installations ambient : List Nat) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) (budget : Footprint)
    {receivingScope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints receivingScope}
    (context : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Context hints)
    (certificate : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.SourceAdmission.Code outward actions budget phases world installations helperRows context)
    (certificateChecked : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.CodeChecked ambient outward certificate)
    (root annotated : Requirements demand)
    (run : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.Run world installations helperRows context root)
    (entries : RecursiveRequirements.Store) (receiving : OwnerPhases.Context) (row : Footprint)
    (annotation : SourceDependencyAnnotations.RowAnnotation root annotated)
    (check : RecursiveRequirements.Checked entries receiving phases (SourceScheduledCleanupInterfaces.Lexical.Recursive.annotateDisposals annotated) row)
    (bounded : row ⊆ budget) :
    ∃ (actualDependencies : SourceDependencyAnnotations.Dependencies) (actualPlan : Plan actualDependencies)
      (actualRows : Rows (signature actualPlan)), ∃ (bodyDemand : List Nat) (bodyReq : Requirements bodyDemand),
      Source globals outward world [effect] .none Environment.empty (helperBody.subst 0 (payload extra)) .unit bodyDemand bodyReq actualPlan actualRows ∧
      Certified outward world actualPlan ∧
      RawStep ⟨.app helper (payload extra), scope, stack⟩ ⟨helperBody.subst 0 (payload extra), .none, stack⟩ [] [] ∧
      ∃ actualCertificate : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.SourceAdmission.Code outward actions budget phases world installations actualRows context,
        SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.CodeChecked ambient outward actualCertificate ∧
        ∃ actualRoot actualAnnotated : Requirements demand, ∃ actualRow : Footprint,
          SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.Run world installations actualRows context actualRoot ∧
          CoreCallableRootRefinement.RootTransport root actualRoot ∧ SourceDependencyAnnotations.RowAnnotation actualRoot actualAnnotated ∧
          RecursiveRequirements.Checked entries receiving phases (SourceScheduledCleanupInterfaces.Lexical.Recursive.annotateDisposals actualAnnotated) actualRow ∧ actualRow ⊆ budget := by
  obtain ⟨bodyDemand, bodyReq, dependencies, plan, rows, source, certified, refinement, _outward, raw⟩ :=
    helper_beta (outward := outward) (world := world) (scope := scope) extra stack
  let actualCertificate := refinement.code outward actions budget phases world installations context certificate
  obtain ⟨actualRoot, actualAnnotated, actualRow, actualRun, transport, actualAnnotation, actualCheck, actualBound⟩ :=
    CoreCallableRootRefinement.checked_accounting refinement world installations context root annotated run
      entries receiving phases budget row annotation check bounded
  exact ⟨dependencies, plan, rows, bodyDemand, bodyReq, source, certified, raw, actualCertificate,
    refinement.checked ambient outward actions budget phases world installations context certificate certificateChecked,
    actualRoot, actualAnnotated, actualRow, actualRun, transport, actualAnnotation, actualCheck, actualBound⟩

private def payloadBody (extra : Bool) : Code := if extra then .bind 3 .unit run else run
private theorem payload_substitution (extra : Bool) (stack : Stack) :
    ∃ (bodyDemand : List Nat) (bodyReq : Requirements bodyDemand) (dependencies : SourceDependencyAnnotations.Dependencies)
      (plan : Plan dependencies) (rows : Rows (signature plan)),
      Source globals outward world [effect] .none Environment.empty ((payloadBody extra).subst 2 .unit) .unit bodyDemand bodyReq plan rows ∧
      Certified outward world plan ∧ Refines operationRows rows ∧
      RawStep ⟨.app (payload extra) .unit, scope, stack⟩ ⟨(payloadBody extra).subst 2 .unit, .none, stack⟩ [] [] := by
  have replacement : CoreCallableContractAdmission.Supported globals outward world [effect] .none Environment.empty
      ScopedPorts.Support.empty .unit .unit [] emptyReq .pure Rows.pure [] [] :=
    ⟨.unit, .nil, by simp, ⟨[], rfl, .checked .nil .unit⟩, by simp⟩
  cases extra
  · have body : CoreCallableContractAdmission.Supported globals outward world [effect] .none (Environment.empty.extend 2 Contract.unit)
        (ScopedPorts.Support.extend ScopedPorts.Support.empty 2 []) run .unit [] operationReq operationPlan operationRows [] [] := by
      refine ⟨run_source, ?_, by simp, ⟨[(2, [])], ?_, run_authenticated _⟩, by simp⟩
      · apply SourceSupport.bounds_iff.mpr
        simp [run, effect, Code.dependencies, ScopedPorts.Support.evaluate, Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources]
      · funext name; by_cases same : name = 2 <;> simp [same, LexicalBounds.environment, LexicalBounds.lookup, ScopedPorts.Support.extend, ScopedPorts.Support.empty]
    obtain ⟨plan, rows, source, exactPlan, _, sameRows⟩ := CoreCallableContractAdmission.Supported.substitution body replacement ScopedExecution.Examples.unit_closed
    have samePlan : plan = operationPlan := by rw [exactPlan]; simp [run, operationPlan, CoreCallablePlanSubstitution.plan]
    cases samePlan; cases eq_of_heq sameRows
    exact ⟨[], operationReq, _, operationPlan, operationRows, source.source, planCertified, Refines.identity operationRows,
      .beta 2 run .unit scope stack ScopedExecution.Examples.unit_closed simple_closed⟩
  · have body : CoreCallableContractAdmission.Supported globals outward world [effect] .none (Environment.empty.extend 2 Contract.unit)
        (ScopedPorts.Support.extend ScopedPorts.Support.empty 2 []) (.bind 3 .unit run) .unit [] (.sequence emptyReq operationReq)
        (.sequence .pure operationPlan) (sequenceRows Rows.pure operationRows) [] [] := by
      refine ⟨.bind .unit run_source, ?_, by simp, ⟨[(2, [])], ?_, .checked ?_
        (.bind (initialSource := .unit) (bodySource := run_source) (.checked .nil .unit) (run_authenticated _))⟩, by simp⟩
      · apply SourceSupport.bounds_iff.mpr
        simp [run, effect, Code.dependencies, Syntax.without, ScopedPorts.Support.evaluate, Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources]
      · funext name; by_cases same : name = 2 <;> simp [same, LexicalBounds.environment, LexicalBounds.lookup, ScopedPorts.Support.extend, ScopedPorts.Support.empty]
      · apply SourceSupport.bounds_iff.mpr
        simp [run, effect, Code.dependencies, Syntax.without, ScopedPorts.Support.evaluate, Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources]
    obtain ⟨plan, rows, source, exactPlan, _, sameRows⟩ := CoreCallableContractAdmission.Supported.substitution body replacement ScopedExecution.Examples.unit_closed
    have samePlan : plan = Plan.sequence Plan.pure operationPlan := by rw [exactPlan]; simp [run, operationPlan, CoreCallablePlanSubstitution.plan]
    cases samePlan; cases eq_of_heq sameRows
    exact ⟨[], .sequence emptyReq operationReq, _, .sequence .pure operationPlan, sequenceRows Rows.pure operationRows,
      source.source, .sequence .pure planCertified,
      Refines.of_exact (CoreCallableRefinementTransport.Refines.pure_prefix CorePayloadRefinement.PurePlan.pure Rows.pure operationRows),
      .beta 2 (.bind 3 .unit run) .unit scope stack ScopedExecution.Examples.unit_closed sequenced_closed⟩

/-- Invoke the selected effectful payload itself. Current checking transports
into its recovered private operation body (including the extra sequence). -/
theorem payload_current (extra : Bool) (stack : Stack)
    (installations ambient : List Nat) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) (budget : Footprint)
    {receivingScope : SourceDependencyCapture.Scope} {hints : SourceDependencyChecks.Lexical.ReturnHints receivingScope}
    (context : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Context hints)
    (certificate : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.SourceAdmission.Code outward actions budget phases world installations operationRows context)
    (certificateChecked : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.CodeChecked ambient outward certificate)
    (root annotated : Requirements demand)
    (run : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.Run world installations operationRows context root)
    (entries : RecursiveRequirements.Store) (receiving : OwnerPhases.Context) (row : Footprint)
    (annotation : SourceDependencyAnnotations.RowAnnotation root annotated)
    (check : RecursiveRequirements.Checked entries receiving phases (SourceScheduledCleanupInterfaces.Lexical.Recursive.annotateDisposals annotated) row)
    (bounded : row ⊆ budget) :
    ∃ (actualDependencies : SourceDependencyAnnotations.Dependencies) (actualPlan : Plan actualDependencies)
      (actualRows : Rows (signature actualPlan)), ∃ (bodyDemand : List Nat) (bodyReq : Requirements bodyDemand),
      Source globals outward world [effect] .none Environment.empty ((payloadBody extra).subst 2 .unit) .unit bodyDemand bodyReq actualPlan actualRows ∧
      Certified outward world actualPlan ∧
      RawStep ⟨.app (payload extra) .unit, scope, stack⟩ ⟨(payloadBody extra).subst 2 .unit, .none, stack⟩ [] [] ∧
      ∃ actualCertificate : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.SourceAdmission.Code outward actions budget phases world installations actualRows context,
        SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.CodeChecked ambient outward actualCertificate ∧
        ∃ actualRoot actualAnnotated : Requirements demand, ∃ actualRow : Footprint,
          SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.Run world installations actualRows context actualRoot ∧
          CoreCallableRootRefinement.RootTransport root actualRoot ∧ SourceDependencyAnnotations.RowAnnotation actualRoot actualAnnotated ∧
          RecursiveRequirements.Checked entries receiving phases (SourceScheduledCleanupInterfaces.Lexical.Recursive.annotateDisposals actualAnnotated) actualRow ∧ actualRow ⊆ budget := by
  obtain ⟨bodyDemand, bodyReq, dependencies, plan, rows, source, certified, refinement, raw⟩ :=
    payload_substitution (outward := outward) (world := world) (scope := scope) extra stack
  let actualCertificate := refinement.code outward actions budget phases world installations context certificate
  obtain ⟨actualRoot, actualAnnotated, actualRow, actualRun, transport, actualAnnotation, actualCheck, actualBound⟩ :=
    CoreCallableRootRefinement.checked_accounting refinement world installations context root annotated run
      entries receiving phases budget row annotation check bounded
  exact ⟨dependencies, plan, rows, bodyDemand, bodyReq, source, certified, raw, actualCertificate,
    refinement.checked ambient outward actions budget phases world installations context certificate certificateChecked,
    actualRoot, actualAnnotated, actualRow, actualRun, transport, actualAnnotation, actualCheck, actualBound⟩

#print axioms payload_current
#print axioms wrong_input_rejected
#print axioms wrong_key_rejected
#print axioms both_bind
#print axioms retaining_supported
#print axioms wrong_support_rejected
#print axioms helper_beta
#print axioms helper_current
#print axioms both_source
#print axioms exact_operation
#print axioms wrong_result_rejected
#print axioms helper_substitutions
end
end Ash.OneShot.CoreCallableContractAdmissionExamples
