import CoreCallableContractExecution

/-! Finite effect-boundary gate for the indexed experimental judgment. All
functions and requests share one global exact operation contract. This constructs bounded plain/cell pending evidence; handler/owner pending, capture
and full M4 admission remain open. -/
namespace Ash.OneShot.CoreCallableContractExecutionExamples
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractSource (Contract Environment sequenceRows)
open CoreCallableContractAdmission
open CoreCallableContractExecution
open SourceDependencyAnnotations (Dependencies RowAnnotation)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourceScheduledCleanupInterfaces.Lexical.Recursive (annotateDisposals)
open SourcePlannedChecks (Certified DeclarationPolicy)
open RecursiveRequirements (Requirements Checked)
open SourceDependencyChecks.Lexical (ReturnHints)
open CoreCallableRootRefinement (Refines)

private def world : List Nat := [0]
private def effect : Instance := .cell 0
private def request : Demand := ⟨effect, 0, false⟩
private def emptyReq : Requirements [] := .request [] []
private def operationReq : Requirements [] := .emitAfter emptyReq [] [request]
private def operationPlan : Plan (.sequence .pure (.request effect 0)) := .sequence .pure .request
private def operationRows : Rows (signature operationPlan) := sequenceRows Rows.pure Rows.request
private def action : Contract := .function .unit .integer [effect] [request] operationPlan operationRows
private def globals : Globals where
  operations := fun e operation => if e = effect ∧ operation = 0 then some (.reference 0, .integer) else none
  policy := fun _ => ⟨false, false⟩
  owners := fun _ => none
private def run : Code := .perform (Instantiation.freezeEffect effect) 0 (.resourceRef (.activation 0))
private def simple : Code := .lambda 2 run
private def sequenced : Code := .lambda 2 (.bind 3 .unit run)

section
local instance : DeclarationPolicy := SourceScheduledCleanupInterfaces.Lexical.Recursive.declarationPolicy

private theorem planCertified : Certified outward world operationPlan := .sequence .pure .request
private theorem actionFormed : ScopedPorts.InWorld world action.port := by
  change [0] ⊆ world
  exact List.Subset.refl _

private theorem run_source : Source globals outward world [effect] scope environment run .integer [] operationReq operationPlan operationRows :=
  .perform (by simp [globals, Globals.registry]) (by simp) (.reference (by simp [world])) (by change [] ⊆ world; intro identity member; cases member)

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
private def helperContract : Contract := .function action .integer [effect] [request] helperPlan helperRows
private theorem helperCertified : Certified outward world helperPlan := .sequence .pure (.sequence .pure planCertified)
private theorem helper_source : Source globals outward world allowed scope environment helper helperContract [] emptyReq .pure Rows.pure := by
  refine .lambda (.app (.variable (by simp [Environment.extend, action]) actionFormed) .unit (by simp) planCertified)
    (Refines.identity helperRows) ?_ (by simp [request]) helperCertified ?_
  · exact .emitAfter (layers := []) (.sequence (.request (layers := [])) (.request (layers := [])))
  · simp [Contract.port, Contract.value, SourcePlannedTyping.Value.erase,
      SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port, ScopedPorts.InWorld, world,
      ScopedPorts.Port.resources, List.flatMap, Instance.resources, effect,
      action]

private def callPlan := Plan.sequence Plan.pure (Plan.sequence Plan.pure helperPlan)
private def callRows : Rows (signature callPlan) := sequenceRows Rows.pure (sequenceRows Rows.pure helperRows)
private def callReq : Requirements [] := .emitAfter (.sequence emptyReq emptyReq) [] [request]
private def bothBody : Code := .bind 11 (.app (.variable 10) simple) (.app (.variable 10) sequenced)
private def both : Code := .bind 10 helper bothBody

/-- One helper is bound once and consumes two unchanged effectful closures
under the same public callable contract and exact global registry. -/
theorem both_source : Source globals outward world [effect] scope environment both .integer []
    (.sequence emptyReq (.sequence callReq callReq))
    (.sequence .pure (.sequence callPlan callPlan))
    (sequenceRows Rows.pure (sequenceRows callRows callRows)) := by
  have formed : ScopedPorts.InWorld world helperContract.port := by
    change [0, 0] ⊆ world
    simp [world]
  apply Source.bind helper_source
  unfold bothBody
  apply Source.bind (initialDemand := []) (bodyDemand := [])
  · exact .app (input := action) (output := Contract.integer) (requests := [effect]) (latent := [request])
      (.variable (by simp [Environment.extend, helperContract]) formed) simple_source (by simp) helperCertified
  · exact .app (input := action) (output := Contract.integer) (requests := [effect]) (latent := [request])
      (.variable (by simp [Environment.extend, helperContract]) formed) sequenced_source (by simp) helperCertified



private def bothReq : Requirements [] := .sequence emptyReq (.sequence callReq callReq)
private def bothPlan := Plan.sequence Plan.pure (Plan.sequence callPlan callPlan)
private def bothRows : Rows (signature bothPlan) := sequenceRows Rows.pure (sequenceRows callRows callRows)
private def before : Code := .bind 99 run both
private def beforePlan := Plan.sequence operationPlan bothPlan
private def beforeRows : Rows (signature beforePlan) := sequenceRows operationRows bothRows
private def beforeReq : Requirements [] := .sequence operationReq bothReq
private def baseContext := Context.cell (identity := 0) Context.nil
private def baseStack : Stack := .push (.cell 0 42 .none .integer) .nil
private def plain : PlainData where
  context := .bind 99 both
  scope := .none
  input := .integer
  output := .integer
  pending := []
  translated := by rfl
private def focusedContext := Context.plain bothRows baseContext
private def focusedStack := Stack.push (.plain plain) baseStack
private def reply : Code := .integer 42
private def plugged : Code := .bind 99 reply both
private def pluggedPlan := Plan.sequence Plan.pure bothPlan
private def pluggedRows : Rows (signature pluggedPlan) := sequenceRows Rows.pure bothRows
private def root : Requirements [] := .request [] []
private def noActions : Syntax.UsageTickets := fun _ => none
private def phases : OwnerPhaseTransitions.Phases := OwnerPhaseTransitions.empty

private theorem operation_structural : ReadRows operationRows := .sequence .pure .read
private theorem helper_structural : ReadRows helperRows := .sequence .pure (.sequence .pure operation_structural)
private theorem call_structural : ReadRows callRows := .sequence .pure (.sequence .pure helper_structural)
private theorem both_structural : ReadRows bothRows := .sequence .pure (.sequence call_structural call_structural)
private theorem before_structural : ReadRows beforeRows := .sequence operation_structural both_structural

private theorem before_source : Source globals [] world [effect] .none Environment.empty before .integer [] beforeReq beforePlan beforeRows :=
  .bind run_source both_source

open CoreCallableReceiverRefinement (LexicalBounds)
open SourceScheduledCleanupInterfaces.Lexical.Recursive

private theorem run_authenticated (source : Source globals outward currentWorld [effect] scope environment
    run .integer [] operationReq operationPlan operationRows) (issued : 0 ∈ currentWorld) (received : 0 ∈ receiver) :
    Authenticated globals.registry outward source lexical receiver := by
  refine .checked ?_ (.perform (known := by simp [globals, Globals.registry]) (admitted := by simp)
    (formed := by change [] ⊆ currentWorld; simp) (.checked ?_ (.reference (issued := issued))))
  all_goals apply SourceSupport.bounds_iff.mpr
  all_goals simp [run, effect, Code.dependencies, ScopedPorts.Support.evaluate,
    Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources, received]

private theorem simple_authenticated (source : Source globals outward currentWorld allowed scope environment
    simple action [] emptyReq .pure Rows.pure) (issued : 0 ∈ currentWorld) (received : 0 ∈ receiver) :
    Authenticated globals.registry outward source lexical receiver := by
  refine .checked ?_ (.lambda (bodySource := .perform (by simp [globals, Globals.registry]) (by simp)
    (.reference issued) (by change [] ⊆ currentWorld; simp)) (Refines.identity operationRows)
    operation_outward (by simp [request]) (.sequence .pure .request) ?_ ?_ ?_)
  · apply SourceSupport.bounds_iff.mpr
    simp [simple, run, effect, Code.dependencies, Syntax.without, ScopedPorts.Support.evaluate,
      Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources, received]
  · change [0] ⊆ currentWorld
    simpa using issued
  · intro name member
    simp [effect, Code.dependencies, Syntax.without, Instantiation.freezeEffect,
      effectAtoms, Instantiation.Effect.resources] at member
  · intro nextLexical call _ captured
    apply run_authenticated _ (call.worldExtended issued)
    apply captured
    simp [effect, Code.dependencies, Syntax.without, ScopedPorts.Support.evaluate,
      Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources]

private theorem sequenced_authenticated (source : Source globals outward currentWorld allowed scope environment
    sequenced action [] emptyReq .pure Rows.pure) (issued : 0 ∈ currentWorld) (received : 0 ∈ receiver) :
    Authenticated globals.registry outward source lexical receiver := by
  let bodySource : Source globals outward currentWorld [effect] .none (environment.extend 2 Contract.unit)
      (.bind 3 .unit run) .integer [] (.sequence emptyReq operationReq)
      (.sequence .pure operationPlan) (sequenceRows Rows.pure operationRows) :=
    .bind .unit (.perform (by simp [globals, Globals.registry]) (by simp) (.reference issued) (by change [] ⊆ currentWorld; simp))
  refine .checked ?_ (.lambda (bodySource := bodySource)
    (Refines.of_exact (CoreCallableRefinementTransport.Refines.pure_prefix CorePayloadRefinement.PurePlan.pure Rows.pure operationRows))
    (.sequence (.request (layers := [])) operation_outward) (by simp [request]) (.sequence .pure .request) ?_ ?_ ?_)
  · apply SourceSupport.bounds_iff.mpr
    simp [sequenced, run, effect, Code.dependencies, Syntax.without, ScopedPorts.Support.evaluate,
      Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources, received]
  · change [0] ⊆ currentWorld
    simpa using issued
  · intro name member
    simp [run, effect, Code.dependencies, Syntax.without, Instantiation.freezeEffect,
      effectAtoms, Instantiation.Effect.resources] at member
  · intro nextLexical call _ captured
    have cellReceived : 0 ∈ call.receiver := by
      apply captured
      simp [run, effect, Code.dependencies, Syntax.without, ScopedPorts.Support.evaluate,
        Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources]
    refine .checked ?_ (.bind (initialSource := .unit) (bodySource := .perform (by simp [globals, Globals.registry])
      (by simp) (.reference (call.worldExtended issued)) (by change [] ⊆ call.world; simp))
      (.checked ?_ .unit) (run_authenticated _ (call.worldExtended issued) cellReceived))
    all_goals apply SourceSupport.bounds_iff.mpr
    all_goals simp [run, effect, Code.dependencies, Syntax.without, ScopedPorts.Support.evaluate,
      Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources, cellReceived]

private theorem helper_authenticated (source : Source globals [] world allowed scope environment
    helper helperContract [] emptyReq .pure Rows.pure) (_received : 0 ∈ receiver) :
    Authenticated globals.registry [] source lexical receiver := by
  let bodySource : Source globals [] world [effect] .none (environment.extend 0 action)
      helperBody .integer [] helperReq helperPlan helperRows :=
    .app (.variable (by simp [Environment.extend, action]) actionFormed) .unit (by simp) planCertified
  refine .checked ?_ (.lambda (bodySource := bodySource) (Refines.identity helperRows)
    (.emitAfter (layers := []) (.sequence (.request (layers := [])) (.request (layers := []))))
    (by simp [request]) helperCertified ?_ ?_ ?_)
  · apply SourceSupport.bounds_iff.mpr
    simp [helper, helperBody, Code.dependencies, Syntax.without, ScopedPorts.Support.evaluate]
  · change [0, 0] ⊆ world
    simp [world]
  · intro name member
    simp [helperBody, Code.dependencies, Syntax.without] at member
  · intro nextLexical call _ _
    refine .checked ?_ (.app (admitted := by simp) (publicCertified := .sequence .pure .request)
      (functionSource := .variable (contract := action) (by simp [Environment.extend, action])
      (by change [0] ⊆ call.world; exact call.worldExtended)) (argumentSource := .unit)
      (.checked ?_ (.variable (known := by simp [Environment.extend, action])
        (formed := by change [0] ⊆ call.world; exact call.worldExtended) ⟨call.argument, by simp [LexicalBounds.lookup, LexicalBounds.extend]⟩))
      (.checked ?_ .unit))
    all_goals apply SourceSupport.bounds_iff.mpr
    all_goals simp [helperBody, Code.dependencies, ScopedPorts.Support.evaluate,
      LexicalBounds.environment, LexicalBounds.lookup, LexicalBounds.extend, call.argumentReceived]

private theorem both_authenticated (source : Source globals [] world [effect] scope environment
    both .integer [] bothReq bothPlan bothRows) (received : 0 ∈ receiver) :
    Authenticated globals.registry [] source lexical receiver := by
  have formed : ScopedPorts.InWorld world helperContract.port := by
    change [0, 0] ⊆ world
    simp [world]
  let first : Source globals [] world [effect] scope (environment.extend 10 helperContract)
      (.app (.variable 10) simple) .integer [] callReq callPlan callRows :=
    .app (.variable (by simp [Environment.extend, helperContract]) formed) simple_source (by simp) helperCertified
  let second : Source globals [] world [effect] scope ((environment.extend 10 helperContract).extend 11 Contract.integer)
      (.app (.variable 10) sequenced) .integer [] callReq callPlan callRows :=
    .app (.variable (by simp [Environment.extend, helperContract]) formed) sequenced_source (by simp) helperCertified
  refine .checked ?_ (.bind (initialSource := helper_source) (bodySource := .bind first second)
    (helper_authenticated _ received) (.checked ?_ (.bind (initialSource := first) (bodySource := second)
      (.checked ?_ (.app (admitted := by simp) (publicCertified := helperCertified) (functionSource := .variable (contract := helperContract) (by simp [Environment.extend, helperContract]) formed)
        (argumentSource := simple_source) (.checked ?_ (.variable (known := by simp [Environment.extend, helperContract]) (formed := formed) ⟨receiver, by simp [LexicalBounds.lookup, LexicalBounds.extend]⟩))
        (simple_authenticated _ (by simp [world]) received)))
      (.checked ?_ (.app (admitted := by simp) (publicCertified := helperCertified) (functionSource := .variable (contract := helperContract) (by simp [Environment.extend, helperContract]) formed)
        (argumentSource := sequenced_source) (.checked ?_ (.variable (known := by simp [Environment.extend, helperContract]) (formed := formed) ⟨receiver, by simp [LexicalBounds.lookup, LexicalBounds.extend]⟩))
        (sequenced_authenticated _ (by simp [world]) received))))))
  all_goals apply SourceSupport.bounds_iff.mpr
  all_goals simp [both, bothBody, helper, helperBody, simple, sequenced, run, effect,
    Code.dependencies, Syntax.without, ScopedPorts.Support.evaluate, LexicalBounds.environment,
    LexicalBounds.lookup, LexicalBounds.extend, Instantiation.freezeEffect, effectAtoms,
    Instantiation.Effect.resources, received]

private theorem before_supported : CoreCallableContractAdmission.Supported globals [] world [effect] .none Environment.empty
    ScopedPorts.Support.empty before .integer [] beforeReq beforePlan beforeRows [0] [0] := by
  refine ⟨before_source, ?_, List.Subset.refl _, ⟨[], rfl, .checked ?_
    (.bind (initialSource := run_source) (bodySource := both_source)
      (run_authenticated _ (by simp [world]) (by simp)) (both_authenticated _ (by simp)))⟩, List.Subset.refl _⟩
  all_goals apply SourceSupport.bounds_iff.mpr
  all_goals simp [before, both, bothBody, helper, helperBody, simple, sequenced, run, effect, Code.dependencies,
    Syntax.without, ScopedPorts.Support.evaluate, ScopedPorts.Support.empty, Instantiation.freezeEffect, effectAtoms,
    Instantiation.Effect.resources]

private theorem suffix_supported : CoreCallableContractAdmission.Supported globals [] world [effect] .none
    (Environment.empty.extend 99 Contract.integer) (ScopedPorts.Support.extend ScopedPorts.Support.empty 99 [0])
    both .integer [] bothReq bothPlan bothRows [0] [0] := by
  refine ⟨both_source, ?_, List.Subset.refl _, ⟨[(99, [0])], by funext name; by_cases same : name = 99 <;> simp [same, LexicalBounds.environment, LexicalBounds.lookup, ScopedPorts.Support.extend, ScopedPorts.Support.empty], both_authenticated _ (by simp)⟩, List.Subset.refl _⟩
  apply SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr
  simp [both, bothBody, helper, helperBody, simple, sequenced, run, effect, Code.dependencies,
    Syntax.without, ScopedPorts.Support.evaluate, Instantiation.freezeEffect, effectAtoms,
    Instantiation.Effect.resources]

private theorem frame_source : FrameSource globals [] world [effect] plain Contract.integer Contract.integer
    99 both [] bothReq bothPlan bothRows [0] [0] [0] := ⟨rfl, rfl, rfl, by simp [world], suffix_supported⟩

private theorem read_supported : CoreCallableContractAdmission.Supported globals [] world [effect] .none Environment.empty
    ScopedPorts.Support.empty run .integer [] operationReq operationPlan operationRows [0] [0] := by
  refine ⟨run_source, ?_, List.Subset.refl _, ⟨[], rfl, run_authenticated _ (by simp [world]) (by simp)⟩, List.Subset.refl _⟩
  apply SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.bounds_iff.mpr
  simp [run, effect, Code.dependencies, ScopedPorts.Support.evaluate, Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources]

private theorem reply_supported : CoreCallableContractAdmission.Supported globals [] world [effect] .none Environment.empty
    ScopedPorts.Support.empty reply .integer [] emptyReq .pure Rows.pure [] [0] :=
  ⟨.integer, SourceSupport.Bounds.canonical _ _, by simp, ⟨[], rfl, .checked (by apply SourceSupport.bounds_iff.mpr; simp [reply, Code.dependencies, ScopedPorts.Support.evaluate]) .integer⟩, List.Subset.refl _⟩

private theorem reply_closed : ClosedValue reply := by simp [reply, ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Code.dependencies]

private theorem plugged_supported : CoreCallableContractAdmission.Supported globals [] world [effect] .none Environment.empty
    ScopedPorts.Support.empty plugged .integer [] (.sequence emptyReq bothReq) pluggedPlan pluggedRows [0] [0] := by
  refine ⟨.bind reply_supported.source suffix_supported.source, ?_, List.Subset.refl _,
    ⟨[], rfl, .checked ?_ (.bind (initialSource := reply_supported.source) (bodySource := suffix_supported.source)
      (.checked (by apply SourceSupport.bounds_iff.mpr; simp [reply, Code.dependencies, ScopedPorts.Support.evaluate]) .integer) (both_authenticated _ (by simp)))⟩, List.Subset.refl _⟩
  all_goals apply SourceSupport.bounds_iff.mpr
  all_goals simp [plugged, reply, both, bothBody, helper, helperBody, simple, sequenced, run, effect, Code.dependencies,
    Syntax.without, ScopedPorts.Support.evaluate, ScopedPorts.Support.empty, Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources]

private theorem after_supported : CoreCallableContractAdmission.Supported globals [] world [effect] .none Environment.empty
    ScopedPorts.Support.empty (both.subst 99 reply) .integer [] bothReq bothPlan bothRows [0] [0] := by
  obtain ⟨nextPlan, nextRows, supported, exactPlan, sameSignature, sameRows, _⟩ :=
    FrameSource.plug (fun recipes same => ClauseDeclarations.signature_congr recipes same) frame_source
      ⟨reply_supported.source, .nil, List.Subset.refl _, reply_supported.authentication, List.Subset.refl _⟩ reply_closed
  have planSame : nextPlan = bothPlan := by
    rw [exactPlan]
    simp [both, bothBody, helper, helperBody, simple, sequenced, run, CoreCallablePlanSubstitution.plan,
      bothPlan, callPlan, helperPlan]
  cases planSame
  cases eq_of_heq sameRows
  exact supported


/-- One connected segment. All five sites carry actual source, saved recursive
frames, constructed M4 checks and the same executable root. No old Valid
or desired successor admission is included. -/
structure Segment where
  initial : Site globals [] world [effect] noActions phases [] [] [] before .none baseStack Contract.integer Contract.integer baseContext root
  focused : Site globals [] world [effect] noActions phases [] [] [] run .none focusedStack Contract.integer Contract.integer focusedContext root
  replied : Site globals [] world [effect] noActions phases [] [] [] reply .none focusedStack Contract.integer Contract.integer focusedContext root
  pluggedSite : Site globals [] world [effect] noActions phases [] [] [] plugged .none baseStack Contract.integer Contract.integer baseContext root
  final : Site globals [] world [effect] noActions phases [] [] [] (both.subst 99 reply) .none baseStack Contract.integer Contract.integer baseContext root
  focusStep : RawStep ⟨before, .none, baseStack⟩ ⟨run, .none, focusedStack⟩ [] []
  replyStep : RawStep ⟨run, .none, focusedStack⟩ ⟨reply, .none, focusedStack⟩ [] []
  plugStep : RawStep ⟨reply, .none, focusedStack⟩ ⟨plugged, .none, baseStack⟩ [] []
  bindStep : RawStep ⟨plugged, .none, baseStack⟩ ⟨both.subst 99 reply, .none, baseStack⟩ [] []

/-- Construct the nonvacuous predecessor and derive its four successors.
The suffix source used by the initial bind is the same witness retained in
frame_source and substituted at final; checks are split/plugged from initial. -/
theorem constructed_segment : Nonempty Segment := by
  obtain ⟨initialCertificate, initialChecked⟩ := before_structural.admission (outward := [])
    (actions := noActions) (budget := []) (phases := phases) (world := world) (installations := []) (ambient := []) ReadReceiver.cell
  have initialRun : Accounting.Run world [] beforeRows baseContext root :=
    before_structural.accounting ReadReceiver.cell (.cell .nil)
  have emptyCheck : Checked [] [] phases (annotateDisposals root) [] := by
    change Checked [] [] phases root []
    exact .request rfl
  have split : FocusRows beforeRows operationRows bothRows := .sequence
  obtain ⟨focusedCertificate, suffixCertificate⟩ := split.source_certificate initialCertificate
  obtain ⟨focusedChecked, suffixChecked⟩ := InstallationSupport.focus_rows split initialChecked
  have focusedRun : Accounting.Run world [] operationRows focusedContext root := initialRun.focus_rows split
  have requestedRun : Accounting.Run world [] (Rows.request (effect := effect) (operation := 0)) focusedContext root :=
    (Accounting.silent_prefix_iff .pure Rows.pure Rows.request).mp focusedRun
  have replyWait : Accounting.Wait world [] focusedContext .ordinary root :=
    requestedRun.builtin_wait (ReadReceiver.select (.plain .cell))
  have suffixRun : Accounting.Run world [] bothRows baseContext root := by
    cases replyWait with | plain code => exact code
  have replyRun : Accounting.Run world [] Rows.pure focusedContext root := .pure replyWait
  have pluggedRun : Accounting.Run world [] pluggedRows baseContext root := PlugRows.single.accounting_iff.mpr suffixRun
  let basePending : CoreCallableContractExecution.Pending globals [] world [effect] [] baseStack Contract.integer Contract.integer baseContext :=
    .cell (by simp [world]) rfl .nil
  let focusedPending : CoreCallableContractExecution.Pending globals [] world [effect] [] focusedStack Contract.integer Contract.integer focusedContext :=
    .plain frame_source (List.Subset.refl _) (by intro identity _ member; exact member) basePending
  let baseRetained : SourceAdmission.Pending [] noActions [] phases world [] baseContext .nil .ordinary .ordinary := .cell .nil
  have baseRetainedChecked : InstallationSupport.PendingChecked [] [] baseRetained := .cell .nil
  let focusedRetained : SourceAdmission.Pending [] noActions [] phases world [] focusedContext .nil .ordinary .ordinary :=
    .plain suffixCertificate baseRetained
  have focusedRetainedChecked : InstallationSupport.PendingChecked [] [] focusedRetained := .plain suffixChecked baseRetainedChecked
  let initial : Site globals [] world [effect] noActions phases [] [] [] before .none baseStack Contract.integer Contract.integer baseContext root :=
    { sourceDemand := [], requirements := beforeReq, dependencies := _, plan := beforePlan, rows := beforeRows,
      bound := [0], current := before_supported, received := by exact List.Subset.refl _,
      certificate := initialCertificate, certificateChecked := initialChecked,
      pending := basePending, retained := baseRetained, retainedChecked := baseRetainedChecked,
      accounting := initialRun, annotated := root, row := [], annotation := .original, checked := emptyCheck, bounded := List.Subset.refl _ }
  let focused : Site globals [] world [effect] noActions phases [] [] [] run .none focusedStack Contract.integer Contract.integer focusedContext root :=
    { sourceDemand := [], requirements := operationReq, dependencies := _, plan := operationPlan, rows := operationRows,
      bound := [0], current := read_supported, received := by exact List.Subset.refl _,
      certificate := focusedCertificate, certificateChecked := focusedChecked,
      pending := focusedPending, retained := focusedRetained, retainedChecked := focusedRetainedChecked,
      accounting := focusedRun, annotated := root, row := [], annotation := .original, checked := emptyCheck, bounded := List.Subset.refl _ }
  let replied : Site globals [] world [effect] noActions phases [] [] [] reply .none focusedStack Contract.integer Contract.integer focusedContext root :=
    { sourceDemand := [], requirements := emptyReq, dependencies := _, plan := .pure, rows := Rows.pure,
      bound := [], current := reply_supported, received := by simp,
      certificate := .pure, certificateChecked := .pure,
      pending := focusedPending, retained := focusedRetained, retainedChecked := focusedRetainedChecked,
      accounting := replyRun, annotated := root, row := [], annotation := .original, checked := emptyCheck, bounded := List.Subset.refl _ }
  let pluggedSite : Site globals [] world [effect] noActions phases [] [] [] plugged .none baseStack Contract.integer Contract.integer baseContext root :=
    { sourceDemand := [], requirements := .sequence emptyReq bothReq, dependencies := _, plan := pluggedPlan, rows := pluggedRows,
      bound := [0], current := plugged_supported, received := by exact List.Subset.refl _,
      certificate := PlugRows.single.source_certificate suffixCertificate,
      certificateChecked := InstallationSupport.plug_rows PlugRows.single suffixChecked,
      pending := basePending, retained := baseRetained, retainedChecked := baseRetainedChecked,
      accounting := pluggedRun, annotated := root, row := [], annotation := .original, checked := emptyCheck, bounded := List.Subset.refl _ }
  let final : Site globals [] world [effect] noActions phases [] [] [] (both.subst 99 reply) .none baseStack Contract.integer Contract.integer baseContext root :=
    { sourceDemand := [], requirements := bothReq, dependencies := _, plan := bothPlan, rows := bothRows,
      bound := [0], current := after_supported, received := by exact List.Subset.refl _,
      certificate := suffixCertificate, certificateChecked := suffixChecked,
      pending := basePending, retained := baseRetained, retainedChecked := baseRetainedChecked,
      accounting := suffixRun, annotated := root, row := [], annotation := .original, checked := emptyCheck, bounded := List.Subset.refl _ }
  have focusStep : RawStep ⟨before, .none, baseStack⟩ ⟨run, .none, focusedStack⟩ [] [] :=
    .focus plain (.bind (by simp [run, Code.IsValue])) baseStack
  have replyStep : RawStep ⟨run, .none, focusedStack⟩ ⟨reply, .none, focusedStack⟩ [] [] :=
    .readCell 0 42 .none focusedStack focusedStack (.push (by simp [ExecFrame.erase, PlainData.erase, Frame.target]) .hit)
  have plugStep : RawStep ⟨reply, .none, focusedStack⟩ ⟨plugged, .none, baseStack⟩ [] [] := .plug plain reply reply_closed .none baseStack
  have bindStep : RawStep ⟨plugged, .none, baseStack⟩ ⟨both.subst 99 reply, .none, baseStack⟩ [] [] :=
    .bind 99 reply both .none baseStack reply_closed (by
      simp [both, bothBody, helper, helperBody, simple, sequenced, run, effect, ClosedExcept, Code.dependencies,
        Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources, Syntax.without])
  exact ⟨⟨initial, focused, replied, pluggedSite, final, focusStep, replyStep, plugStep, bindStep⟩⟩

/-- Start from the constructed nonvacuous predecessor, then use the generic
current/saved-frame/exact-reply transports for every edge. The endpoint carries
its actual recursive private bodies and current checks from that predecessor. -/
theorem transported_segment :
    ∃ output : Contract, ∃ _next : Site globals [] world [effect] noActions phases [] [] []
      (both.subst 99 reply) .none baseStack output Contract.integer baseContext root,
      RawTrace ⟨before, .none, baseStack⟩ ⟨both.subst 99 reply, .none, baseStack⟩ [] [] := by
  obtain ⟨segment⟩ := constructed_segment
  obtain ⟨input, data, dependencies, plan, rows, position, sameScope, focused, focusStep⟩ :=
    Site.focus_bind segment.initial (by simp [run, Code.IsValue]) plain.translated
  have update : CellUpdate 0 42 42 (.push (.plain data) baseStack) (.push (.plain data) baseStack) :=
    .push (by simp [ExecFrame.erase, PlainData.erase, Frame.target]) .hit
  obtain ⟨replied, readStep⟩ := Site.read_cell_reply focused (by simp [globals, effect]) update
  obtain ⟨parameter, body, pluggedPosition, output, pluggedSite, plugStep⟩ := Site.plug_bind replied reply_closed
  have sameContext : ScopedExecution.Context.bind 99 both = .bind parameter body := position.symm.trans pluggedPosition
  obtain ⟨sameParameter, sameBody⟩ := ScopedExecution.Context.bind.inj sameContext
  subst parameter
  subst body
  rw [sameScope] at pluggedSite plugStep
  obtain ⟨finalSite, bindStep⟩ := Site.bind_value (fun recipes same => ClauseDeclarations.signature_congr recipes same) pluggedSite reply_closed (by
    simp [both, bothBody, helper, helperBody, simple, sequenced, run, effect, ClosedExcept, Code.dependencies,
      Instantiation.freezeEffect, effectAtoms, Instantiation.Effect.resources, Syntax.without])
  exact ⟨output, finalSite, .next focusStep (.next readStep (.next plugStep (.next bindStep (.refl _))))⟩

#print axioms both_source
#print axioms before_supported
#print axioms suffix_supported
#print axioms constructed_segment
#print axioms transported_segment
end
end Ash.OneShot.CoreCallableContractExecutionExamples
