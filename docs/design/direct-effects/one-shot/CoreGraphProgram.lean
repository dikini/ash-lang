import CoreGraphAdmission
import CoreInitialPrefix

/-! Initial admission assembly for the actual exported graph root. Plan
certificates retain its helper closures, administrative binds, resource handle,
cleanup callback and consuming clause suffix. -/
namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram
open ScopedExpressions ProtectionContracts
open SourceDependencyAnnotations (Dependencies)
open SourcePlanSignatures (signature)
open SourceDeclarationPlans (Plan)
open InstallationSupport
open CoreInitialExample
def planDependencies {dependencies : Dependencies} (_plan : Plan dependencies) := dependencies

theorem writeFootprint : SourceRequestFootprints.Footprint (signature (CoreGraphAdmission.Writes.plan identity)) [(.cell identity, 1)] :=
  .sequence .pure (.sequence (.sequence .pure .pure) (.sequence .pure .request))

/-- D9's consuming-prefix/static-suffix recipe retains every administrative
prefix of the actual exported write helper. -/
theorem clauseRecipe :
    ClauseRecipe [] ⟨true, true⟩ [(.cell identity, 1)] (fun owner => planDependencies (CoreGraphAdmission.Clause.plan identity owner)) := by
  apply ClauseRecipe.sequence SourceRequestFootprints.Footprint.pure
  apply ClauseRecipe.choice (firstRequired := [(.cell identity, 1)]) (secondRequired := [])
  · have consuming : ClauseRecipe [] ⟨true, true⟩ []
        (fun owner => .sequence .pure (.invoke ⟨owner, .resume⟩)) :=
      .sequence .pure (.existing (.resume rfl))
    simpa [externalRequirements, SourceContextualRequirements.providerScope,
      SourceHandlerRequirements.outwardRequirements, SourceHandlerRequirements.reaches]
      using ClauseRecipe.suffix consuming (writeFootprint (identity := identity))
  · exact .existing (.dispose rfl)

theorem declarationRecipe :
    ClauseDeclarations [] CoreGraphAdmission.Handler.arms
      [(0, some (fun owner => planDependencies (CoreGraphAdmission.Clause.plan identity owner)), none)] [(.cell identity, 1)] :=
  by
  apply ClauseDeclarations.cons (operation := 0) (parameter := 9)
    (binder := CoreGraphAdmission.Clause.ticket) (body := CoreGraphAdmission.Clause.code)
    (ordinaryRequired := [(.cell identity, 1)]) (protectedRequired := []) (restRequired := [])
  · exact .available clauseRecipe
  · exact .unavailable
  · exact .nil

theorem certified : SourcePlannedChecks.Certified (evidence := declarationPolicy) [] [] CoreGraphAdmission.Main.rootPlan := by
  letI : SourcePlannedChecks.DeclarationPolicy := declarationPolicy
  unfold CoreGraphAdmission.Main.rootPlan CoreGraphAdmission.Main.applicationPlan CoreGraphAdmission.Main.bodyPlan CoreGraphAdmission.Resource.plan
  apply SourcePlannedChecks.Certified.sequence .pure
  apply SourcePlannedChecks.Certified.sequence .pure
  apply SourcePlannedChecks.Certified.sequence .pure
  apply SourcePlannedChecks.Certified.sequence .pure
  apply SourcePlannedChecks.Certified.sequence .pure
  apply SourcePlannedChecks.Certified.resource
  intro identity fresh
  unfold CoreGraphAdmission.Spine.plan CoreGraphAdmission.Handler.plan CoreGraphAdmission.Guarded.plan CoreGraphAdmission.Guarded.cleanupPlan
    CoreGraphAdmission.Guarded.bodyPlan CoreGraphAdmission.Guarded.afterSecondPlan CoreGraphAdmission.Writes.plan CoreGraphAdmission.Writes.tuplePlan
    CoreInitialExample.requestPlan
  apply SourcePlannedChecks.Certified.sequence .pure
  apply SourcePlannedChecks.Certified.sequence .pure
  apply SourcePlannedChecks.Certified.sequence .pure
  apply SourcePlannedChecks.Certified.sequence
  · apply SourcePlannedChecks.Certified.handler declarationRecipe
    · apply SourcePlannedChecks.CertifiedClauses.cons
      · apply SourcePlannedChecks.CertifiedModes.available
        intro owner
        exact .sequence .pure (.choice (.sequence (.sequence .pure .invoke)
          (.sequence .pure (.sequence (.sequence .pure .pure) (.sequence .pure .request)))) .invoke)
      · exact .unavailable
      · exact .nil
    · exact .sequence .pure (.sequence .pure (.cleanup
        (.sequence .pure (.sequence (.sequence .pure .pure) (.sequence .pure .request)))
        (.sequence (.sequence .pure .request) (.sequence (.sequence .pure .request)
          (.sequence .pure (.sequence (.sequence .pure .pure) (.sequence .pure .request)))))))
  · exact .sequence .pure (.sequence .pure (.sequence .pure .request))

theorem source : SourcePlannedSources.Expression operations policy CoreGraphAdmission.Spine.emptyContracts [] [] .none
    (fun _ => none) CoreGraphAdmission.Main.root .integer [] CoreGraphAdmission.Main.rootRequirements (signature CoreGraphAdmission.Main.rootPlan) := by
  obtain ⟨raw, translated, instantiated, source, authenticated⟩ := CoreGraphAdmission.Main.rootCompiled 0
  exact source

theorem authenticated : Auth operations policy ports CoreGraphAdmission.Spine.emptyOwners CoreGraphAdmission.Spine.emptyEnvironmentRows
    source .integer CoreGraphAdmission.Main.rootRows := by
  obtain ⟨raw, translated, instantiated, source, authenticated⟩ := CoreGraphAdmission.Main.rootCompiled 0
  exact authenticated

theorem actualRoot : CoreGraphAdmission.Main.root = CoreInitialPrefix.rootCode := rfl

open SourceDependencyChecks.Lexical (ReturnHints)
open OwnerPhaseTransitions (Phases)
open LexicalUnwind (UseMode)
open CoreKernelProgram
open RecursiveRequirements (Requirements LocalOwner)

/-- Only pure administrative rows, exact local cell requests and sequencing.
No callback, handler, owner invocation or arbitrary admission leaf is accepted. -/
inductive BuiltinRows (identity : Nat) : {dependencies : Dependencies} →
    {checking : SourcePlanSignatures.Signature dependencies} → Rows checking → Type where
  | pure : BuiltinRows identity Rows.pure
  | request (operation : Nat) : BuiltinRows identity (Rows.request (effect := .cell identity) (operation := operation))
  | sequence : BuiltinRows identity first → BuiltinRows identity second → BuiltinRows identity (Rows.sequence first second)

variable {actions : Syntax.UsageTickets} {phases : Phases} {world installations : List Nat}
  {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope} {context : Context hints}

noncomputable def BuiltinRows.proof (shape : BuiltinRows identity rows)
    (found : ∀ operation, select (.cell identity) operation context = some (.builtin identity)) :
    SourceProof actions phases world installations rows context := by
  induction shape generalizing scope with
  | pure => exact pureProof
  | request operation => exact builtinProof (found operation)
  | sequence first second ihFirst ihSecond =>
      exact SourceProof.sequence
        (ihFirst (fun operation => by simp only [select, found operation, Option.map_some, Selection.prepend]))
        (ihSecond found)

theorem BuiltinRows.accounting (shape : BuiltinRows identity rows)
    (found : ∀ operation, select (.cell identity) operation context = some (.builtin identity))
    (waiting : Accounting.Wait world installations context .ordinary root) :
    Accounting.Run world installations rows context root := by
  induction shape generalizing scope with
  | pure => exact .pure waiting
  | request operation => exact .builtin (found operation) waiting
  | sequence first second ihFirst ihSecond =>
      exact .sequence (ihFirst
        (fun operation => by simp only [select, found operation, Option.map_some, Selection.prepend])
        (.plain (ihSecond found waiting)))

inductive ReceiverTail (identity : Nat) : {scope : SourceDependencyCapture.Scope} →
    {hints : ReturnHints scope} → Context hints → Type where
  | cell : ReceiverTail identity (Context.cell (identity := identity) .nil)
  | plain {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope} {context : Context hints}
      (shape : BuiltinRows identity rows) (tail : ReceiverTail identity context) :
      ReceiverTail identity (.plain rows context)
  | spent {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope} {context : Context hints}
      (tail : ReceiverTail identity context) : ReceiverTail identity (.spent (owner := owner) context)

theorem ReceiverTail.lookup (tail : ReceiverTail identity context) :
    select (.cell identity) operation context = some (.builtin identity) := by
  induction tail with
  | cell => simp [select]
  | plain shape tail ih => simp only [select, ih, Option.map_some, Selection.prepend]
  | spent tail ih => simp only [select, ih, Option.map_some, Selection.prepend]

noncomputable def ReceiverTail.pending (tail : ReceiverTail identity context) :
    PendingProof actions phases world installations context Context.nil .ordinary .ordinary := by
  induction tail with
  | cell => exact ⟨.cell .nil, .cell .nil⟩
  | plain shape tail ih =>
      exact PendingProof.plain (shape.proof (fun _ => tail.lookup)) ih
  | spent tail ih => exact ⟨.spent ih.pending, .spent ih.checked⟩

theorem ReceiverTail.ordinaryMode (tail : ReceiverTail identity context) :
    context.hints.returnMode .ordinary = .ordinary := by
  induction tail <;> simp_all [Context.hints, ReturnHints.returnMode]

theorem ReceiverTail.exportCell (tail : ReceiverTail identity context) :
    OwnerSource.exportAt context.context phases [⟨.cell identity, operation, held⟩] = some [] := by
  induction tail with
  | cell =>
      simp [OwnerSource.exportAt, Context.context, OwnerPhaseTransitions.project,
        ProtectionResiduals.residualize, ProtectionResiduals.throughLayer,
        ProtectionResiduals.demandThrough, ProtectionResiduals.merge]
  | plain shape tail ih =>
      simpa [OwnerSource.exportAt, Context.context, OwnerPhaseTransitions.project,
        ProtectionResiduals.residualize, ProtectionResiduals.throughLayer,
        ProtectionResiduals.demandThrough, ProtectionResiduals.merge] using ih
  | spent tail ih => exact ih

noncomputable def ReceiverTail.root (tail : ReceiverTail identity context) : Requirements [] := by
  induction tail with
  | cell => exact empty
  | plain shape tail ih => exact ih
  | @spent owner scope hints context tail ih => exact .sequence (.spent owner) ih

theorem ReceiverTail.accounting (tail : ReceiverTail identity context) :
    Accounting.Wait world installations context .ordinary tail.root := by
  induction tail with
  | cell => exact .cell .nil
  | plain shape tail ih => exact .plain (shape.accounting (fun _ => tail.lookup) ih)
  | spent tail ih => exact .spent ih

theorem ReceiverTail.accountingUnwind (tail : ReceiverTail identity context) :
    Accounting.Wait world installations context .unwind tail.root := by
  induction tail with
  | cell => exact .cell .nil
  | plain shape tail ih => exact .skipped ih
  | spent tail ih => exact .spent ih

theorem ReceiverTail.localOwner (tail : ReceiverTail identity context) (absent : owner ∉ context.ticketNames) :
    LocalOwner owner phase tail.root tail.root phase := by
  induction tail with
  | cell => exact .empty
  | plain shape tail ih => exact ih absent
  | @spent other scope hints context tail ih =>
      have separate : other ≠ owner := by
        intro same; subst other
        exact absent (by simp [Context.ticketNames])
      exact .sequence (.spentOther separate) (ih (by
        intro member; exact absent (by simp [Context.ticketNames, member])))

/-- Structural consuming admission with its actual finite builtin suffix. -/
noncomputable def consumingClause {suffixDependencies : Dependencies}
    {suffixChecking : SourcePlanSignatures.Signature suffixDependencies} {suffixRows : Rows suffixChecking}
    (suffix : BuiltinRows identity suffixRows) (tail : ReceiverTail identity context) (captured : Context capturedHints)
    (capturedMode : captured.hints.returnMode .ordinary = .ordinary)
    (unprotected : captured.pack.scope.held = false)
    (ordinary : ∀ {actions : Syntax.UsageTickets} {phases : Phases} {world installations : List Nat}
      {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope} {receiving : Context hints},
      ReceiverTail identity receiving → PendingProof actions phases world installations
        (captured.append receiving) Context.nil .ordinary .ordinary)
    (unwind : ∀ {actions : Syntax.UsageTickets} {phases : Phases} {world installations : List Nat}
      {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope} {receiving : Context hints},
      ReceiverTail identity receiving → PendingProof actions phases world installations
        captured (Context.closing receiving) .unwind .unwind)
    (owner : Nat) (resumeDemand : List Nat) :
    SourceProof (actions.insert owner ⟨true, true⟩) (OwnerPhaseTransitions.introduce phases owner)
      world installations
      (.sequence .pure (.choice
        (.sequence (.sequence .pure (.invoke (key := ⟨owner, .resume⟩))) suffixRows)
        (.invoke (key := ⟨owner, .dispose⟩))))
      (.live (owner := owner) (resumeDemand := resumeDemand) captured context) := by
  have callerMode := tail.ordinaryMode
  dsimp only [Context.hints] at callerMode
  have savedMode := capturedMode
  dsimp only [Context.hints] at savedMode
  let nextActions := actions.insert owner ⟨true, true⟩
  let nextPhases := OwnerPhaseTransitions.introduce phases owner
  let resumedTail := ReceiverTail.plain suffix (ReceiverTail.spent (owner := owner) tail)
  let restored := ordinary (actions := nextActions) (phases := OwnerPhaseTransitions.spend nextPhases owner)
    (world := world) (installations := installations) resumedTail
  let caller := ReceiverTail.pending (actions := nextActions) (phases := OwnerPhaseTransitions.spend nextPhases owner)
    (world := world) (installations := installations) (ReceiverTail.spent (owner := owner) tail)
  let abandoned := unwind (actions := nextActions) (phases := OwnerPhaseTransitions.spend nextPhases owner)
    (world := world) (installations := installations) (ReceiverTail.spent (owner := owner) tail)
  let resumes : SourceAdmission.Code [] nextActions [] nextPhases world installations
      (.invoke (key := ⟨owner, .resume⟩))
      (.plain suffixRows
        (.live (owner := owner) (resumeDemand := resumeDemand) captured context)) := by
    apply SourceAdmission.Code.resume (front := .plain suffixRows .nil)
      (captured := captured) (tail := context) (rights := ⟨true, true⟩)
    · exact .plain .hit
    · simp [nextActions, Syntax.UsageTickets.insert]
    · rfl
    · simp [nextPhases, OwnerPhaseTransitions.introduce]
    · change ResumeShape (captured.hints.returnMode .ordinary) _ = true
      rw [capturedMode]; rfl
    · simpa only [Context.append, ReturnHints.append, SourceDependencyCapture.Scope.append,
      ReturnHints.returnMode, Context.hints, savedMode, callerMode] using restored.pending
  let disposes : SourceAdmission.Code [] nextActions [] nextPhases world installations
      (.invoke (key := ⟨owner, .dispose⟩))
      (.live (owner := owner) (resumeDemand := resumeDemand) captured context) := by
    apply SourceAdmission.Code.dispose (front := .nil) (captured := captured)
      (tail := context) (rights := ⟨true, true⟩)
    · exact .hit
    · simp [nextActions, Syntax.UsageTickets.insert]
    · rfl
    · simp [nextPhases, OwnerPhaseTransitions.introduce]
    · exact unprotected
    · exact abandoned.pending
    · simpa only [Context.append, ReturnHints.append, SourceDependencyCapture.Scope.append,
      ReturnHints.returnMode, Context.hints, savedMode, callerMode] using caller.pending
  let writes := suffix.proof (actions := nextActions) (phases := nextPhases) (world := world)
    (installations := installations)
    (context := Context.live (owner := owner) (resumeDemand := resumeDemand) captured context)
    (fun operation => by change (select (.cell identity) operation context).map _ = _; rw [tail.lookup]; rfl)
  refine ⟨.sequence .pure (.choice (.sequence (.sequence .pure resumes) writes.code) disposes), ?_⟩
  apply CodeChecked.sequence (first := .pure) (second := .choice (.sequence (.sequence .pure resumes) writes.code) disposes) .pure
  apply CodeChecked.choice (first := .sequence (.sequence .pure resumes) writes.code) (second := disposes)
  · apply CodeChecked.sequence
    · apply CodeChecked.sequence (first := .pure) (second := resumes) .pure
      apply CodeChecked.resume (front := .plain suffixRows .nil)
        (captured := captured) (tail := context) (rights := ⟨true, true⟩)
        (located := .plain .hit) (known := by simp [nextActions, Syntax.UsageTickets.insert])
        (permission := rfl) (available := by simp [nextPhases, OwnerPhaseTransitions.introduce])
        (resumeShape := by change ResumeShape (captured.hints.returnMode .ordinary) _ = true; rw [capturedMode]; rfl)
        (restored := by simpa only [Context.append, ReturnHints.append, SourceDependencyCapture.Scope.append,
          ReturnHints.returnMode, Context.hints, savedMode, callerMode] using restored.pending)
      simpa only [Context.append, ReturnHints.append, SourceDependencyCapture.Scope.append,
        ReturnHints.returnMode, Context.hints, savedMode, callerMode] using restored.checked
    · exact writes.checked
  · apply CodeChecked.dispose (front := .nil) (captured := captured)
      (tail := context) (rights := ⟨true, true⟩) (located := .hit)
      (known := by simp [nextActions, Syntax.UsageTickets.insert]) (permission := rfl)
      (available := by simp [nextPhases, OwnerPhaseTransitions.introduce]) (unprotected := unprotected)
      (abandoned := abandoned.pending)
      (waiting := by simpa only [Context.append, ReturnHints.append, SourceDependencyCapture.Scope.append,
        ReturnHints.returnMode, Context.hints, savedMode, callerMode] using caller.pending) abandoned.checked
    simpa only [Context.append, ReturnHints.append, SourceDependencyCapture.Scope.append,
      ReturnHints.returnMode, Context.hints, savedMode, callerMode] using caller.checked

def writeShape (identity : Nat) : BuiltinRows identity (CoreGraphAdmission.Writes.rows identity) :=
  .sequence .pure (.sequence (.sequence .pure .pure) (.sequence .pure (.request 1)))
def readShape (identity : Nat) : BuiltinRows identity (CoreExportedAdmission.applicationRows identity) :=
  .sequence .pure (.sequence .pure (.sequence .pure (.request 0)))

theorem BuiltinRows.within {rowDependencies : Dependencies}
    {checking : SourcePlanSignatures.Signature rowDependencies} {rows : Rows checking}
    (shape : BuiltinRows identity rows) :
    SourceDependencyOwners.Within world owned rowDependencies := by
  induction shape with
  | pure => exact .pure
  | request => exact .request
  | sequence first second ihFirst ihSecond => exact .sequence ihFirst ihSecond

def terminal (identity activation : Nat) :=
  Context.handler (effect := effect) (table := CoreGraphAdmission.Handler.table identity)
    activation (CoreGraphAdmission.Handler.declarationRows identity) .nil

def armed (identity activation : Nat) := Context.cleanup (needs := [.cell identity])
  (CoreGraphAdmission.Setter.footprint identity) (CoreGraphAdmission.Writes.rows identity) (terminal identity activation)

def capture {dependencies : Dependencies} {checking : SourcePlanSignatures.Signature dependencies}
    (identity activation : Nat) (rows : Rows checking) := Context.plain rows (armed identity activation)

noncomputable def armedOrdinary (tail : ReceiverTail identity context) :
    PendingProof actions phases world installations ((armed identity activation).append context)
      Context.nil .ordinary .ordinary := by
  let receiving := (terminal identity activation).append context
  let waiting := tail.pending (actions := actions) (phases := phases) (world := world) (installations := installations)
  let handled : PendingProof actions phases world installations receiving Context.nil .ordinary .ordinary :=
    ⟨.handler waiting.pending, .handler waiting.checked⟩
  let callback := (writeShape identity).proof (actions := actions) (phases := phases) (world := world)
    (installations := installations) (context := Context.normal receiving)
    (fun operation => by
      simp only [receiving, terminal, Context.append, ReturnHints.append, SourceDependencyCapture.Scope.append,
        select, effect, reduceCtorEq, ↓reduceIte]
      rw [tail.lookup]
      rfl)
  exact ⟨.cleanup (callback.code.reindex_context (Context.normal receiving).append_nil_pack.symm) handled.pending,
    .cleanup (callback.checked.reindex_context (Context.normal receiving).append_nil_pack.symm) handled.checked⟩

noncomputable def captureUnwind (tail : ReceiverTail identity context) (rows : Rows checking) :
    PendingProof actions phases world installations (capture identity activation rows)
      (Context.closing context) .unwind .unwind := by
  let receiving := (terminal identity activation).append (Context.closing context)
  let callback := (writeShape identity).proof (actions := actions) (phases := phases) (world := world)
    (installations := installations) (context := Context.unwinding receiving)
    (fun operation => by
      simp only [receiving, terminal, Context.append, ReturnHints.append, SourceDependencyCapture.Scope.append,
        select, effect, reduceCtorEq, ↓reduceIte]
      rw [tail.lookup]
      rfl)
  exact ⟨.skipped (.cleanup callback.code (.handler .nil)), .skipped (.cleanup callback.checked (.handler .nil))⟩

def captureMetadata (identity activation : Nat) (rows : Rows checking) :
    CleanupHints.Metadata (capture identity activation rows).pack.scope :=
  .plain (.cleanup (CoreGraphAdmission.Setter.footprint identity) (.handler activation .nil))

theorem captureBudgetCheck (tail : ReceiverTail identity context) (rows : Rows checking) :
    (captureMetadata identity activation rows).check context.context phases [] = true ∧
      (captureMetadata identity activation rows).check (.ordinary (.barrier true) :: context.context) phases [] = true := by
  have exported := tail.exportCell (phases := phases) (operation := 1) (held := true)
  change ProtectionResiduals.residualize (OwnerPhaseTransitions.project context.context phases)
    [⟨.cell identity, 1, true⟩] = some [] at exported
  constructor <;>
    simp [captureMetadata, CleanupHints.Metadata.check, CleanupHints.Metadata.closing,
      CleanupHints.Metadata.context, RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel,
      OwnerSource.exportAt, OwnerPhaseTransitions.project, OwnerPhaseTransitions.spendAll,
      CoreGraphAdmission.Setter.footprint, qualify, ProtectionResiduals.residualize, ProtectionResiduals.throughLayer,
      ProtectionResiduals.demandThrough, ProtectionResiduals.merge, ProtectionResiduals.residual_empty, effect, exported]

/-- One finite capture factory, used for both actual request suffixes. Its
pending and owner-check inputs are instantiated structurally below. -/
noncomputable def capturedRequest {capturedDependencies : Dependencies}
    {checking : SourcePlanSignatures.Signature capturedDependencies} (rows : Rows checking)
    (bounded : ∀ world owned, SourceDependencyOwners.Within world owned capturedDependencies)
    (ordinary : ∀ {actions : Syntax.UsageTickets} {phases : Phases} {world installations : List Nat}
      {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope} {receiving : Context hints},
      ReceiverTail identity receiving → PendingProof actions phases world installations
        ((capture identity activation rows).append receiving) Context.nil .ordinary .ordinary)
    (tail : ReceiverTail identity context) :
    SourceProof actions phases world installations (Rows.request (effect := effect) (operation := 0))
      ((capture identity activation rows).append context) := by
  have callerMode := tail.ordinaryMode
  dsimp only [Context.hints] at callerMode
  let captured := capture identity activation rows
  let whole := captured.append context
  have cut : Cut effect 0 whole captured context
      (ClauseContract.mk true (some (CoreGraphAdmission.Setter.footprint identity)) none)
      (some (fun owner => planDependencies (CoreGraphAdmission.Clause.plan identity owner)), none) := by rfl
  have guarded : SourceDependencyChecks.Lexical.Capture whole.pack.scope effect 0 := .handler rfl rfl rfl rfl
  have ownerBound : (ClauseContract.mk true (some (CoreGraphAdmission.Setter.footprint identity)) none).dispose = true →
      SourceDependencyOwners.PendingWithin world (SourceDependencyOwners.owners captured.pack.scope) captured.pack.scope :=
    fun _ => .plain (bounded _ _) (.cleanup (.handler .nil))
  have budget : RequestBudget [] phases effect 0 whole := by
    unfold RequestBudget
    rw [cut]
    intro _
    exact ⟨captureMetadata identity activation rows, rfl, (captureBudgetCheck tail rows).1, (captureBudgetCheck tail rows).2⟩
  let callback := captureUnwind (actions := actions) (phases := phases) (world := world)
    (installations := installations) (activation := activation) tail rows
  let retained := ordinary (actions := actions) (phases := phases) (world := world) (installations := installations) tail
  let clauses := fun owner resumeDemand => consumingClause (writeShape identity)
    (actions := actions) (phases := phases) (world := world) (installations := installations)
    tail captured rfl rfl ordinary (fun current => captureUnwind (activation := activation) current rows) owner resumeDemand
  let body := fun owner resumeDemand (_fresh : actions owner = none) (_absent : owner ∉ whole.ticketNames) =>
    (clauses owner resumeDemand).code
  have terminalFound : TerminalHandler effect activation (CoreGraphAdmission.Handler.declarationRows identity) captured :=
    .plain (.cleanup .here)
  have selected : CapturedClauseRows effect 0 captured.pack.scope.held captured (CoreGraphAdmission.Clause.rows identity) :=
    .selected terminalFound .ordinary
  have waiting : SourceAdmission.Pending [] actions [] phases world installations whole Context.nil
      .ordinary (whole.hints.returnMode .ordinary) := by
    simpa only [whole, captured, capture, armed, terminal, Context.hints, ReturnHints.append,
      SourceDependencyCapture.Scope.append, ReturnHints.returnMode, callerMode] using retained.pending
  refine ⟨SourceAdmission.Code.request cut guarded (fun _ => callback.pending) ownerBound budget
    selected terminalFound rfl waiting body, ?_⟩
  apply CodeChecked.request (cut := cut) (guarded := guarded) (callbacks := fun _ => callback.pending)
    (ownerBound := ownerBound) (cleanupBudget := budget) (selected := selected)
    (terminal := terminalFound) (requiredRights := rfl) (retained := waiting) (body := body)
  · intro _; exact callback.checked
  · simpa only [whole, captured, capture, armed, terminal, Context.hints, ReturnHints.append,
      SourceDependencyCapture.Scope.append, ReturnHints.returnMode, callerMode] using retained.checked
  · intro owner demand fresh absent
    exact (clauses owner demand).checked

noncomputable def laterOrdinary (tail : ReceiverTail identity context) :
    PendingProof actions phases world installations ((capture identity activation (CoreGraphAdmission.Writes.rows identity)).append context)
      Context.nil .ordinary .ordinary :=
  PendingProof.plain ((writeShape identity).proof (fun operation => by
    simp only [armed, terminal, Context.append, ReturnHints.append, SourceDependencyCapture.Scope.append,
      select, effect, reduceCtorEq, ↓reduceIte]
    rw [tail.lookup]; rfl)) (armedOrdinary (activation := activation) tail)

noncomputable def laterRequest (tail : ReceiverTail identity context) :
    SourceProof actions phases world installations (Rows.request (effect := effect) (operation := 0))
      ((capture identity activation (CoreGraphAdmission.Writes.rows identity)).append context) :=
  capturedRequest (CoreGraphAdmission.Writes.rows identity) (fun _ _ => (writeShape identity).within)
    (fun current => laterOrdinary (activation := activation) current) tail

noncomputable def laterSuffix (tail : ReceiverTail identity context) :
    SourceProof actions phases world installations (CoreGraphAdmission.Guarded.afterSecondRows identity)
      ((armed identity activation).append context) :=
  SourceProof.sequence (SourceProof.sequence pureProof (laterRequest (activation := activation) tail))
    ((writeShape identity).proof (fun operation => by
      simp only [armed, terminal, Context.append, ReturnHints.append, SourceDependencyCapture.Scope.append,
        select, effect, reduceCtorEq, ↓reduceIte]
      rw [tail.lookup]; rfl))

noncomputable def firstOrdinary (tail : ReceiverTail identity context) :
    PendingProof actions phases world installations
      ((capture identity activation (CoreGraphAdmission.Guarded.afterSecondRows identity)).append context)
      Context.nil .ordinary .ordinary :=
  PendingProof.plain (laterSuffix (activation := activation) tail) (armedOrdinary (activation := activation) tail)

noncomputable def firstRequest (tail : ReceiverTail identity context) :
    SourceProof actions phases world installations (Rows.request (effect := effect) (operation := 0))
      ((capture identity activation (CoreGraphAdmission.Guarded.afterSecondRows identity)).append context) :=
  capturedRequest (CoreGraphAdmission.Guarded.afterSecondRows identity)
    (fun _ _ => .sequence (.sequence .pure .request) (writeShape identity).within)
    (fun current => firstOrdinary (activation := activation) current) tail

noncomputable def guardedProof (tail : ReceiverTail identity context) :
    SourceProof actions phases world installations (CoreGraphAdmission.Guarded.rows identity)
      ((terminal identity activation).append context) := by
  let callback := (writeShape identity).proof (actions := actions) (phases := phases) (world := world)
    (installations := installations) (context := Context.normal ((terminal identity activation).append context))
    (fun operation => by
      simp only [terminal, Context.append, ReturnHints.append, SourceDependencyCapture.Scope.append,
        select, effect, reduceCtorEq, ↓reduceIte]
      rw [tail.lookup]; rfl)
  let body : SourceProof actions phases world installations (CoreGraphAdmission.Guarded.bodyRows identity)
      ((armed identity activation).append context) :=
    SourceProof.sequence (SourceProof.sequence pureProof (firstRequest (activation := activation) tail))
      (laterSuffix (activation := activation) tail)
  let cleanup : SourceProof actions phases world installations
      (.cleanup (needs := [.cell identity]) (CoreGraphAdmission.Setter.footprint identity)
        (CoreGraphAdmission.Writes.rows identity) (CoreGraphAdmission.Guarded.bodyRows identity))
      ((terminal identity activation).append context) :=
    ⟨.cleanup body.code callback.code,
      .cleanup (body := body.code) (callback := callback.code) body.checked callback.checked⟩
  exact SourceProof.sequence pureProof (SourceProof.sequence pureProof cleanup)

noncomputable def cellBodyProof (identity : Nat) :
    SourceProof actions phases world installations
      (.sequence .pure (CoreGraphAdmission.Spine.rows identity)) (Context.cell (identity := identity) .nil) := by
  let tail := ReceiverTail.plain (readShape identity) (ReceiverTail.cell (identity := identity))
  let bodies := fun activation (_fresh : activation ∉ installations) =>
    guardedProof (actions := actions) (phases := phases) (world := world)
      (installations := activation :: installations) (activation := activation) tail
  let handlerCode : SourceAdmission.Code [] actions [] phases world installations
      (CoreGraphAdmission.Handler.rows identity)
      (.plain (CoreExportedAdmission.applicationRows identity) (.cell (identity := identity) .nil)) :=
    .handler (fun activation fresh => (bodies activation fresh).code)
  have supported : (CoreGraphAdmission.Handler.declarationRows identity).resourceSupport ⊆
      SourceDependencyCapture.Scope.visibleResources
        (.plain (planDependencies (CoreExportedAdmission.applicationPlan identity)) (.cell identity .nil)) ++ ([] : List Nat) := by
    simp [CoreGraphAdmission.Handler.declarationRows, ClauseRows.resourceSupport,
      SourceDependencyCapture.Scope.visibleResources]
  have handlerChecked : CodeChecked [] [] handlerCode := by
    apply CodeChecked.handler (body := fun activation fresh => (bodies activation fresh).code) supported
    intro activation fresh
    exact (bodies activation fresh).checked
  exact SourceProof.sequence pureProof (SourceProof.sequence pureProof (SourceProof.sequence pureProof
    (SourceProof.sequence ⟨handlerCode, handlerChecked⟩ ((readShape identity).proof (fun _ => by simp [select])))))

noncomputable def rootProof :
    SourceProof InitialAdmission.actions (OwnerPhaseTransitions.available []) [] [] CoreGraphAdmission.Main.rootRows Context.nil := by
  let bodies := fun identity (_fresh : identity ∉ ([] : List Nat)) =>
    cellBodyProof (actions := InitialAdmission.actions) (phases := OwnerPhaseTransitions.available [])
      (world := [identity]) (installations := []) identity
  let code : SourceAdmission.Code [] InitialAdmission.actions [] (OwnerPhaseTransitions.available []) [] []
      (.resource (fun identity => Rows.sequence Rows.pure (CoreGraphAdmission.Spine.rows identity))) Context.nil :=
    .resource (fun identity fresh => (bodies identity fresh).code)
  have checked : CodeChecked [] [] code := by
    apply CodeChecked.resource (body := fun identity fresh => (bodies identity fresh).code)
    intro identity fresh
    exact (bodies identity fresh).checked
  exact SourceProof.sequence pureProof (SourceProof.sequence pureProof (SourceProof.sequence pureProof
    (SourceProof.sequence pureProof (SourceProof.sequence pureProof ⟨code, checked⟩))))

theorem armedAccounting (tail : ReceiverTail identity context) :
    Accounting.Wait world installations ((armed identity activation).append context) .ordinary tail.root := by
  apply Accounting.Wait.cleanup
  apply BuiltinRows.accounting (writeShape identity)
  · intro operation
    simp only [terminal, Context.append, Context.callback, ReturnHints.append,
      SourceDependencyCapture.Scope.append, select, effect, reduceCtorEq, ↓reduceIte]
    rw [tail.lookup]; rfl
  · exact .normal (.handler tail.accounting)

theorem captureAccountingUnwind (tail : ReceiverTail identity context) (rows : Rows checking) :
    Accounting.Wait world installations ((capture identity activation rows).append (Context.closing context))
      .unwind tail.root := by
  apply Accounting.Wait.skipped
  apply Accounting.Wait.cleanup
  apply BuiltinRows.accounting (writeShape identity)
  · intro operation
    simp only [terminal, Context.append, Context.callback, ReturnHints.append,
      SourceDependencyCapture.Scope.append, select, effect, reduceCtorEq, ↓reduceIte]
    rw [tail.lookup]; rfl
  · exact .unwinding (.handler (.closing tail.accounting))

theorem laterAccounting (tail : ReceiverTail identity context) :
    Accounting.Wait world installations
      ((capture identity activation (CoreGraphAdmission.Writes.rows identity)).append context) .ordinary tail.root :=
  .plain ((writeShape identity).accounting (fun operation => by
    simp only [armed, terminal, Context.append, ReturnHints.append, SourceDependencyCapture.Scope.append,
      select, effect, reduceCtorEq, ↓reduceIte]
    rw [tail.lookup]; rfl) (armedAccounting (activation := activation) tail))

def capturedClauseRoot (interpret : Requirements [] → Requirements []) (owner : Nat) (root : Requirements []) : Requirements [owner] :=
  .choice (.sequence (.retire owner) (interpret (.sequence (.spent owner) root))) (invocationRoot owner root) (.refl [owner])
def capturedRoot (interpret : Requirements [] → Requirements []) (root : Requirements []) : Requirements [] :=
  .choice (.sequence empty (interpret (.sequence empty root))) (.sequence empty (.sequence empty root)) (.refl [])

theorem capturedAccounting {capturedDependencies : Dependencies}
    {checking : SourcePlanSignatures.Signature capturedDependencies} (rows : Rows checking)
    (interpret : Requirements [] → Requirements [])
    (binding : ∀ {owner phase localRoot outerRoot}, LocalOwner owner phase localRoot outerRoot phase →
      LocalOwner owner phase (interpret localRoot) (interpret outerRoot) phase)
    (ordinary : ∀ {world installations : List Nat} {scope : SourceDependencyCapture.Scope}
      {hints : ReturnHints scope} {receiving : Context hints},
      (tail : ReceiverTail identity receiving) →
      Accounting.Wait world installations ((capture identity activation rows).append receiving) .ordinary (interpret tail.root))
    (tail : ReceiverTail identity context) :
    Accounting.Run world installations (Rows.request (effect := effect) (operation := 0))
      ((capture identity activation rows).append context) (capturedRoot interpret tail.root) := by
  have clauseAccounting (owner : Nat) (resumeDemand : List Nat) :
      Accounting.Run world installations (CoreGraphAdmission.Clause.rows identity owner)
        (.live (owner := owner) (resumeDemand := resumeDemand) (capture identity activation rows) context)
        (capturedClauseRoot interpret owner tail.root) := by
    apply Accounting.Run.sequence
    apply Accounting.Run.pure
    apply Accounting.Wait.plain
    apply Accounting.Run.choice
    · apply Accounting.Run.sequence
      apply Accounting.Run.sequence
      apply Accounting.Run.pure
      apply Accounting.Wait.plain
      apply Accounting.Run.resume (front := .plain (CoreGraphAdmission.Writes.rows identity) .nil)
        (captured := capture identity activation rows) (tail := context)
      · exact .plain .hit
      · simpa only [Context.append, ReturnHints.append, SourceDependencyCapture.Scope.append, ReceiverTail.root]
          using ordinary (world := world) (installations := installations)
            (ReceiverTail.plain (writeShape identity) (ReceiverTail.spent (owner := owner) tail))
    · apply Accounting.Run.dispose (front := .nil) (captured := capture identity activation rows) (tail := context)
      · exact .hit
      · simpa only [Context.append, ReturnHints.append, SourceDependencyCapture.Scope.append, ReceiverTail.root]
          using captureAccountingUnwind (world := world) (installations := installations) (activation := activation)
            (ReceiverTail.spent (owner := owner) tail) rows
  apply Accounting.Run.request
    (captured := capture identity activation rows) (tail := context)
    (contract := ⟨true, some (CoreGraphAdmission.Setter.footprint identity), none⟩)
    (modes := (some (fun owner => planDependencies (CoreGraphAdmission.Clause.plan identity owner)), none))
    (bodyRows := CoreGraphAdmission.Clause.rows identity)
    (localRoot := fun owner _ => capturedClauseRoot interpret owner tail.root)
  · rfl
  · exact .selected (.plain (.cleanup .here)) .ordinary
  · intro owner demand absent
    exact clauseAccounting owner demand
  · intro owner demand absent
    apply LocalOwner.choice
    · apply LocalOwner.sequence .retireSelf
      apply binding
      apply LocalOwner.sequence .spentSelf
      apply tail.localOwner
      intro member; apply absent
      simpa only [Context.append_ticketNames, Context.ticketNames, capture, armed, terminal, List.nil_append] using member
    · apply LocalOwner.sequence .retireSelf
      apply LocalOwner.sequence .spentSelf
      apply tail.localOwner
      intro member; apply absent
      simpa only [Context.append_ticketNames, Context.ticketNames, capture, armed, terminal, List.nil_append] using member

theorem laterRequestAccounting (tail : ReceiverTail identity context) :
    Accounting.Run world installations (Rows.request (effect := effect) (operation := 0))
      ((capture identity activation (CoreGraphAdmission.Writes.rows identity)).append context) (consumingRoot tail.root) :=
  capturedAccounting (CoreGraphAdmission.Writes.rows identity) id (fun proof => proof)
    (fun current => laterAccounting (activation := activation) current) tail

theorem laterSuffixAccounting (tail : ReceiverTail identity context) :
    Accounting.Run world installations (CoreGraphAdmission.Guarded.afterSecondRows identity)
      ((armed identity activation).append context) (consumingRoot tail.root) :=
  .sequence (.sequence (.pure (.plain (laterRequestAccounting (activation := activation) tail))))

theorem firstAccounting (tail : ReceiverTail identity context) :
    Accounting.Wait world installations
      ((capture identity activation (CoreGraphAdmission.Guarded.afterSecondRows identity)).append context)
      .ordinary (consumingRoot tail.root) := .plain (laterSuffixAccounting (activation := activation) tail)

theorem firstRequestAccounting (tail : ReceiverTail identity context) :
    Accounting.Run world installations (Rows.request (effect := effect) (operation := 0))
      ((capture identity activation (CoreGraphAdmission.Guarded.afterSecondRows identity)).append context) (firstRoot tail.root) :=
  capturedAccounting (CoreGraphAdmission.Guarded.afterSecondRows identity) consumingRoot consumingRootBinding
    (fun current => firstAccounting (activation := activation) current) tail

theorem guardedAccounting (tail : ReceiverTail identity context) :
    Accounting.Run world installations (CoreGraphAdmission.Guarded.rows identity)
      ((terminal identity activation).append context) (firstRoot tail.root) :=
  .sequence (.pure (.plain (.sequence (.pure (.plain (.installCleanup
    (.sequence (.sequence (.pure (.plain (firstRequestAccounting (activation := activation) tail)))))))))))

theorem cellBodyAccounting :
    Accounting.Run world installations (.sequence .pure (CoreGraphAdmission.Spine.rows identity))
      (Context.cell (identity := identity) .nil) (firstRoot empty) :=
  .sequence (.pure (.plain (.sequence (.pure (.plain (.sequence (.pure (.plain
    (.sequence (.installHandler (fun activation _ =>
      guardedAccounting (activation := activation) (ReceiverTail.plain (readShape identity) (ReceiverTail.cell (identity := identity))))))))))))))

theorem rootAccounting : Accounting.Run [] [] CoreGraphAdmission.Main.rootRows Context.nil (firstRoot empty) :=
  .sequence (.pure (.plain (.sequence (.pure (.plain (.sequence (.pure (.plain
    (.sequence (.pure (.plain (.sequence (.pure (.plain (.installResource (fun _ _ => cellBodyAccounting))))))))))))))))

/-- Every field concerns the exact exported graph root and its authenticated
plans. No execution, successor or external source certificate is an input. -/
noncomputable def program : Program operations policy ports [] [] CoreGraphAdmission.Main.root :=
  { result := .integer, resultRows := .integer,
    dependencies := _, plan := CoreGraphAdmission.Main.rootPlan, rows := CoreGraphAdmission.Main.rootRows,
    demand := [], requirements := CoreGraphAdmission.Main.rootRequirements, source := source,
    authenticated := authenticated, certified := certified,
    certificate := rootProof.code, resourceChecked := rootProof.checked,
    rootDemand := [], root := firstRoot empty, interpreted := rootAccounting,
    annotated := firstRoot empty, annotation := .original,
    rootRow := [], checked := CoreKernelProgram.rootChecked, bounded := List.nil_subset _,
    resources := by decide, builtinSignatures := builtinSignatures }

theorem closed_initial_state (tables : CallableProtectionFrames.Tables)
    (families : SourceDependencyFrames.Families) (required : SourceContextualRechecking.Required) :
    InstallationState operations policy InitialAdmission.contracts tables families required [] InitialAdmission.annotations
      [] [] [] [] [] [] [] ports InitialAdmission.owners InitialAdmission.emptyRows
      (.value .integer) (.value .integer) (initialRun CoreGraphAdmission.Main.root) :=
  program.closed_initial_state tables families required

/-- The admitted configuration is the fixed runtime prefix's initial target.
This equality does not authenticate that prefix's subsequent annotations. -/
theorem initial_target : (initialRun CoreGraphAdmission.Main.root).execution.machine = .eval CoreInitialPrefix.rootTarget := rfl

open InstallationSupport.Preservation

theorem finite_prefix (tables : CallableProtectionFrames.Tables)
    (families : SourceDependencyFrames.Families) (required : SourceContextualRechecking.Required) (fuel : Nat) :
    ∃ count final,
      RawTrace (initialRun CoreGraphAdmission.Main.root).execution count final.run.execution ∧
      Valid policy [] [] [] ports InitialAdmission.emptyRows .integer .integer final ∧
      count ≤ fuel ∧ (count = fuel ∨ Terminal final) :=
  InstallationSupport.Preservation.InitialAdmission.Program.finite_prefix program tables families required fuel

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram.certified
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram.source
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram.authenticated
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram.actualRoot

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram.BuiltinRows.proof
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram.BuiltinRows.accounting
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram.ReceiverTail.pending
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram.ReceiverTail.accounting
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram.consumingClause
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram.capturedRequest
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram.laterRequest
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram.firstRequest
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram.guardedProof
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram.cellBodyProof
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram.rootProof

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram.capturedAccounting
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram.firstRequestAccounting
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram.cellBodyAccounting
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram.rootAccounting

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram.program
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram.closed_initial_state
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram.initial_target
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreGraphProgram.finite_prefix
