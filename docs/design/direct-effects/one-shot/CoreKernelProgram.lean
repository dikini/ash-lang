import CoreKernelAdmission
import SourceScheduledM4

/-! Structural admission for the exact normalized integration fixture. The
receiving-tail description below retains its actual read, write and spent frames;
it contains no execution or future-success premise. -/
namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreKernelProgram
open ScopedExpressions ProtectionContracts
open SourceDependencyAnnotations (Dependencies)
open SourcePlanSignatures (Signature signature)
open SourceDependencyChecks.Lexical (ReturnHints)
open OwnerPhaseTransitions (Phases)
open LexicalUnwind (UseMode)
open InstallationSupport
open CoreInitialExample CoreKernelAdmission

structure SourceProof (actions : Syntax.UsageTickets) (phases : Phases)
    (world installations : List Nat) {checking : Signature dependencies}
    (rows : Rows checking) {hints : ReturnHints scope} (context : Context hints) : Type where
  code : SourceAdmission.Code [] actions [] phases world installations rows context
  checked : CodeChecked [] [] code

structure PendingProof (actions : Syntax.UsageTickets) (phases : Phases)
    (world installations : List Nat) {hints : ReturnHints scope} {outsideHints : ReturnHints outsideScope}
    (context : Context hints) (outside : Context outsideHints) (input output : UseMode) : Type where
  pending : SourceAdmission.Pending [] actions [] phases world installations context outside input output
  checked : PendingChecked [] [] pending

variable {actions : Syntax.UsageTickets} {phases : Phases} {world installations : List Nat}

def builtinProof (found : select (.cell identity) operation context = some (.builtin identity)) :
    SourceProof actions phases world installations
      (Rows.request (effect := .cell identity) (operation := operation)) context :=
  ⟨.builtin (identity := identity) found, .builtin (identity := identity) (found := found)⟩

def operationRows (identity operation : Nat) : Rows
    (.sequence .pure (.request (effect := .cell identity) (operation := operation))) :=
  .sequence .pure .request

def operationProof (found : select (.cell identity) operation context = some (.builtin identity)) :
    SourceProof actions phases world installations (operationRows identity operation) context :=
  let primitive := builtinProof (actions := actions) (phases := phases)
    (world := world) (installations := installations) found
  ⟨.sequence .pure primitive.code, .sequence .pure primitive.checked⟩

/-- The finite receiving tails used by this fixture: a cell activation, the final
read, and the actual post-resume writes separated by spent owner markers. -/
inductive CellTail (identity : Nat) : {scope : SourceDependencyCapture.Scope} →
    {hints : ReturnHints scope} → Context hints → Type where
  | cell : CellTail identity (Context.cell (identity := identity) .nil)
  | plain (tail : CellTail identity context) :
      CellTail identity (.plain (operationRows identity operation) context)
  | spent (tail : CellTail identity context) :
      CellTail identity (.spent (owner := owner) context)

theorem CellTail.lookup (tail : CellTail identity context) :
    select (.cell identity) operation context = some (.builtin identity) := by
  induction tail with
  | cell => simp [select]
  | plain tail ih => simp only [select, ih, Option.map_some, Selection.prepend]
  | spent tail ih => simp only [select, ih, Option.map_some, Selection.prepend]

noncomputable def CellTail.pending (tail : CellTail identity context) :
    PendingProof actions phases world installations context Context.nil .ordinary .ordinary := by
  induction tail with
  | cell => exact ⟨.cell .nil, .cell .nil⟩
  | plain tail ih =>
      rename_i restScope restHints restContext operation
      let expression := operationProof (actions := actions) (phases := phases)
        (world := world) (installations := installations) (operation := operation) tail.lookup
      exact ⟨.plain (expression.code.reindex_context restContext.append_nil_pack.symm) ih.pending,
        .plain (expression.checked.reindex_context restContext.append_nil_pack.symm) ih.checked⟩
  | spent tail ih => exact ⟨.spent ih.pending, .spent ih.checked⟩

def PendingProof.plain (body : SourceProof actions phases world installations rows context)
    (rest : PendingProof actions phases world installations context Context.nil .ordinary .ordinary) :
    PendingProof actions phases world installations (.plain rows context) Context.nil .ordinary .ordinary :=
  ⟨.plain (body.code.reindex_context context.append_nil_pack.symm) rest.pending,
    .plain (body.checked.reindex_context context.append_nil_pack.symm) rest.checked⟩

def pureProof : SourceProof actions phases world installations Rows.pure context :=
  ⟨.pure, .pure⟩

def SourceProof.sequence
    (first : SourceProof actions phases world installations firstRows (.plain secondRows context))
    (second : SourceProof actions phases world installations secondRows context) :
    SourceProof actions phases world installations (.sequence firstRows secondRows) context :=
  ⟨.sequence first.code second.code,
    .sequence (first := first.code) (second := second.code) first.checked second.checked⟩

def terminal (identity activation : Nat) :=
  Context.handler (effect := effect) (table := table identity) activation (declarationRows identity) .nil

def laterCapture (identity activation : Nat) :=
  Context.plain (operationRows identity 1)
    (Context.cleanup (needs := [.cell identity]) (callbackFootprint identity) (operationRows identity 1)
      (terminal identity activation))

noncomputable def armedOrdinary (tail : CellTail identity context) :
    PendingProof actions phases world installations ((Context.cleanup (needs := [.cell identity]) (callbackFootprint identity)
        (operationRows identity 1) (terminal identity activation)).append context)
      Context.nil .ordinary .ordinary := by
  have cellFound := tail.lookup (operation := 1)
  let receiving := (terminal identity activation).append context
  let waiting := tail.pending (actions := actions) (phases := phases)
    (world := world) (installations := installations)
  let handled : PendingProof actions phases world installations receiving Context.nil .ordinary .ordinary :=
    ⟨.handler waiting.pending, .handler waiting.checked⟩
  let callback := operationProof (identity := identity) (actions := actions) (phases := phases) (world := world)
    (installations := installations) (operation := 1) (context := Context.normal receiving)
    (by
      simp only [receiving, terminal, Context.append, ReturnHints.append,
        SourceDependencyCapture.Scope.append, select, effect, reduceCtorEq, ↓reduceIte]
      rw [cellFound]
      rfl)
  let armed : PendingProof actions phases world installations
      (Context.cleanup (needs := [.cell identity]) (callbackFootprint identity) (operationRows identity 1) receiving)
      Context.nil .ordinary .ordinary :=
    ⟨.cleanup (callback.code.reindex_context (Context.normal receiving).append_nil_pack.symm) handled.pending,
      .cleanup (callback.checked.reindex_context (Context.normal receiving).append_nil_pack.symm) handled.checked⟩
  exact armed

noncomputable def laterOrdinary (tail : CellTail identity context) :
    PendingProof actions phases world installations ((laterCapture identity activation).append context)
      Context.nil .ordinary .ordinary := by
  have found := tail.lookup (operation := 1)
  let armed := armedOrdinary (actions := actions) (phases := phases) (world := world)
    (installations := installations) (activation := activation) tail
  apply PendingProof.plain (rest := armed)
  exact operationProof (identity := identity) (operation := 1) (by
    simp only [terminal, Context.append, ReturnHints.append, SourceDependencyCapture.Scope.append,
      select, effect, reduceCtorEq, ↓reduceIte]
    rw [found]
    rfl)

noncomputable def laterUnwind (tail : CellTail identity context) :
    PendingProof actions phases world installations (laterCapture identity activation)
      (Context.closing context) .unwind .unwind := by
  have cellFound := tail.lookup (operation := 1)
  let receiving := (terminal identity activation).append (Context.closing context)
  let callback := operationProof (identity := identity) (actions := actions) (phases := phases) (world := world)
    (installations := installations) (operation := 1) (context := Context.unwinding receiving)
    (by
      simp only [receiving, terminal, Context.append, ReturnHints.append,
        SourceDependencyCapture.Scope.append, select, effect, reduceCtorEq, ↓reduceIte]
      rw [cellFound]
      rfl)
  exact ⟨.skipped (.cleanup callback.code (.handler .nil)),
    .skipped (.cleanup callback.checked (.handler .nil))⟩

theorem CellTail.ordinaryMode (tail : CellTail identity context) :
    context.hints.returnMode .ordinary = .ordinary := by
  induction tail <;> simp_all [Context.hints, ReturnHints.returnMode]

noncomputable def consumingClause (tail : CellTail identity context) (captured : Context capturedHints)
    (capturedMode : captured.hints.returnMode .ordinary = .ordinary)
    (unprotected : captured.pack.scope.held = false)
    (ordinary : ∀ {actions : Syntax.UsageTickets} {phases : Phases} {world installations : List Nat}
      {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope} {receiving : Context hints},
      CellTail identity receiving → PendingProof actions phases world installations
        (captured.append receiving) Context.nil .ordinary .ordinary)
    (unwind : ∀ {actions : Syntax.UsageTickets} {phases : Phases} {world installations : List Nat}
      {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope} {receiving : Context hints},
      CellTail identity receiving → PendingProof actions phases world installations
        captured (Context.closing receiving) .unwind .unwind)
    (owner : Nat) (resumeDemand : List Nat) :
    SourceProof (actions.insert owner ⟨true, true⟩) (OwnerPhaseTransitions.introduce phases owner)
      world installations
      (.sequence .pure (.choice
        (.sequence (.sequence .pure (.invoke (key := ⟨owner, .resume⟩))) (operationRows identity 1))
        (.invoke (key := ⟨owner, .dispose⟩))))
      (.live (owner := owner) (resumeDemand := resumeDemand) captured context) := by
  have callerMode := tail.ordinaryMode
  dsimp only [Context.hints] at callerMode
  have savedMode := capturedMode
  dsimp only [Context.hints] at savedMode
  let nextActions := actions.insert owner ⟨true, true⟩
  let nextPhases := OwnerPhaseTransitions.introduce phases owner
  let resumedTail := CellTail.plain (operation := 1) (CellTail.spent (owner := owner) tail)
  let restored := ordinary (actions := nextActions) (phases := OwnerPhaseTransitions.spend nextPhases owner)
    (world := world) (installations := installations) resumedTail
  let caller := CellTail.pending (actions := nextActions) (phases := OwnerPhaseTransitions.spend nextPhases owner)
    (world := world) (installations := installations) (CellTail.spent (owner := owner) tail)
  let abandoned := unwind (actions := nextActions) (phases := OwnerPhaseTransitions.spend nextPhases owner)
    (world := world) (installations := installations) (CellTail.spent (owner := owner) tail)
  let resumes : SourceAdmission.Code [] nextActions [] nextPhases world installations
      (.invoke (key := ⟨owner, .resume⟩))
      (.plain (operationRows identity 1)
        (.live (owner := owner) (resumeDemand := resumeDemand) captured context)) := by
    apply SourceAdmission.Code.resume (front := .plain (operationRows identity 1) .nil)
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
  have found := tail.lookup (operation := 1)
  let writes := operationProof (actions := nextActions) (phases := nextPhases) (world := world)
    (installations := installations) (identity := identity) (operation := 1)
    (context := Context.live (owner := owner) (resumeDemand := resumeDemand) captured context)
    (by change (select (.cell identity) 1 context).map _ = _; rw [found]; rfl)
  refine ⟨.sequence .pure (.choice (.sequence (.sequence .pure resumes) writes.code) disposes), ?_⟩
  apply CodeChecked.sequence (first := .pure) (second := .choice (.sequence (.sequence .pure resumes) writes.code) disposes) .pure
  apply CodeChecked.choice (first := .sequence (.sequence .pure resumes) writes.code) (second := disposes)
  · apply CodeChecked.sequence
    · apply CodeChecked.sequence (first := .pure) (second := resumes) .pure
      apply CodeChecked.resume (front := .plain (operationRows identity 1) .nil)
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

noncomputable def laterClause {activation : Nat} (tail : CellTail identity context) (owner : Nat) (resumeDemand : List Nat) :
    SourceProof (actions.insert owner ⟨true, true⟩) (OwnerPhaseTransitions.introduce phases owner)
      world installations
      (.sequence .pure (.choice
        (.sequence (.sequence .pure (.invoke (key := ⟨owner, .resume⟩))) (operationRows identity 1))
        (.invoke (key := ⟨owner, .dispose⟩))))
      (.live (owner := owner) (resumeDemand := resumeDemand) (laterCapture identity activation) context) :=
  consumingClause (actions := actions) (phases := phases) (world := world) (installations := installations)
    tail (laterCapture identity activation) rfl rfl
    (fun current => laterOrdinary (activation := activation) current)
    (fun current => laterUnwind (activation := activation) current) owner resumeDemand

theorem CellTail.exportCell (tail : CellTail identity context) :
    OwnerSource.exportAt context.context phases [⟨.cell identity, operation, held⟩] = some [] := by
  induction tail with
  | cell =>
      simp [OwnerSource.exportAt, Context.context, OwnerPhaseTransitions.project,
        ProtectionResiduals.residualize, ProtectionResiduals.throughLayer,
        ProtectionResiduals.demandThrough, ProtectionResiduals.merge]
  | plain tail ih =>
      simpa [OwnerSource.exportAt, Context.context, OwnerPhaseTransitions.project,
        ProtectionResiduals.residualize, ProtectionResiduals.throughLayer,
        ProtectionResiduals.demandThrough, ProtectionResiduals.merge] using ih
  | spent tail ih => exact ih

def laterMetadata (identity activation : Nat) :
    CleanupHints.Metadata (laterCapture identity activation).pack.scope :=
  CleanupHints.Metadata.plain
    (CleanupHints.Metadata.cleanup (callbackFootprint identity)
      (CleanupHints.Metadata.handler (effect := effect) (table := table identity)
        (families := [(0, some (clauseDependencies identity), none)]) activation .nil))

theorem laterBudgetCheck (tail : CellTail identity context) :
    (laterMetadata identity activation).check context.context phases [] = true ∧
      (laterMetadata identity activation).check (.ordinary (.barrier true) :: context.context) phases [] = true := by
  have exported := tail.exportCell (phases := phases) (operation := 1) (held := true)
  change ProtectionResiduals.residualize (OwnerPhaseTransitions.project context.context phases)
    [⟨.cell identity, 1, true⟩] = some [] at exported
  constructor <;>
    simp [laterMetadata, CleanupHints.Metadata.check, CleanupHints.Metadata.closing,
      CleanupHints.Metadata.context, RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel,
      OwnerSource.exportAt, OwnerPhaseTransitions.project, OwnerPhaseTransitions.spendAll,
      callbackFootprint, qualify, ProtectionResiduals.residualize, ProtectionResiduals.throughLayer,
      ProtectionResiduals.demandThrough, ProtectionResiduals.merge, ProtectionResiduals.residual_empty, effect, exported]

def fixtureClauseRows (identity owner : Nat) : Rows (signature (clausePlan identity owner)) :=
  .sequence .pure (.choice (.sequence (.sequence .pure .invoke) (operationRows identity 1)) .invoke)

noncomputable def laterRequest (tail : CellTail identity context) :
    SourceProof actions phases world installations (Rows.request (effect := effect) (operation := 0))
      ((laterCapture identity activation).append context) := by
  have callerMode := tail.ordinaryMode
  dsimp only [Context.hints] at callerMode
  let captured := laterCapture identity activation
  let whole := captured.append context
  have cut : Cut effect 0 whole captured context (ClauseContract.mk true (some (callbackFootprint identity)) none)
      (some (clauseDependencies identity), none) := by rfl
  have guarded : SourceDependencyChecks.Lexical.Capture whole.pack.scope effect 0 :=
    .handler rfl rfl rfl rfl
  have ownerBound : (ClauseContract.mk true (some (callbackFootprint identity)) none).dispose = true →
      SourceDependencyOwners.PendingWithin world (SourceDependencyOwners.owners captured.pack.scope) captured.pack.scope := by
    intro _
    exact .plain (.sequence .pure .request) (.cleanup (.handler .nil))
  have budget : RequestBudget [] phases effect 0 whole := by
    unfold RequestBudget
    rw [cut]
    intro _
    exact ⟨laterMetadata identity activation, rfl, (laterBudgetCheck tail).1, (laterBudgetCheck tail).2⟩
  let callback := laterUnwind (actions := actions) (phases := phases) (world := world)
    (installations := installations) (activation := activation) tail
  let retained := laterOrdinary (actions := actions) (phases := phases) (world := world)
    (installations := installations) (activation := activation) tail
  let body := fun owner resumeDemand (_fresh : actions owner = none) (_absent : owner ∉ whole.ticketNames) =>
    (laterClause (actions := actions) (phases := phases) (world := world)
      (installations := installations) (activation := activation) tail owner resumeDemand).code
  have terminalFound : TerminalHandler effect activation (declarationRows identity) captured :=
    .plain (.cleanup .here)
  have selected : CapturedClauseRows effect 0 captured.pack.scope.held captured (fixtureClauseRows identity) :=
    .selected terminalFound .ordinary
  have waiting : SourceAdmission.Pending [] actions [] phases world installations whole Context.nil
      .ordinary (whole.hints.returnMode .ordinary) := by
    simpa only [whole, captured, laterCapture, terminal, Context.hints, ReturnHints.append,
      SourceDependencyCapture.Scope.append, ReturnHints.returnMode, callerMode] using retained.pending
  refine ⟨SourceAdmission.Code.request cut guarded (fun _ => callback.pending) ownerBound budget
    selected terminalFound rfl waiting body, ?_⟩
  apply CodeChecked.request (cut := cut) (guarded := guarded) (callbacks := fun _ => callback.pending)
    (ownerBound := ownerBound) (cleanupBudget := budget) (selected := selected)
    (terminal := terminalFound) (requiredRights := rfl) (retained := waiting) (body := body)
  · intro _; exact callback.checked
  · simpa only [whole, captured, laterCapture, terminal, Context.hints, ReturnHints.append,
      SourceDependencyCapture.Scope.append, ReturnHints.returnMode, callerMode] using retained.checked
  · intro owner demand fresh absent
    exact (laterClause (actions := actions) (phases := phases) (world := world)
      (installations := installations) (activation := activation) tail owner demand).checked

def suffixRows (identity : Nat) : Rows
    (.sequence (.sequence .pure (.request (effect := effect) (operation := 0)))
      (.sequence .pure (.request (effect := .cell identity) (operation := 1)))) :=
  .sequence (.sequence .pure .request) (operationRows identity 1)

def firstCapture (identity activation : Nat) :=
  Context.plain (suffixRows identity)
    (Context.cleanup (needs := [.cell identity]) (callbackFootprint identity) (operationRows identity 1)
      (terminal identity activation))

noncomputable def laterSuffix (tail : CellTail identity context) :
    SourceProof actions phases world installations (suffixRows identity)
      ((Context.cleanup (needs := [.cell identity]) (callbackFootprint identity)
        (operationRows identity 1) (terminal identity activation)).append context) := by
  have found := tail.lookup (operation := 1)
  let writes := operationProof (actions := actions) (phases := phases) (world := world)
    (installations := installations) (identity := identity) (operation := 1)
    (context := (Context.cleanup (needs := [.cell identity]) (callbackFootprint identity)
      (operationRows identity 1) (terminal identity activation)).append context)
    (by
      simp only [terminal, Context.append, ReturnHints.append, SourceDependencyCapture.Scope.append,
        select, effect, reduceCtorEq, ↓reduceIte]
      rw [found]
      rfl)
  exact SourceProof.sequence (SourceProof.sequence pureProof (laterRequest (activation := activation) tail)) writes

noncomputable def firstOrdinary (tail : CellTail identity context) :
    PendingProof actions phases world installations ((firstCapture identity activation).append context)
      Context.nil .ordinary .ordinary :=
  PendingProof.plain (laterSuffix (activation := activation) tail) (armedOrdinary (activation := activation) tail)

noncomputable def firstUnwind (tail : CellTail identity context) :
    PendingProof actions phases world installations (firstCapture identity activation)
      (Context.closing context) .unwind .unwind := by
  have found := tail.lookup (operation := 1)
  let receiving := (terminal identity activation).append (Context.closing context)
  let callback := operationProof (identity := identity) (actions := actions) (phases := phases) (world := world)
    (installations := installations) (operation := 1) (context := Context.unwinding receiving)
    (by
      simp only [receiving, terminal, Context.append, ReturnHints.append,
        SourceDependencyCapture.Scope.append, select, effect, reduceCtorEq, ↓reduceIte]
      rw [found]
      rfl)
  exact ⟨.skipped (.cleanup callback.code (.handler .nil)),
    .skipped (.cleanup callback.checked (.handler .nil))⟩

noncomputable def firstClause (tail : CellTail identity context) (owner : Nat) (resumeDemand : List Nat) :
    SourceProof (actions.insert owner ⟨true, true⟩) (OwnerPhaseTransitions.introduce phases owner)
      world installations (fixtureClauseRows identity owner)
      (.live (owner := owner) (resumeDemand := resumeDemand) (firstCapture identity activation) context) :=
  consumingClause (actions := actions) (phases := phases) (world := world) (installations := installations)
    tail (firstCapture identity activation) rfl rfl
    (fun current => firstOrdinary (activation := activation) current)
    (fun current => firstUnwind (activation := activation) current) owner resumeDemand

def firstMetadata (identity activation : Nat) :
    CleanupHints.Metadata (firstCapture identity activation).pack.scope :=
  .plain (.cleanup (callbackFootprint identity) (.handler activation .nil))

theorem firstBudgetCheck (tail : CellTail identity context) :
    (firstMetadata identity activation).check context.context phases [] = true ∧
      (firstMetadata identity activation).check (.ordinary (.barrier true) :: context.context) phases [] = true :=
  laterBudgetCheck (activation := activation) (phases := phases) tail

noncomputable def firstRequest (tail : CellTail identity context) :
    SourceProof actions phases world installations (Rows.request (effect := effect) (operation := 0))
      ((firstCapture identity activation).append context) := by
  have callerMode := tail.ordinaryMode
  dsimp only [Context.hints] at callerMode
  let captured := firstCapture identity activation
  let whole := captured.append context
  have cut : Cut effect 0 whole captured context (ClauseContract.mk true (some (callbackFootprint identity)) none)
      (some (clauseDependencies identity), none) := by rfl
  have guarded : SourceDependencyChecks.Lexical.Capture whole.pack.scope effect 0 :=
    .handler rfl rfl rfl rfl
  have ownerBound : (ClauseContract.mk true (some (callbackFootprint identity)) none).dispose = true →
      SourceDependencyOwners.PendingWithin world (SourceDependencyOwners.owners captured.pack.scope) captured.pack.scope := by
    intro _
    exact .plain (.sequence (.sequence .pure .request) (.sequence .pure .request)) (.cleanup (.handler .nil))
  have budget : RequestBudget [] phases effect 0 whole := by
    unfold RequestBudget
    rw [cut]
    intro _
    exact ⟨firstMetadata identity activation, rfl, (firstBudgetCheck tail).1, (firstBudgetCheck tail).2⟩
  let callback := firstUnwind (actions := actions) (phases := phases) (world := world)
    (installations := installations) (activation := activation) tail
  let retained := firstOrdinary (actions := actions) (phases := phases) (world := world)
    (installations := installations) (activation := activation) tail
  let body := fun owner resumeDemand (_fresh : actions owner = none) (_absent : owner ∉ whole.ticketNames) =>
    (firstClause (actions := actions) (phases := phases) (world := world)
      (installations := installations) (activation := activation) tail owner resumeDemand).code
  have terminalFound : TerminalHandler effect activation (declarationRows identity) captured :=
    .plain (.cleanup .here)
  have selected : CapturedClauseRows effect 0 captured.pack.scope.held captured (fixtureClauseRows identity) :=
    .selected terminalFound .ordinary
  have waiting : SourceAdmission.Pending [] actions [] phases world installations whole Context.nil
      .ordinary (whole.hints.returnMode .ordinary) := by
    simpa only [whole, captured, firstCapture, terminal, Context.hints, ReturnHints.append,
      SourceDependencyCapture.Scope.append, ReturnHints.returnMode, callerMode] using retained.pending
  refine ⟨SourceAdmission.Code.request cut guarded (fun _ => callback.pending) ownerBound budget
    selected terminalFound rfl waiting body, ?_⟩
  apply CodeChecked.request (cut := cut) (guarded := guarded) (callbacks := fun _ => callback.pending)
    (ownerBound := ownerBound) (cleanupBudget := budget) (selected := selected)
    (terminal := terminalFound) (requiredRights := rfl) (retained := waiting) (body := body)
  · intro _; exact callback.checked
  · simpa only [whole, captured, firstCapture, terminal, Context.hints, ReturnHints.append,
      SourceDependencyCapture.Scope.append, ReturnHints.returnMode, callerMode] using retained.checked
  · intro owner demand fresh absent
    exact (firstClause (actions := actions) (phases := phases) (world := world)
      (installations := installations) (activation := activation) tail owner demand).checked

noncomputable def protectedProof (tail : CellTail identity context) :
    SourceProof actions phases world installations
      (.sequence (.sequence .pure (.request (effect := effect) (operation := 0))) (suffixRows identity))
      ((Context.cleanup (needs := [.cell identity]) (callbackFootprint identity)
        (operationRows identity 1) (terminal identity activation)).append context) :=
  SourceProof.sequence (SourceProof.sequence pureProof (firstRequest (activation := activation) tail))
    (laterSuffix (activation := activation) tail)

noncomputable def guardedProof (tail : CellTail identity context) :
    SourceProof actions phases world installations
      (.sequence .pure (.cleanup (needs := [.cell identity]) (callbackFootprint identity)
        (operationRows identity 1)
        (.sequence (.sequence .pure (.request (effect := effect) (operation := 0))) (suffixRows identity))))
      ((terminal identity activation).append context) := by
  have found := tail.lookup (operation := 1)
  let callback := operationProof (identity := identity) (actions := actions) (phases := phases) (world := world)
    (installations := installations) (operation := 1)
    (context := Context.normal ((terminal identity activation).append context))
    (by
      simp only [terminal, Context.append, ReturnHints.append, SourceDependencyCapture.Scope.append,
        select, effect, reduceCtorEq, ↓reduceIte]
      rw [found]
      rfl)
  let body := protectedProof (actions := actions) (phases := phases) (world := world)
    (installations := installations) (activation := activation) tail
  let cleanup : SourceProof actions phases world installations
      (.cleanup (needs := [.cell identity]) (callbackFootprint identity) (operationRows identity 1)
        (.sequence (.sequence .pure (.request (effect := effect) (operation := 0))) (suffixRows identity)))
      ((terminal identity activation).append context) :=
    ⟨.cleanup body.code callback.code,
      .cleanup (body := body.code) (callback := callback.code) body.checked callback.checked⟩
  exact SourceProof.sequence pureProof cleanup

def cellBodyRows (identity : Nat) : Rows (signature (cellBodyPlan identity)) :=
  .sequence (handledRows identity) (operationRows identity 0)

def resourceRows : Rows (signature resourcePlan) :=
  .sequence .pure (.resource cellBodyRows)

noncomputable def cellBodyProof (identity : Nat) :
    SourceProof actions phases world installations (cellBodyRows identity)
      (Context.cell (identity := identity) .nil) := by
  let tail := CellTail.plain (operation := 0) (CellTail.cell (identity := identity))
  let bodies := fun activation (_fresh : activation ∉ installations) =>
    guardedProof (actions := actions) (phases := phases) (world := world)
      (installations := activation :: installations) (activation := activation) tail
  let handledCode : SourceAdmission.Code [] actions [] phases world installations (handledRows identity)
      (.plain (operationRows identity 0) (.cell (identity := identity) .nil)) :=
    .handler (fun activation fresh => (bodies activation fresh).code)
  have supported : (declarationRows identity).resourceSupport ⊆
      SourceDependencyCapture.Scope.visibleResources
        (.plain (.sequence .pure (.request (.cell identity) 0)) (.cell identity .nil)) ++ ([] : List Nat) := by
    simp [declarationRows, ClauseRows.resourceSupport, SourceDependencyCapture.Scope.visibleResources]
  have handledChecked : CodeChecked [] [] handledCode := by
    apply CodeChecked.handler (body := fun activation fresh => (bodies activation fresh).code) supported
    intro activation fresh
    exact (bodies activation fresh).checked
  exact SourceProof.sequence ⟨handledCode, handledChecked⟩ (operationProof (identity := identity) (operation := 0) (by simp [select]))

noncomputable def resourceProof :
    SourceProof InitialAdmission.actions (OwnerPhaseTransitions.available []) [] [] resourceRows Context.nil := by
  let bodies := fun identity (_fresh : identity ∉ ([] : List Nat)) =>
    cellBodyProof (actions := InitialAdmission.actions) (phases := OwnerPhaseTransitions.available [])
      (world := [identity]) (installations := []) identity
  let code : SourceAdmission.Code [] InitialAdmission.actions [] (OwnerPhaseTransitions.available []) [] []
      (.resource cellBodyRows) Context.nil := .resource (fun identity fresh => (bodies identity fresh).code)
  have checked : CodeChecked [] [] code := by
    apply CodeChecked.resource (body := fun identity fresh => (bodies identity fresh).code)
    intro identity fresh
    exact (bodies identity fresh).checked
  exact SourceProof.sequence pureProof ⟨code, checked⟩

open RecursiveRequirements (Requirements LocalOwner)

noncomputable def CellTail.root (tail : CellTail identity context) : Requirements [] := by
  induction tail with
  | cell => exact empty
  | plain tail ih => exact ih
  | spent tail ih => rename_i owner; exact .sequence (.spent owner) ih

theorem operationAccounting
    (found : select (.cell identity) operation context = some (.builtin identity))
    (waiting : Accounting.Wait world installations context .ordinary root) :
    Accounting.Run world installations (operationRows identity operation) context root :=
  .sequence (.pure (.plain (.builtin found waiting)))

theorem CellTail.accounting (tail : CellTail identity context) :
    Accounting.Wait world installations context .ordinary tail.root := by
  induction tail with
  | cell => exact .cell .nil
  | plain tail ih => exact .plain (operationAccounting tail.lookup ih)
  | spent tail ih => exact .spent ih

theorem CellTail.accountingUnwind (tail : CellTail identity context) :
    Accounting.Wait world installations context .unwind tail.root := by
  induction tail with
  | cell => exact .cell .nil
  | plain tail ih => exact .skipped ih
  | spent tail ih => exact .spent ih

theorem CellTail.localOwner (tail : CellTail identity context) (absent : owner ∉ context.ticketNames) :
    LocalOwner owner phase tail.root tail.root phase := by
  induction tail with
  | cell => exact .empty
  | plain tail ih => exact ih absent
  | @spent scope hints context other tail ih =>
      have separate : other ≠ owner := by
        intro same; subst other
        exact absent (by simp [Context.ticketNames])
      exact .sequence (.spentOther separate) (ih (by
        intro member; exact absent (by simp [Context.ticketNames, member])))

theorem laterAccounting (tail : CellTail identity context) :
    Accounting.Wait world installations ((laterCapture identity activation).append context) .ordinary tail.root := by
  have found := tail.lookup (operation := 1)
  apply Accounting.Wait.plain
  apply operationAccounting
  · simp only [terminal, Context.append, ReturnHints.append, SourceDependencyCapture.Scope.append,
      select, effect, reduceCtorEq, ↓reduceIte]
    rw [found]; rfl
  · apply Accounting.Wait.cleanup
    apply operationAccounting
    · simp only [terminal, Context.append, Context.callback, ReturnHints.append, SourceDependencyCapture.Scope.append,
        select, effect, reduceCtorEq, ↓reduceIte]
      rw [found]; rfl
    · exact .normal (.handler tail.accounting)

theorem laterAccountingUnwind (tail : CellTail identity context) :
    Accounting.Wait world installations ((laterCapture identity activation).append (Context.closing context))
      .unwind tail.root := by
  have found := tail.lookup (operation := 1)
  apply Accounting.Wait.skipped
  apply Accounting.Wait.cleanup
  apply operationAccounting
  · simp only [terminal, Context.append, Context.callback, ReturnHints.append,
      SourceDependencyCapture.Scope.append, select, effect, reduceCtorEq, ↓reduceIte]
    rw [found]; rfl
  · exact .unwinding (.handler (.closing tail.accounting))

def consumingRoot (root : Requirements []) : Requirements [] :=
  .choice (.sequence empty (.sequence empty root)) (.sequence empty (.sequence empty root)) (.refl [])

def invocationRoot (owner : Nat) (root : Requirements []) : Requirements [owner] :=
  .sequence (.retire owner) (.sequence (.spent owner) root)

theorem laterClauseAccounting (tail : CellTail identity context) :
    Accounting.Run world installations (fixtureClauseRows identity owner)
      (.live (owner := owner) (resumeDemand := resumeDemand) (laterCapture identity activation) context)
      (.choice (invocationRoot owner tail.root) (invocationRoot owner tail.root) (.refl [owner])) := by
  apply Accounting.Run.sequence
  apply Accounting.Run.pure
  apply Accounting.Wait.plain
  apply Accounting.Run.choice
  · apply Accounting.Run.sequence
    apply Accounting.Run.sequence
    apply Accounting.Run.pure
    apply Accounting.Wait.plain
    apply Accounting.Run.resume (front := .plain (operationRows identity 1) .nil)
      (captured := laterCapture identity activation) (tail := context)
    · exact .plain .hit
    · simpa only [Context.append, ReturnHints.append, SourceDependencyCapture.Scope.append, CellTail.root]
        using laterAccounting (world := world) (installations := installations) (activation := activation)
          (CellTail.plain (operation := 1) (CellTail.spent (owner := owner) tail))
  · apply Accounting.Run.dispose (front := .nil) (captured := laterCapture identity activation) (tail := context)
    · exact .hit
    · simpa only [Context.append, ReturnHints.append, SourceDependencyCapture.Scope.append, CellTail.root]
        using laterAccountingUnwind (world := world) (installations := installations) (activation := activation)
          (CellTail.spent (owner := owner) tail)

theorem laterClauseBinding (tail : CellTail identity context) (absent : owner ∉ context.ticketNames) :
    LocalOwner owner .available
      (.choice (invocationRoot owner tail.root) (invocationRoot owner tail.root) (.refl [owner]))
      (consumingRoot tail.root) .consumed :=
  .choice (.sequence .retireSelf (.sequence .spentSelf (tail.localOwner absent)))
    (.sequence .retireSelf (.sequence .spentSelf (tail.localOwner absent)))

theorem laterRequestAccounting (tail : CellTail identity context) :
    Accounting.Run world installations (Rows.request (effect := effect) (operation := 0))
      ((laterCapture identity activation).append context) (consumingRoot tail.root) := by
  apply Accounting.Run.request
    (captured := laterCapture identity activation) (tail := context)
    (contract := ⟨true, some (callbackFootprint identity), none⟩)
    (modes := (some (clauseDependencies identity), none))
    (bodyRows := fixtureClauseRows identity)
    (localRoot := fun owner _ => .choice (invocationRoot owner tail.root) (invocationRoot owner tail.root) (.refl [owner]))
  · rfl
  · exact .selected (.plain (.cleanup .here)) .ordinary
  · intro owner demand absent
    exact laterClauseAccounting tail
  · intro owner demand absent
    apply laterClauseBinding tail
    intro member
    apply absent
    simpa only [Context.append_ticketNames, Context.ticketNames, laterCapture, terminal, List.nil_append] using member

theorem laterSuffixAccounting (tail : CellTail identity context) :
    Accounting.Run world installations (suffixRows identity)
      ((Context.cleanup (needs := [.cell identity]) (callbackFootprint identity)
        (operationRows identity 1) (terminal identity activation)).append context) (consumingRoot tail.root) :=
  .sequence (.sequence (.pure (.plain (laterRequestAccounting (activation := activation) tail))))

theorem firstAccounting (tail : CellTail identity context) :
    Accounting.Wait world installations ((firstCapture identity activation).append context)
      .ordinary (consumingRoot tail.root) :=
  .plain (laterSuffixAccounting (activation := activation) tail)

theorem firstAccountingUnwind (tail : CellTail identity context) :
    Accounting.Wait world installations ((firstCapture identity activation).append (Context.closing context))
      .unwind tail.root := by
  have found := tail.lookup (operation := 1)
  apply Accounting.Wait.skipped
  apply Accounting.Wait.cleanup
  apply operationAccounting
  · simp only [terminal, Context.append, Context.callback, ReturnHints.append,
      SourceDependencyCapture.Scope.append, select, effect, reduceCtorEq, ↓reduceIte]
    rw [found]; rfl
  · exact .unwinding (.handler (.closing tail.accounting))

def firstInvocationRoot (owner : Nat) (root : Requirements []) : Requirements [owner] :=
  .sequence (.retire owner) (consumingRoot (.sequence (.spent owner) root))

def firstClauseRoot (owner : Nat) (root : Requirements []) : Requirements [owner] :=
  .choice (firstInvocationRoot owner root) (invocationRoot owner root) (.refl [owner])

def firstRoot (root : Requirements []) : Requirements [] :=
  .choice (.sequence empty (consumingRoot (.sequence empty root)))
    (.sequence empty (.sequence empty root)) (.refl [])

theorem consumingRootBinding
    (binding : LocalOwner owner phase localRoot outerRoot phase) :
    LocalOwner owner phase (consumingRoot localRoot) (consumingRoot outerRoot) phase :=
  .choice (.sequence .empty (.sequence .empty binding)) (.sequence .empty (.sequence .empty binding))

theorem firstClauseAccounting (tail : CellTail identity context) :
    Accounting.Run world installations (fixtureClauseRows identity owner)
      (.live (owner := owner) (resumeDemand := resumeDemand) (firstCapture identity activation) context)
      (firstClauseRoot owner tail.root) := by
  apply Accounting.Run.sequence
  apply Accounting.Run.pure
  apply Accounting.Wait.plain
  apply Accounting.Run.choice
  · apply Accounting.Run.sequence
    apply Accounting.Run.sequence
    apply Accounting.Run.pure
    apply Accounting.Wait.plain
    apply Accounting.Run.resume (front := .plain (operationRows identity 1) .nil)
      (captured := firstCapture identity activation) (tail := context)
    · exact .plain .hit
    · simpa only [Context.append, ReturnHints.append, SourceDependencyCapture.Scope.append, CellTail.root]
        using firstAccounting (world := world) (installations := installations) (activation := activation)
          (CellTail.plain (operation := 1) (CellTail.spent (owner := owner) tail))
  · apply Accounting.Run.dispose (front := .nil) (captured := firstCapture identity activation) (tail := context)
    · exact .hit
    · simpa only [Context.append, ReturnHints.append, SourceDependencyCapture.Scope.append, CellTail.root]
        using firstAccountingUnwind (world := world) (installations := installations) (activation := activation)
          (CellTail.spent (owner := owner) tail)

theorem firstClauseBinding (tail : CellTail identity context) (absent : owner ∉ context.ticketNames) :
    LocalOwner owner .available (firstClauseRoot owner tail.root) (firstRoot tail.root) .consumed :=
  .choice (.sequence .retireSelf (consumingRootBinding (.sequence .spentSelf (tail.localOwner absent))))
    (.sequence .retireSelf (.sequence .spentSelf (tail.localOwner absent)))

theorem firstRequestAccounting (tail : CellTail identity context) :
    Accounting.Run world installations (Rows.request (effect := effect) (operation := 0))
      ((firstCapture identity activation).append context) (firstRoot tail.root) := by
  apply Accounting.Run.request
    (captured := firstCapture identity activation) (tail := context)
    (contract := ⟨true, some (callbackFootprint identity), none⟩)
    (modes := (some (clauseDependencies identity), none))
    (bodyRows := fixtureClauseRows identity)
    (localRoot := fun owner _ => firstClauseRoot owner tail.root)
  · rfl
  · exact .selected (.plain (.cleanup .here)) .ordinary
  · intro owner demand absent
    exact firstClauseAccounting tail
  · intro owner demand absent
    apply firstClauseBinding tail
    intro member
    apply absent
    simpa only [Context.append_ticketNames, Context.ticketNames, firstCapture, terminal, List.nil_append] using member

theorem protectedAccounting (tail : CellTail identity context) :
    Accounting.Run world installations
      (.sequence (.sequence .pure (.request (effect := effect) (operation := 0))) (suffixRows identity))
      ((Context.cleanup (needs := [.cell identity]) (callbackFootprint identity)
        (operationRows identity 1) (terminal identity activation)).append context) (firstRoot tail.root) :=
  .sequence (.sequence (.pure (.plain (firstRequestAccounting (activation := activation) tail))))

theorem guardedAccounting (tail : CellTail identity context) :
    Accounting.Run world installations
      (.sequence .pure (.cleanup (needs := [.cell identity]) (callbackFootprint identity)
        (operationRows identity 1)
        (.sequence (.sequence .pure (.request (effect := effect) (operation := 0))) (suffixRows identity))))
      ((terminal identity activation).append context) (firstRoot tail.root) :=
  .sequence (.pure (.plain (.installCleanup (protectedAccounting (activation := activation) tail))))

theorem cellBodyAccounting :
    Accounting.Run world installations (cellBodyRows identity) (Context.cell (identity := identity) .nil)
      (firstRoot empty) :=
  .sequence (.installHandler (fun activation _ =>
    guardedAccounting (activation := activation) (CellTail.plain (operation := 0) (CellTail.cell (identity := identity)))))

theorem resourceAccounting : Accounting.Run [] [] resourceRows Context.nil (firstRoot empty) :=
  .sequence (.pure (.plain (.installResource (fun _ _ => cellBodyAccounting))))

theorem rootChecked : RecursiveRequirements.Checked [] [] (OwnerPhaseTransitions.available [])
    (annotateDisposals (firstRoot empty)) [] := by
  apply RecursiveRequirements.evaluate_sound
  simp [firstRoot, consumingRoot, empty, annotateDisposals, RecursiveRequirements.evaluate,
    RecursiveRequirements.evaluateFuel, OwnerSource.exportAt, ProtectionResiduals.residual_empty,
    ProtectionResiduals.merge, OwnerPhaseTransitions.spendAll]

/-- Every field is built from the exact normalized source and its authenticated
rows. Neither a future execution nor an external certificate is a premise. -/
noncomputable def program : Program operations policy ports [] [] normalized :=
  { result := .integer, resultRows := .integer,
    dependencies := _, plan := resourcePlan, rows := resourceRows,
    demand := [], requirements := resourceRequirements, source := resourceSource,
    authenticated := resourceAuth, certified := resourceCertified,
    certificate := resourceProof.code, resourceChecked := resourceProof.checked,
    rootDemand := [], root := firstRoot empty, interpreted := resourceAccounting,
    annotated := firstRoot empty, annotation := .original,
    rootRow := [], checked := rootChecked, bounded := List.nil_subset _,
    resources := by decide, builtinSignatures := builtinSignatures }

theorem closed_initial_state (tables : CallableProtectionFrames.Tables)
    (families : SourceDependencyFrames.Families) (required : SourceContextualRechecking.Required) :
    InstallationState operations policy InitialAdmission.contracts tables families required [] InitialAdmission.annotations
      [] [] [] [] [] [] [] ports InitialAdmission.owners InitialAdmission.emptyRows
      (.value .integer) (.value .integer) (initialRun normalized) :=
  program.closed_initial_state tables families required

open InstallationSupport.Preservation

theorem finite_prefix (tables : CallableProtectionFrames.Tables)
    (families : SourceDependencyFrames.Families) (required : SourceContextualRechecking.Required) (fuel : Nat) :
    ∃ count final,
      RawTrace (initialRun normalized).execution count final.run.execution ∧
      Valid policy [] [] [] ports InitialAdmission.emptyRows .integer .integer final ∧
      count ≤ fuel ∧ (count = fuel ∨ Terminal final) :=
  InstallationSupport.Preservation.InitialAdmission.Program.finite_prefix program tables families required fuel

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreKernelProgram

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreKernelProgram.resourceProof

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreKernelProgram.resourceAccounting
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreKernelProgram.rootChecked

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreKernelProgram.program
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreKernelProgram.closed_initial_state
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreKernelProgram.finite_prefix
