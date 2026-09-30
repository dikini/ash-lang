import SourceDependencyChecks
import SourceDependencyNeutral

/-! Contextual source checking ignores spent markers through a proved
projection. Uniform clause schemes quantify over structurally checked captured
source. They do not quantify over runs or assume a full successor invariant.
The rich declaration/source and runtime invariant integration remain separate. -/
namespace Ash.OneShot.SourceDependencySchemes
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyChecks (Local Pending)
open SourceDependencyProjection (project)
open SourceDependencyAnnotations (Dependencies)
open SourceDependencyCapture
open OwnerPhaseTransitions (Phases spend)
abbrev Receiving := SourceDependencyCapture.Scope

abbrev Checked (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : Phases) (world : List Nat) (dependencies : Dependencies) (scope : Receiving) : Prop :=
  Local outward actions phases world dependencies (project scope)

abbrev Retained (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : Phases) (world : List Nat) (forest outside : Receiving) : Prop :=
  Pending outward actions phases world (project forest) (project outside)

/-- This equation changes only the source-checking view. The owner remains
spent in the actual stack and in the independent phase map. -/
theorem checked_spent : Checked outward actions phases world dependencies (.spent owner scope) ↔
    Checked outward actions phases world dependencies scope := Iff.rfl

theorem retained_spent : Retained outward actions phases world (.spent owner forest) outside ↔
    Retained outward actions phases world forest outside := Iff.rfl

theorem retained_outside_spent : Retained outward actions phases world forest (.spent owner outside) ↔
    Retained outward actions phases world forest outside := Iff.rfl

theorem retained_append : Retained outward actions phases world (first.append second) outside ↔
    Retained outward actions phases world first (second.append outside) ∧
      Retained outward actions phases world second outside := by
  simp only [Retained, SourceDependencyProjection.project_append, Pending.append_iff]

theorem retained_capture (checked : Retained outward actions phases world (captured.append tail) outside) :
    Retained outward actions phases world (.live owner captured tail) outside :=
  by
    apply Pending.live
    · simpa only [Retained, SourceDependencyProjection.project_append] using (retained_append.mp checked).1
    · exact (retained_append.mp checked).2

theorem checked_request (checked : Checked outward actions phases world (.request effect operation) scope) :
    checkCapture outward scope effect operation = true := by
  simpa only [SourceDependencyProjection.project_checkCapture] using Local.request_guard checked

theorem checked_request_schedule
    (checked : Checked outward actions phases world (.request effect operation) scope)
    (found : select effect operation scope = some (.handler captured tail contract modes))
    (disposes : contract.dispose = true) :
    Retained outward actions phases world captured.forClosing (.running tail) := by
  have projectedFound : select effect operation (project scope) =
      some (.handler (project captured) (project tail) contract modes) := by
    rw [SourceDependencyProjection.project_select, found]
    rfl
  have scheduled := Local.request_schedule checked projectedFound disposes
  simpa only [Retained, SourceDependencyProjection.project_forClosing, project,
    SourceDependencyProjection.project_idempotent] using scheduled

theorem owners_project (scope : Receiving) :
    SourceDependencyOwners.owners (project scope) = SourceDependencyOwners.owners scope := by
  induction scope <;> simp_all [project, SourceDependencyOwners.owners]

theorem pending_owners_unproject
    (checked : SourceDependencyOwners.PendingWithin world owned (project scope)) :
    SourceDependencyOwners.PendingWithin world owned scope := by
  induction scope with
  | nil => exact .nil
  | plain dependencies rest ih => cases checked with | plain code tail => exact .plain code (ih tail)
  | handler effect table families rest ih => cases checked with | handler tail => exact .handler (ih tail)
  | cell identity rest ih => cases checked with | cell tail => exact .cell (ih tail)
  | cleanup needs callback rest ih => cases checked with | cleanup tail => exact .cleanup (ih tail)
  | running rest ih => cases checked with | running tail => exact .running (ih tail)
  | live owner captured rest ihCaptured ihRest =>
      cases checked with | live inside outside => exact .live (ihCaptured inside) (ihRest outside)
  | spent owner rest ih => exact .spent (ih checked)

theorem checked_request_owners
    (checked : Checked outward actions phases world (.request effect operation) scope)
    (found : select effect operation scope = some (.handler captured tail contract modes))
    (disposes : contract.dispose = true) :
    SourceDependencyOwners.PendingWithin world (SourceDependencyOwners.owners captured) captured := by
  have selected : select effect operation (project scope) =
      some (.handler (project captured) (project tail) contract modes) := by
    rw [SourceDependencyProjection.project_select, found]
    rfl
  apply pending_owners_unproject
  simpa only [owners_project] using Local.request_owners checked selected disposes

/-- The local structural owner bound describes this actual cut because the
rich source segment authenticates both its pending code and owner identities. -/
theorem capture_internal_uses
    (cut : HandlerCut requested whole capture tail handler)
    (source : SourceDependencyFrames.Segment operations policy contracts tables families actions world
      whole input output demand requirements records wholeScope incoming outgoing)
    (checked : Checked outward actions phases world (.request requested operation) wholeScope)
    (known : lookup operation (tables handler) = some offered) (disposes : offered.dispose = true) :
    InternalUses capture.erase.liveTickets capture.erase.pending := by
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
    annotation, selected, saved, outside, sameScope, sameDemand, sameRecords, selection, evaluation⟩ :=
    SourceDependencyFrames.capture_segments cut source
  cases annotated : lookupDependencies operation (families handler) with
  | none =>
      have absent : select requested operation wholeScope = none := by
        simpa only [chosen, known, annotated] using selection operation
      have guard := checked_request checked
      simp [checkCapture, absent] at guard
  | some modes =>
      have found : select requested operation wholeScope = some (.handler capScope tailScope offered modes) := by
        simpa only [chosen, known, annotated] using selection operation
      exact SourceDependencyOwners.internal_uses saved (checked_request_owners checked found disposes)

theorem checked_sequence : Checked outward actions phases world (.sequence first second) scope ↔
    Checked outward actions phases world first (.plain second scope) ∧
      Checked outward actions phases world second scope := Local.sequence_iff

theorem checked_cleanup : Checked outward actions phases world (.cleanup needs callback body) scope ↔
    Checked outward actions phases world body (.cleanup needs callback scope) ∧
      Checked outward actions phases world callback (.running scope) := Local.cleanup_iff

/-- Recover the actual invocation result, then reuse the retained-source
proof. Projection does not manufacture access to an absent or consumed owner. -/
theorem checked_resume (checked : Checked outward actions phases world (.invoke ⟨owner, .resume⟩) scope) :
    ∃ after, checkResume actions phases owner scope = some after ∧
      Retained outward actions (spend phases owner) world after .nil := by
  obtain ⟨projectedAfter, computed, retained⟩ := Local.resume_restored checked
  have same := SourceDependencyProjection.project_checkResume (actions := actions) (phases := phases) (owner := owner) scope
  rw [computed] at same
  cases actual : checkResume actions phases owner scope with
  | none => simp [actual] at same
  | some after =>
      have scopes : project projectedAfter = project after := by simpa only [actual, Option.map_some, Option.some.injEq] using same
      exact ⟨after, rfl, by simpa only [Retained, ← scopes, project] using retained⟩

theorem checked_dispose (checked : Checked outward actions phases world (.invoke ⟨owner, .dispose⟩) scope) :
    ∃ after, checkDispose outward actions phases owner scope = some after ∧
      Retained outward actions (spend phases owner) world after .nil := by
  obtain ⟨projectedAfter, computed, retained⟩ := Local.dispose_scheduled checked
  have same := SourceDependencyProjection.project_checkDispose (outward := outward) (actions := actions)
    (phases := phases) (owner := owner) scope
  rw [computed] at same
  cases actual : checkDispose outward actions phases owner scope with
  | none => simp [actual] at same
  | some after =>
      have scopes : project projectedAfter = project after := by simpa only [actual, Option.map_some, Option.some.injEq] using same
      exact ⟨after, rfl, by simpa only [Retained, ← scopes, project] using retained⟩

/-- All source premises inspect the present captured forest and receiving
tail. Check retained work after the new owner is spent, since the clause may
consume it. Disposal also checks the explicitly scheduled callback forest.
Deriving these premises at every admitted capture is still required. -/
structure CaptureSource (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : Phases) (world : List Nat) (owner : Nat) (rights : Syntax.OneShotRights)
    (captured tail : Receiving) : Prop where
  saved : rights.resume = true → Retained outward actions (spend phases owner) world captured tail
  waiting : Retained outward actions (spend phases owner) world tail .nil
  disposal : rights.dispose = true → captured.held = false ∧
    SourceRecursiveRoutes.Closing outward captured.shape [] [] ∧
    Retained outward actions (spend phases owner) world captured.forClosing (.running tail)

/-- A clause family is checked once for arbitrary owner names, phase maps,
worlds and admitted captured source. This is an explicit universal source rule;
it neither unfolds effect dispatch recursively nor restricts execution length. -/
inductive ClauseFamily (outward : List Instance) (rights : Syntax.OneShotRights)
    (family : Nat → Dependencies) : Prop where
  | checked (body : ∀ actions phases world owner captured tail,
      actions owner = some rights → phases owner = .available →
      CaptureSource outward actions phases world owner rights captured tail →
      Checked outward actions phases world (family owner) (.live owner captured tail)) :
      ClauseFamily outward rights family

theorem ClauseFamily.instantiate (scheme : ClauseFamily outward rights family)
    (known : actions owner = some rights) (available : phases owner = .available)
    (source : CaptureSource outward actions phases world owner rights captured tail) :
    Checked outward actions phases world (family owner) (.live owner captured tail) := by
  cases scheme with | checked body => exact body actions phases world owner captured tail known available source

/-- Reuse finite retained-source recomposition. No induction over possible
captures or evaluation histories is needed for the ordinary resume clause. -/
theorem resume_family {rights : Syntax.OneShotRights} (permission : rights.resume = true) :
    ClauseFamily outward rights (fun owner => .invoke ⟨owner, .resume⟩) := by
  constructor
  intro actions phases world owner captured tail known available source
  apply Local.resume (after := (project captured).append (.spent owner (project tail)))
    (ResumeChecked.checked OwnerCut.hit known permission available)
  simpa only [Retained, SourceDependencyProjection.project_append, project, SourceDependencyProjection.project_idempotent] using
    (retained_append.mpr ⟨by simpa only [SourceDependencyProjection.scope_append_nil] using source.saved permission, source.waiting⟩ :
      Retained outward actions (spend phases owner) world (captured.append tail) .nil)

theorem dispose_family {rights : Syntax.OneShotRights} (permission : rights.dispose = true) :
    ClauseFamily outward rights (fun owner => .invoke ⟨owner, .dispose⟩) := by
  constructor
  intro actions phases world owner captured tail known available source
  obtain ⟨unprotected, closes, scheduled⟩ := source.disposal permission
  have projectedCloses : SourceRecursiveRoutes.Closing outward (project captured).shape [] [] :=
    check_closing_iff.mp (by simpa only [SourceDependencyProjection.project_checkClosing] using check_closing_iff.mpr closes)
  apply Local.dispose (after := (project captured).forClosing.append (.running (.spent owner (project tail))))
    (DisposeChecked.checked OwnerCut.hit known permission available
      (by simpa only [SourceDependencyProjection.project_held] using unprotected) projectedCloses)
  have joined : Retained outward actions (spend phases owner) world
      (captured.forClosing.append (.running tail)) .nil :=
    retained_append.mpr ⟨by simpa only [SourceDependencyProjection.scope_append_nil] using scheduled, Pending.running source.waiting⟩
  simpa only [Retained, SourceDependencyProjection.project_append, project,
    SourceDependencyProjection.project_idempotent, SourceDependencyProjection.project_forClosing] using joined

/-- Value evaluation may precede a uniformly checked clause without changing
its capability or receiving scope. Latent function effects are not Silent. -/
theorem ClauseFamily.silent_prefix (scheme : ClauseFamily outward rights family) (silent : SourceDependencyAnnotations.Dependencies.Silent dependencies) :
    ClauseFamily outward rights (fun owner => .sequence dependencies (family owner)) := by
  constructor
  intro actions phases world owner captured tail known available source
  exact .sequence (.silent silent) (scheme.instantiate known available source)

theorem ClauseFamily.choice (first : ClauseFamily outward rights family) (second : ClauseFamily outward rights alternative) :
    ClauseFamily outward rights (fun owner => .choice (family owner) (alternative owner)) := by
  constructor
  intro actions phases world owner captured tail known available source
  exact .choice (first.instantiate known available source) (second.instantiate known available source)

/-- Phase extension preserves every currently available owner. It is used
for fresh allocation, not for reversing an actual consumption. -/
def PhaseExtension (before after : Phases) : Prop :=
  ∀ owner, before owner = .available → after owner = .available

theorem PhaseExtension.spend (extension : PhaseExtension before after) :
    PhaseExtension (spend before owner) (spend after owner) := by
  intro other available
  by_cases same : other = owner
  · subst other
    rw [OwnerPhaseTransitions.spend_self] at available
    cases available
  · rw [OwnerPhaseTransitions.spend_other same] at available ⊢
    exact extension other available

theorem introduce_extends : PhaseExtension phases (OwnerPhaseTransitions.introduce phases owner) := by
  intro other available
  by_cases same : other = owner <;> simp [OwnerPhaseTransitions.introduce, same, available]

/-- Structural induction over the existing source checks transports permission-map, world and phase
extensions, including all retained source recursively checked by invocations. -/
theorem local_transport (source : Local outward actions before world dependencies receiving)
    (extension : PhaseExtension before after) (permissions : Syntax.UsageExtension actions nextActions)
    (larger : world ⊆ nextWorld) : Local outward nextActions after nextWorld dependencies receiving := by
  refine Local.rec
    (motive_1 := fun before world dependencies receiving _ => ∀ after nextActions nextWorld, PhaseExtension before after →
      Syntax.UsageExtension actions nextActions → world ⊆ nextWorld → Local outward nextActions after nextWorld dependencies receiving)
    (motive_2 := fun before world forest outside _ => ∀ after nextActions nextWorld, PhaseExtension before after →
      Syntax.UsageExtension actions nextActions → world ⊆ nextWorld → Pending outward nextActions after nextWorld forest outside)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ source after nextActions nextWorld extension permissions larger
  · intro phases world scope after nextActions nextWorld extension permissions larger
    exact .pure
  · intro scope effect operation phases world guarded scheduled ownerBound ih after nextActions nextWorld extension permissions larger
    exact .request guarded (fun captured tail contract modes found disposes =>
      ih captured tail contract modes found disposes after nextActions nextWorld extension permissions larger)
      (fun captured tail contract modes found disposes => (ownerBound captured tail contract modes found disposes).world_weaken larger)
  · intro phases owner scope result world access restored ih after nextActions nextWorld extension permissions larger
    cases access with
    | checked located known permission available =>
        exact .resume (.checked located (permissions _ _ known) permission (extension _ available)) (ih _ nextActions nextWorld extension.spend permissions larger)
  · intro phases owner scope result world access scheduled ih after nextActions nextWorld extension permissions larger
    cases access with
    | checked located known permission available unprotected closes =>
        exact .dispose (.checked located (permissions _ _ known) permission (extension _ available) unprotected closes) (ih _ nextActions nextWorld extension.spend permissions larger)
  · intro phases world before next scope first second ihFirst ihSecond after nextActions nextWorld extension permissions larger
    exact .sequence (ihFirst after nextActions nextWorld extension permissions larger) (ihSecond after nextActions nextWorld extension permissions larger)
  · intro phases world first scope second left right ihLeft ihRight after nextActions nextWorld extension permissions larger
    exact .choice (ihLeft after nextActions nextWorld extension permissions larger) (ihRight after nextActions nextWorld extension permissions larger)
  · intro phases world dependencies effect table families scope body ih after nextActions nextWorld extension permissions larger
    exact .handler (ih after nextActions nextWorld extension permissions larger)
  · intro phases world dependencies needs callback scope body completion ihBody ihCallback after nextActions nextWorld extension permissions larger
    exact .cleanup (ihBody after nextActions nextWorld extension permissions larger) (ihCallback after nextActions nextWorld extension permissions larger)
  · intro world phases family scope body ih after nextActions nextWorld extension permissions larger
    exact .resource (fun identity fresh => ih identity (fun member => fresh (larger member))
      after nextActions (nextWorld ++ [identity]) extension permissions
      (ScopedExpressions.append_subset larger (List.Subset.refl _)))
  · intro phases world outside after nextActions nextWorld extension permissions larger
    exact .nil
  · intro phases world dependencies rest outside code tail ihCode ihTail after nextActions nextWorld extension permissions larger
    exact .plain (ihCode after nextActions nextWorld extension permissions larger) (ihTail after nextActions nextWorld extension permissions larger)
  · intro phases world rest outside effect table families tail ih after nextActions nextWorld extension permissions larger
    exact .handler (ih after nextActions nextWorld extension permissions larger)
  · intro phases world rest outside identity tail ih after nextActions nextWorld extension permissions larger
    exact .cell (ih after nextActions nextWorld extension permissions larger)
  · intro phases world dependencies rest outside needs callback tail ihCallback ihTail after nextActions nextWorld extension permissions larger
    exact .cleanup (ihCallback after nextActions nextWorld extension permissions larger) (ihTail after nextActions nextWorld extension permissions larger)
  · intro phases world rest outside tail ih after nextActions nextWorld extension permissions larger
    exact .running (ih after nextActions nextWorld extension permissions larger)
  · intro phases world captured rest outside owner saved tail ihSaved ihTail after nextActions nextWorld extension permissions larger
    exact .live (ihSaved after nextActions nextWorld extension permissions larger) (ihTail after nextActions nextWorld extension permissions larger)
  · intro phases world rest outside owner tail ih after nextActions nextWorld extension permissions larger
    exact .spent (ih after nextActions nextWorld extension permissions larger)

theorem pending_transport (source : Pending outward actions before world forest outside)
    (extension : PhaseExtension before after) (permissions : Syntax.UsageExtension actions nextActions)
    (larger : world ⊆ nextWorld) : Pending outward nextActions after nextWorld forest outside := by
  induction forest generalizing outside with
  | nil => exact .nil
  | plain dependencies rest ih => cases source with
      | plain code tail => exact .plain (local_transport code extension permissions larger) (ih tail)
  | handler effect table families rest ih => cases source with
      | handler tail => exact .handler (ih tail)
  | cell identity rest ih => cases source with
      | cell tail => exact .cell (ih tail)
  | cleanup needs callback rest ih => cases source with
      | cleanup code tail => exact .cleanup (local_transport code extension permissions larger) (ih tail)
  | running rest ih => cases source with
      | running tail => exact .running (ih tail)
  | live owner captured rest ihCaptured ihRest => cases source with
      | live saved tail => exact .live (ihCaptured saved) (ihRest tail)
  | spent owner rest ih => cases source with
      | spent tail => exact .spent (ih tail)

theorem local_phase_transport (source : Local outward actions before world dependencies receiving)
    (extension : PhaseExtension before after) : Local outward actions after world dependencies receiving :=
  local_transport source extension (fun _ _ known => known) (List.Subset.refl _)

theorem pending_phase_transport (source : Pending outward actions before world forest outside)
    (extension : PhaseExtension before after) : Pending outward actions after world forest outside :=
  pending_transport source extension (fun _ _ known => known) (List.Subset.refl _)

/-- Allocation preserves checks for retained source while adding the live
boundary. Runtime issued-name freshness and action-map extension are separate. -/
theorem retained_capture_introduce (source : Retained outward actions phases world (captured.append tail) outside) :
    Retained outward actions (OwnerPhaseTransitions.introduce phases owner) world (.live owner captured tail) outside :=
  pending_phase_transport (retained_capture source) introduce_extends

/-- Fresh allocation derives the clause's captured-source premises from
an admitted request and its retained forest. The callback schedule comes from
the request rule itself. No post-allocation source judgment is an input. -/
theorem capture_source_from_request
    (checked : Checked outward actions phases world (.request effect operation) (captured.append tail))
    (retained : Retained outward actions phases world (captured.append tail) .nil)
    (found : select effect operation (captured.append tail) = some (.handler captured tail contract modes))
    (disposalPermission : rights.dispose = true → contract.dispose = true)
    (fresh : actions owner = none) (consumed : phases owner = .consumed) :
    CaptureSource outward (actions.insert owner rights) (OwnerPhaseTransitions.introduce phases owner)
      world owner rights captured tail := by
  have permissions := Syntax.fresh_usage_insert_extends (rights := rights) fresh
  have samePhases := OwnerCaptureContracts.spend_introduced consumed
  have joined : Retained outward (actions.insert owner rights) phases world (captured.append tail) .nil :=
    pending_transport retained (fun _ ready => ready) permissions (List.Subset.refl _)
  obtain ⟨saved, waiting⟩ := retained_append.mp joined
  refine ⟨?_, ?_, ?_⟩
  · intro _
    simpa only [samePhases, SourceDependencyProjection.scope_append_nil] using saved
  · simpa only [samePhases] using waiting
  · intro disposes
    have disposal := disposalPermission disposes
    obtain ⟨unprotected, closes, _⟩ := disposing_capture (checked_request checked) found disposal
    refine ⟨unprotected, closes, ?_⟩
    rw [samePhases]
    exact pending_transport (checked_request_schedule checked found disposal)
      (fun _ ready => ready) permissions (List.Subset.refl _)

/-- The uniform scheme and fresh insertion now produce the checked clause
body and retained live forest from pre-capture source checks. The actual rich
source/store allocation join is still a separate integration obligation. -/
theorem allocate_checked_clause
    (scheme : ClauseFamily outward rights family)
    (checked : Checked outward actions phases world (.request effect operation) (captured.append tail))
    (retained : Retained outward actions phases world (captured.append tail) .nil)
    (found : select effect operation (captured.append tail) = some (.handler captured tail contract modes))
    (disposalPermission : rights.dispose = true → contract.dispose = true)
    (fresh : actions owner = none) (consumed : phases owner = .consumed) :
    Checked outward (actions.insert owner rights) (OwnerPhaseTransitions.introduce phases owner)
      world (family owner) (.live owner captured tail) ∧
    Retained outward (actions.insert owner rights) (OwnerPhaseTransitions.introduce phases owner)
      world (.live owner captured tail) .nil := by
  have source := capture_source_from_request checked retained found disposalPermission fresh consumed
  constructor
  · exact scheme.instantiate (by simp [Syntax.UsageTickets.insert])
      (by simp [OwnerPhaseTransitions.introduce]) source
  · exact pending_transport (retained_capture retained) introduce_extends
      (Syntax.fresh_usage_insert_extends fresh) (List.Subset.refl _)

/-- Unavailable modes carry no family. Available modes carry the uniform
check for the actual clause body's independently computed action permissions. -/
inductive ModeScheme (outward : List Instance) (rights : Syntax.OneShotRights) :
    Option (Nat → Dependencies) → Prop where
  | unavailable : ModeScheme outward rights none
  | available (scheme : ClauseFamily outward rights family) : ModeScheme outward rights (some family)

inductive DeclarationSchemes (outward : List Instance) :
    Clauses → SourceDependencyAnnotations.ClauseDependencies → Prop where
  | nil : DeclarationSchemes outward .nil []
  | cons (ordinary : ModeScheme outward body.requiredActions ordinaryFamily)
      (protectedMode : ModeScheme outward body.requiredActions protectedFamily)
      (rest : DeclarationSchemes outward clauses families) :
      DeclarationSchemes outward (.cons operation parameter binder body clauses)
        ((operation, ordinaryFamily, protectedFamily) :: families)

/-- Value substitution preserves the same certified families and their
permission indices. Ordinary source substitution separately authenticates the
unchanged dependency annotations. Both clause binders still shadow the name. -/
theorem DeclarationSchemes.substitution (schemes : DeclarationSchemes outward clauses families)
    (value : replacement.IsValue) (name : Nat) :
    DeclarationSchemes outward (clauses.subst name replacement) families := by
  induction schemes with
  | nil => exact .nil
  | cons ordinary protectedMode rest ih =>
      simp only [Clauses.subst]
      split
      · exact .cons ordinary protectedMode ih
      · exact .cons
          (by simpa only [Code.substitution_required_actions _ name value] using ordinary)
          (by simpa only [Code.substitution_required_actions _ name value] using protectedMode) ih

/-- Name instantiation preserves certification of the supplied dependency
families because required continuation actions are unchanged. This theorem
alone does not authenticate those families as source annotations of the
instantiated code; resource bodies must supply their hereditary source proof. -/
theorem DeclarationSchemes.instantiation (schemes : DeclarationSchemes outward clauses families)
    (environment : Instantiation.Environment) :
    DeclarationSchemes outward (clauses.instantiate environment) families := by
  induction schemes with
  | nil => exact .nil
  | cons ordinary protectedMode rest ih =>
      exact .cons
        (by simpa only [Code.instantiation_required_actions] using ordinary)
        (by simpa only [Code.instantiation_required_actions] using protectedMode) ih

theorem ModeScheme.selected (scheme : ModeScheme outward rights offeredFamily)
    (found : offeredFamily = some family) : ClauseFamily outward rights family := by
  subst offeredFamily
  cases scheme with | available checked => exact checked

/-- Clause lookup follows the same first-match proof as ordinary typing.
The selected family's permission index comes from that exact source clause. -/
theorem DeclarationSchemes.selected (schemes : DeclarationSchemes outward clauses families)
    (selected : ClauseAt operation clauses parameter binder code)
    (found : (lookupDependencies operation families).bind (modeDependencies held) = some family) :
    ClauseFamily outward code.requiredActions family := by
  induction selected generalizing families with
  | hit => cases schemes with
      | cons ordinary protectedMode rest =>
          simp only [lookupDependencies, if_true, Option.bind_some] at found
          cases held with
          | false => exact ordinary.selected found
          | true => exact protectedMode.selected found
  | pass different next ih => cases schemes with
      | cons ordinary protectedMode rest =>
          exact ih rest (by simpa only [lookupDependencies, if_neg different] using found)

/-- Join the existing typed-family selection theorem to the checked scheme
for the same declaration and mode. The result is uniform in fresh contracts
and admitted captured source; no independently chosen clause annotation is used. -/
theorem selected_checked_body
    (source : SourceDependencyAnnotations.Declarations operations policy contracts world environment allowed requested answer clauses table families)
    (schemes : DeclarationSchemes outward clauses families)
    (selected : ClauseAt operation clauses parameter binder code)
    (found : lookup operation table = some offered)
    (available : offered.row held = some row) :
    ∃ argument input resumeEffects closeEffects family,
      operations requested operation = some (argument, input) ∧
      (code.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.requiredActions.dispose = true → closeEffects = allowed) ∧
      (lookupDependencies operation families).bind (modeDependencies held) = some family ∧
      ClauseFamily outward code.requiredActions family ∧
      ∀ owner (contract : SourceDependencyAnnotations.Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = held → contract.closeDemand.Perm contract.resumeDemand →
        SourceDependencyAnnotations.Body operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (environment.extend parameter argument) code answer ⟨owner, contract.erase, offered.dispose, row⟩ (family owner) := by
  obtain ⟨argument, input, resumeEffects, closeEffects, family, signature, resume, close, located, body⟩ :=
    selected_body source selected found available
  exact ⟨argument, input, resumeEffects, closeEffects, family, signature, resume, close, located,
    schemes.selected selected located, body⟩

/-- Capture preparation for an actual declared clause. Existing declaration
selection supplies the same typed family, and ClauseModes supplies its disposal
permission. Neither compatibility nor a separately checked clause is assumed. -/
theorem allocate_declared_clause
    (source : SourceDependencyAnnotations.Declarations operations policy contracts world environment allowed requested answer clauses table families)
    (modes : SourceTemplates.ClauseModes clauses table)
    (schemes : DeclarationSchemes outward clauses families)
    (selected : ClauseAt operation clauses parameter binder code)
    (found : lookup operation table = some offered)
    (available : offered.row captured.held = some row)
    (selection : select requested operation (captured.append tail) = chosen operation table families captured tail)
    (checked : Checked outward actions phases world (.request requested operation) (captured.append tail))
    (retained : Retained outward actions phases world (captured.append tail) .nil)
    (fresh : actions owner = none) (consumed : phases owner = .consumed) :
    ∃ argument input resumeEffects closeEffects family,
      operations requested operation = some (argument, input) ∧
      (code.requiredActions.resume = true → resumeEffects = allowed) ∧
      (code.requiredActions.dispose = true → closeEffects = allowed) ∧
      (lookupDependencies operation families).bind (modeDependencies captured.held) = some family ∧
      Checked outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.introduce phases owner)
        world (family owner) (.live owner captured tail) ∧
      Retained outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.introduce phases owner)
        world (.live owner captured tail) .nil ∧
      ∀ (contract : SourceDependencyAnnotations.Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = captured.held → contract.closeDemand.Perm contract.resumeDemand →
        SourceDependencyAnnotations.Body operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (environment.extend parameter argument) code answer ⟨owner, contract.erase, offered.dispose, row⟩ (family owner) := by
  obtain ⟨argument, input, resumeEffects, closeEffects, family, signature, resume, close, located, scheme, body⟩ :=
    selected_checked_body source schemes selected found available
  obtain ⟨contract, actual, disposalPermission⟩ := SourceTemplates.selected_clause_mode selected modes
  cases Option.some.inj (found.symm.trans actual)
  cases familyFound : lookupDependencies operation families with
  | none => simp [familyFound] at located
  | some alternatives =>
      have exactSelection : select requested operation (captured.append tail) =
          some (.handler captured tail offered alternatives) := by
        simpa only [chosen, found, familyFound] using selection
      obtain ⟨clauseChecked, liveRetained⟩ := allocate_checked_clause scheme checked retained exactSelection disposalPermission fresh consumed
      exact ⟨argument, input, resumeEffects, closeEffects, family, signature, resume, close, by simpa only [familyFound] using located,
        clauseChecked, liveRetained, body owner⟩

/-- Checked current source recovers the real resume transition and the
retained-source judgment for its result. Physical realization keeps spent
markers; only the checking view projects them away. -/
theorem resume_source_step
    (realized : Realizes tables families receiving stack)
    (checked : Checked outward actions phases world (.invoke ⟨owner, .resume⟩) receiving)
    (resolved : caller.resolve binder = some owner) (closed : ClosedValue value) :
    ∃ afterScope afterStack,
      RawStep ⟨.resume binder value, caller, stack⟩ ⟨value, caller, afterStack⟩ [] [.ticket owner] ∧
      Realizes tables families afterScope afterStack ∧
      Retained outward actions (spend phases owner) world afterScope .nil := by
  obtain ⟨after, computed, retained⟩ := checked_resume checked
  obtain ⟨afterStack, step, source⟩ := checked_resume_step realized computed resolved closed
  exact ⟨after, afterStack, step, source, retained⟩

/-- Scheduled callback checking and existing exact owner accounting describe
the same disposal transition and plan. This is not the full ownership invariant. -/
theorem dispose_source_step
    (realized : Realizes tables families receiving stack)
    (checked : Checked outward actions phases world (.invoke ⟨owner, .dispose⟩) receiving)
    (resolved : caller.resolve binder = some owner) :
    ∃ afterScope afterStack captured plan,
      RawStep ⟨.discard binder, caller, stack⟩ ⟨.unit, caller, afterStack⟩ [.close closeId] [.ticket owner] ∧
      Realizes tables families afterScope afterStack ∧
      Retained outward actions (spend phases owner) world afterScope .nil ∧
      makePlan captured = some plan ∧ (planOwners (plan.map CloseEntry.erase)).Perm captured.erase.owners := by
  obtain ⟨after, computed, retained⟩ := checked_dispose checked
  obtain ⟨afterStack, captured, plan, step, source, built, accounting⟩ := checked_dispose_step realized computed resolved
  exact ⟨after, afterStack, captured, plan, step, source, retained, built, accounting⟩

namespace Stored

/-- Only an actual handler frame introduces a declaration-certificate
obligation. Certificates refer to its own clauses and its own family registry
entry, including when that frame lies in a dormant capture. -/
inductive Frame (outward : List Instance) (families : SourceDependencyCapture.Families) : ExecFrame → Prop where
  | plain : Frame outward families (.plain data)
  | handler (declarations : DeclarationSchemes outward data.clauses (families data)) : Frame outward families (.handler data)
  | cell : Frame outward families (.cell identity payload scope answer)
  | armed : Frame outward families (.armed data)
  | running : Frame outward families (.running data saved closed)
  | closing : Frame outward families (.closing identity scope)
  | retiring : Frame outward families (.retiring owner)

inductive Forest (outward : List Instance) (families : SourceDependencyCapture.Families) : Stack → Prop where
  | nil : Forest outward families .nil
  | push (frame : Frame outward families entry) (tail : Forest outward families rest) :
      Forest outward families (.push entry rest)
  | live (saved : Forest outward families captured) (tail : Forest outward families rest) :
      Forest outward families (.live owner input answer captured caller rest)
  | spent (tail : Forest outward families rest) : Forest outward families (.spent owner answer caller rest)

/-- Splitting the active spine retains the whole dormant branch at each live
boundary. The proof is independent of the size or nesting depth of captures. -/
theorem Forest.append_iff : Forest outward families (first.append second) ↔
    Forest outward families first ∧ Forest outward families second := by
  induction first with
  | nil => exact ⟨fun source => ⟨.nil, source⟩, fun source => source.2⟩
  | push entry rest ih =>
      constructor
      · intro source; cases source with
        | push frame tail => obtain ⟨inside, outside⟩ := ih.mp tail; exact ⟨.push frame inside, outside⟩
      · intro ⟨inside, outside⟩; cases inside with
        | push frame tail => exact .push frame (ih.mpr ⟨tail, outside⟩)
  | live owner input answer captured caller rest ihCaptured ihRest =>
      constructor
      · intro source; cases source with
        | live saved tail => obtain ⟨inside, outside⟩ := ihRest.mp tail; exact ⟨.live saved inside, outside⟩
      · intro ⟨inside, outside⟩; cases inside with
        | live saved tail => exact .live saved (ihRest.mpr ⟨tail, outside⟩)
  | spent owner answer caller rest ih =>
      constructor
      · intro source; cases source with
        | spent tail => obtain ⟨inside, outside⟩ := ih.mp tail; exact ⟨.spent inside, outside⟩
      · intro ⟨inside, outside⟩; cases inside with
        | spent tail => exact .spent (ih.mpr ⟨tail, outside⟩)

/-- The existing exact runtime cut selects a certified declaration from that
same handler and preserves certificates on both resulting forests. -/
theorem Forest.cut (cut : HandlerCut requested whole captured tail handler)
    (source : Forest outward families whole) :
    Forest outward families captured ∧ Forest outward families tail ∧
      DeclarationSchemes outward handler.clauses (families handler) := by
  induction cut with
  | hit handler tail same => cases source with
      | push frame tail => cases frame with
          | handler declarations => exact ⟨.push (.handler declarations) .nil, tail, declarations⟩
  | push entry rest captured tail handler miss next ih => cases source with
      | push frame tail => obtain ⟨saved, outside, declarations⟩ := ih tail; exact ⟨.push frame saved, outside, declarations⟩
  | live owner input answer saved caller rest captured tail handler next ih => cases source with
      | live inside tail => obtain ⟨saved, outside, declarations⟩ := ih tail; exact ⟨.live inside saved, outside, declarations⟩
  | spent owner answer caller rest captured tail handler next ih => cases source with
      | spent tail => obtain ⟨saved, outside, declarations⟩ := ih tail; exact ⟨.spent saved, outside, declarations⟩

theorem Forest.capture (cut : HandlerCut requested whole captured tail handler)
    (source : Forest outward families whole) :
    Forest outward families (.live owner input answer captured caller tail) :=
  .live (source.cut cut).1 (source.cut cut).2.1

theorem Forest.resume {front captured tail : Stack} (source : Forest outward families (front.append (.live owner input answer captured savedCaller tail))) :
    Forest outward families (captured.append (front.append (.spent owner answer caller tail))) := by
  obtain ⟨frontSource, liveSource⟩ := Forest.append_iff.mp source
  cases liveSource with
  | live saved outside => exact Forest.append_iff.mpr ⟨saved, Forest.append_iff.mpr ⟨frontSource, .spent outside⟩⟩

/-- Closing plans do not contain handler frames. Checking code stored in an
armed callback is an independent source obligation, not discharged here. -/
theorem Forest.close_control (plan : List CloseEntry) : Forest outward families (closeControl caller plan) := by
  induction plan with
  | nil => exact .nil
  | cons entry rest ih => cases entry with
      | release identity payload => exact .push .cell ih
      | invoke action => exact .push .armed ih
      | retire owner => exact .push .retiring ih

theorem Forest.dispose {front captured tail : Stack} (source : Forest outward families (front.append (.live owner input answer captured savedCaller tail)))
    (plan : List CloseEntry) :
    Forest outward families ((closeControl caller plan).append
      (.push (.closing closeId caller) (front.append (.spent owner answer caller tail)))) := by
  obtain ⟨frontSource, liveSource⟩ := Forest.append_iff.mp source
  cases liveSource with
  | live saved outside =>
      exact Forest.append_iff.mpr ⟨Forest.close_control plan, .push .closing (Forest.append_iff.mpr ⟨frontSource, .spent outside⟩)⟩

end Stored

/-- Join exact rich-source decomposition to certificates stored on actual
handler frames. The selected declaration, family, capture and pending tail all
come from the same cut; none is supplied as a separate source annotation. -/
theorem capture_checked_interfaces
    (cut : HandlerCut requested whole capture tail handler)
    (source : SourceDependencyFrames.Segment operations policy contracts tables families actions world
      whole input output demand requirements records wholeScope incoming outgoing)
    (certificates : Stored.Forest outward families whole)
    (checked : Checked outward actions phases world (.request requested operation) wholeScope)
    (retained : Retained outward actions phases world wholeScope .nil)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase) = some row)
    (operationKnown : operations requested operation = some (argument, input))
    (fresh : actions owner = none) (consumed : phases owner = .consumed) :
    ∃ (answer : SourceDependencyAnnotations.Value) (residual : List Instance) (capDemand tailDemand : List Nat)
      (capReq : RecursiveRequirements.Requirements capDemand) (tailReq : RecursiveRequirements.Requirements tailDemand)
      (capRecords tailRecords : RecursiveRequirements.Store) (capScope tailScope : Receiving)
      (resumeEffects closeEffects : List Instance) (family : Nat → Dependencies),
      answer.erase.port = ScopedPorts.eraseType handler.answer ∧
      ScopedPorts.EffectScopeKnown contracts.erase.ports handler.scope ∧
      DeclaredSourceFrames.Frame operations.erase policy contracts.erase tables world
        (.handler handler) answer.erase answer.erase [] (.request [] []) ∧
      SourceDependencyFrames.Segment operations policy contracts tables families actions world
        capture input answer capDemand capReq capRecords capScope incoming residual ∧
      SourceDependencyFrames.Segment operations policy contracts tables families actions world
        tail answer output tailDemand tailReq tailRecords tailScope residual outgoing ∧
      wholeScope = capScope.append tailScope ∧ demand = capDemand ++ tailDemand ∧ records = capRecords ++ tailRecords ∧
      (code.requiredActions.resume = true → resumeEffects = residual) ∧
      (code.requiredActions.dispose = true → closeEffects = residual) ∧
      (lookupDependencies operation (families handler)).bind (modeDependencies capScope.held) = some family ∧
      Checked outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.introduce phases owner)
        world (family owner) (.live owner capScope tailScope) ∧
      Retained outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.introduce phases owner)
        world (.live owner capScope tailScope) .nil ∧
      Stored.Forest outward families (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail) ∧
      (∀ store receiving before, RecursiveRequirements.evaluate store receiving before requirements =
        ProtectionResiduals.merge
          (RecursiveRequirements.evaluate store (OwnerPhases.ofStack tables tail ++ receiving) before capReq)
          (RecursiveRequirements.evaluate store receiving (OwnerPhaseTransitions.spendAll before capDemand) tailReq)) ∧
      ∀ (contract : SourceDependencyAnnotations.Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = capScope.held → contract.closeDemand.Perm contract.resumeDemand →
        SourceDependencyAnnotations.Body operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
          (SourceDependencyAnnotations.Environment.empty.extend parameter argument) code answer
          ⟨owner, contract.erase, offered.dispose, row⟩ (family owner) := by
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
    annotation, frame, saved, waiting, scopeSame, demandSame, recordsSame, selection, evaluation⟩ :=
    SourceDependencyFrames.capture_segments cut source
  have schemes := (certificates.cut cut).2.2
  have effectSame := ScopedTyping.handler_cut_instance cut
  have scopedCheck : Checked outward actions phases world (.request handler.effectInst operation) (capScope.append tailScope) := by
    simpa only [effectSame, ← scopeSame] using checked
  have scopedRetained : Retained outward actions phases world (capScope.append tailScope) .nil := scopeSame ▸ retained
  have scopedSelection : select handler.effectInst operation (capScope.append tailScope) =
      chosen operation (tables handler) (families handler) capScope tailScope := by
    simpa only [effectSame, ← scopeSame] using selection operation
  have scopedRow : offered.row capScope.held = some row := by simpa only [saved.realizes.held] using available
  have declaration := frame.erase.source
  cases frame with
  | handler scope annotation clauses coverage unique declarations capabilities modes =>
      obtain ⟨actualArgument, actualInput, resumeEffects, closeEffects, family, signature, resume, close, located,
        bodyChecked, liveRetained, body⟩ :=
        allocate_declared_clause declarations modes schemes selected found scopedRow scopedSelection scopedCheck scopedRetained fresh consumed
      rw [effectSame] at signature
      rcases Prod.mk.inj (Option.some.inj (signature.symm.trans operationKnown)) with ⟨rfl, rfl⟩
      exact ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
        resumeEffects, closeEffects, family, annotation, scope, declaration, saved, waiting, scopeSame, demandSame, recordsSame, resume, close, located,
        bodyChecked, liveRetained, certificates.capture cut, evaluation, body⟩


namespace Closing
open SourceDependencyAnnotations (Operations Contracts ValueSummary)
open SourceDependencyFrames (Segment)
open RecursiveRequirements (Requirements)
open OwnerClosingSource (retirements)

/-- An actual prefix without this owned ticket cannot intercept its scope
lookup. Retiring frames count as owners even though lookup skips them. -/
theorem prefix_owner_cut (realized : Realizes tables families frontScope front)
    (absent : owner ∉ ownedTickets front) :
    OwnerCut owner (frontScope.append (.live owner captured tail)) ⟨frontScope, captured, tail⟩ := by
  induction realized with
  | nil => exact .hit
  | push frame rest ih => cases frame with
      | plain => exact .plain (ih absent)
      | handler => exact .handler (ih absent)
      | cell => exact .cell (ih absent)
      | cleanup => exact .cleanup (ih absent)
      | running | unwinding | closing => exact .running (ih absent)
      | retiring => exact .running (ih (fun member => absent (List.mem_cons_of_mem _ member)))
  | @live savedScope saved restScope rest other input answer caller inside outside ihInside ihOutside =>
      apply OwnerCut.live (selected := ⟨restScope, captured, tail⟩)
      · intro same; subst other; exact absent List.mem_cons_self
      · exact ihOutside (fun member => absent (List.mem_cons_of_mem _ (List.mem_append_right _ member)))
  | spent rest ih => exact .spent (ih absent)

theorem Bound.selected {selected : OwnerSelection} (source : Bound annotations receiving) (cut : OwnerCut owner receiving selected) :
    annotations owner = some selected.captured := by
  induction cut with
  | hit => cases source with | live recorded saved rest => exact recorded
  | plain next ih => cases source with | plain rest => exact ih rest
  | handler next ih => cases source with | handler rest => exact ih rest
  | cell next ih => cases source with | cell rest => exact ih rest
  | cleanup next ih => cases source with | cleanup rest => exact ih rest
  | running next ih => cases source with | running rest => exact ih rest
  | live different next ih => cases source with | live recorded saved rest => exact ih rest
  | spent next ih => cases source with | spent rest => exact ih rest

theorem Bound.transport (source : Bound before receiving)
    (extension : ∀ owner captured, before owner = some captured → after owner = some captured) :
    Bound after receiving := by
  induction source with
  | nil => exact .nil
  | plain rest ih => exact .plain ih
  | handler rest ih => exact .handler ih
  | cell rest ih => exact .cell ih
  | cleanup rest ih => exact .cleanup ih
  | running rest ih => exact .running ih
  | live recorded saved rest ihSaved ihRest => exact .live (extension _ _ recorded) ihSaved ihRest
  | spent rest ih => exact .spent ih

/-- Fresh capture records its actual annotation while preserving all previous
live-boundary annotations. -/
theorem Bound.capture (saved : Bound annotations captured) (waiting : Bound annotations tail)
    (fresh : annotations owner = none) :
    Bound (fun other => if other = owner then some captured else annotations other) (.live owner captured tail) := by
  have extension : ∀ other scope, annotations other = some scope →
      (if other = owner then some captured else annotations other) = some scope := by
    intro other scope known
    by_cases same : other = owner
    · subst other; rw [fresh] at known; cases known
    · simpa only [if_neg same] using known
  exact .live (by simp) (saved.transport extension) (waiting.transport extension)

theorem Bound.append_iff : Bound annotations (first.append second) ↔
    Bound annotations first ∧ Bound annotations second := by
  induction first with
  | nil => exact ⟨fun source => ⟨.nil, source⟩, fun source => source.2⟩
  | plain dependencies rest ih =>
      constructor
      · intro source; cases source with | plain rest => obtain ⟨a, b⟩ := ih.mp rest; exact ⟨.plain a, b⟩
      · intro ⟨a, b⟩; cases a with | plain rest => exact .plain (ih.mpr ⟨rest, b⟩)
  | handler effect table families rest ih =>
      constructor
      · intro source; cases source with | handler rest => obtain ⟨a, b⟩ := ih.mp rest; exact ⟨.handler a, b⟩
      · intro ⟨a, b⟩; cases a with | handler rest => exact .handler (ih.mpr ⟨rest, b⟩)
  | cell identity rest ih =>
      constructor
      · intro source; cases source with | cell rest => obtain ⟨a, b⟩ := ih.mp rest; exact ⟨.cell a, b⟩
      · intro ⟨a, b⟩; cases a with | cell rest => exact .cell (ih.mpr ⟨rest, b⟩)
  | cleanup needs dependencies rest ih =>
      constructor
      · intro source; cases source with | cleanup rest => obtain ⟨a, b⟩ := ih.mp rest; exact ⟨.cleanup a, b⟩
      · intro ⟨a, b⟩; cases a with | cleanup rest => exact .cleanup (ih.mpr ⟨rest, b⟩)
  | running rest ih =>
      constructor
      · intro source; cases source with | running rest => obtain ⟨a, b⟩ := ih.mp rest; exact ⟨.running a, b⟩
      · intro ⟨a, b⟩; cases a with | running rest => exact .running (ih.mpr ⟨rest, b⟩)
  | live owner captured rest ihCaptured ihRest =>
      constructor
      · intro source; cases source with
        | live recorded saved rest => obtain ⟨a, b⟩ := ihRest.mp rest; exact ⟨.live recorded saved a, b⟩
      · intro ⟨a, b⟩; cases a with | live recorded saved rest => exact .live recorded saved (ihRest.mpr ⟨rest, b⟩)
  | spent owner rest ih =>
      constructor
      · intro source; cases source with | spent rest => obtain ⟨a, b⟩ := ih.mp rest; exact ⟨.spent a, b⟩
      · intro ⟨a, b⟩; cases a with | spent rest => exact .spent (ih.mpr ⟨rest, b⟩)

/-- Closing replaces every live capture by its materialized plan, so it
introduces no live-boundary annotation obligations. -/
theorem Bound.forClosing (receiving : Receiving) : Bound annotations receiving.forClosing := by
  induction receiving with
  | nil => exact .nil
  | plain _ _ ih | handler _ _ _ _ ih | spent _ _ ih => exact ih
  | cell _ _ ih => exact .cell ih
  | cleanup _ _ _ ih => exact .cleanup ih
  | running _ ih => exact .running ih
  | live _ _ _ inside outside => exact Bound.append_iff.mpr ⟨inside, .running outside⟩

theorem Bound.invocations {selected : OwnerSelection} (source : Bound annotations receiving) (cut : OwnerCut owner receiving selected) :
    Bound annotations (selected.resumed owner) ∧ Bound annotations (selected.disposed owner) := by
  rw [cut.reconstruct] at source
  obtain ⟨front, boundary⟩ := Bound.append_iff.mp source
  cases boundary with
  | live recorded saved tail =>
      have waiting := Bound.append_iff.mpr ⟨front, Bound.spent (owner := owner) tail⟩
      exact ⟨Bound.append_iff.mpr ⟨saved, waiting⟩,
        Bound.append_iff.mpr ⟨Bound.forClosing _, .running waiting⟩⟩

/-- The template's recorded annotation is the one checked by disposal in the
actual receiving scope, not another valid annotation of the same source code. -/
theorem Bound.disposal (source : Bound annotations receiving)
    (checked : Checked outward actions phases world (.invoke ⟨owner, .dispose⟩) receiving)
    (recorded : annotations owner = some captured) :
    ∃ selected, findOwner owner receiving = some selected ∧
      Bound annotations (selected.disposed owner) ∧
      Retained outward actions (spend phases owner) world
        (captured.forClosing.append (.running (selected.front.append (.spent owner selected.tail)))) .nil := by
  obtain ⟨after, computed, retained⟩ := checked_dispose checked
  cases check_dispose_iff.mp computed with
  | checked cut known permitted active unprotected closing =>
      have same := Option.some.inj (recorded.symm.trans (source.selected cut))
      refine ⟨_, cut.lookup, (source.invocations cut).2, ?_⟩
      simpa only [OwnerSelection.disposed, same] using retained

/-- The actual plan retains each callback's enriched source and dependency
annotation. This is structural source evidence, not a future-run premise. -/
inductive Contents (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Contracts) (world : List Nat) : List CloseEntry → Receiving → Prop where
  | nil : Contents operations policy contracts world [] .nil
  | release (rest : Contents operations policy contracts world tail receiving) :
      Contents operations policy contracts world (.release identity payload :: tail) (.cell identity receiving)
  | retire (known : contracts owner = some contract)
      (rest : Contents operations policy contracts world tail receiving) :
      Contents operations policy contracts world (.retire owner :: tail) (.running receiving)
  | invoke (callback : ValueSummary operations policy contracts world SourceDependencyAnnotations.Environment.empty []
      action.action (.function .unit .unit action.requests latent dependencies))
      (rest : Contents operations policy contracts world tail receiving) :
      Contents operations policy contracts world (.invoke action :: tail) (.cleanup action.requests dependencies receiving)

theorem Contents.append (first : Contents operations policy contracts world before a)
    (second : Contents operations policy contracts world after b) :
    Contents operations policy contracts world (before ++ after) (a.append b) := by
  induction first with
  | nil => exact second
  | release rest ih => exact .release ih
  | retire known rest ih => exact .retire known ih
  | invoke callback rest ih => exact .invoke callback ih

/-- Extract the same scheduled callbacks from the rich captured derivation,
including callbacks inside dormant one-shot captures. -/
theorem plan_contents
    (source : Segment operations policy contracts tables families actions world capture input output
      demand requirements records receiving incoming outgoing)
    (built : makePlan capture = some plan) :
    Contents operations policy contracts world plan receiving.forClosing := by
  induction capture generalizing input output demand requirements records receiving incoming outgoing plan with
  | nil => cases source; cases built; exact .nil
  | push frame rest ih => cases source with
      | push head tail bound => cases head with
          | plain => simpa only [Scope.forClosing] using ih tail built
          | handler => simpa only [Scope.forClosing] using ih tail built
          | cell =>
              cases next : makePlan rest <;> simp [makePlan, next] at built
              case some suffix => subst plan; exact .release (ih tail next)
          | armed scope callback annotation interface =>
              cases next : makePlan rest <;> simp [makePlan, next] at built
              case some suffix => subst plan; exact .invoke callback (ih tail next)
          | running | closing | retiring => simp [makePlan] at built
  | live owner inputType answerType saved scope rest ihSaved ihRest => cases source with
      | live known actionKnown inputAnnotation answerAnnotation scopeKnown held captured savedBound tail resume close bound =>
          cases inside : makePlan saved <;> cases outside : makePlan rest <;> simp [makePlan, inside, outside] at built
          case some.some first second =>
            subst plan
            exact (ihSaved captured inside).append (.retire known (ihRest tail outside))
  | spent owner answer scope rest ih => cases source with
      | spent known annotation scopeKnown tail bound => simpa only [Scope.forClosing] using ih tail built

/-- Keep the existing closing requirement indices while retaining the richer
callback source. A selected store record fixes these indices before execution. -/
inductive Template (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (world : List Nat) (caller : Execution.Scope) :
    (plan : List CloseEntry) → Footprint → Requirements (retirements plan) → Receiving → Prop where
  | nil : Template operations policy contracts tables world caller [] [] (.request [] []) .nil
  | release (rest : Template operations policy contracts tables world caller tail raw requirements receiving) :
      Template operations policy contracts tables world caller (.release identity payload :: tail) raw
        (.sequence ((Requirements.request [] []).prepend (OwnerPhases.ofStack tables (closeControl caller tail))) requirements)
        (.cell identity receiving)
  | retire (known : contracts owner = some contract)
      (rest : Template operations policy contracts tables world caller tail raw requirements receiving) :
      Template operations policy contracts tables world caller (.retire owner :: tail) raw
        (.sequence (.retire owner) requirements) (.running receiving)
  | invoke (callback : ValueSummary operations policy contracts world SourceDependencyAnnotations.Environment.empty []
      action.action (.function .unit .unit action.requests latent dependencies))
      (rest : Template operations policy contracts tables world caller tail raw requirements receiving) :
      Template operations policy contracts tables world caller (.invoke action :: tail)
        (DisposalProtection.callbackResidual tail latent ++ raw)
        (.sequence ((Requirements.request [] (qualify true latent)).prepend (OwnerPhases.ofStack tables (closeControl caller tail))) requirements)
        (.cleanup action.requests dependencies receiving)

theorem Template.erase (source : Template operations policy contracts tables world caller plan raw requirements receiving) :
    DeclaredSourceClosing.PlanTemplate operations.erase policy contracts.erase tables world caller plan raw requirements := by
  induction source with
  | nil => exact .nil
  | release rest ih => exact .release ih
  | retire known rest ih => exact .retire (SourceDependencyAnnotations.contract_erase_known known) ih
  | invoke callback rest ih => exact .invoke (SourceDependencyFrames.value_erase callback) ih

/-- A closed plan's retained providers cover every callback effect. The lambda
rule connects those effects to its latent footprint, so filtering through the
same suffix leaves no outward closing demands. -/
theorem Template.empty_raw
    (source : Template operations policy contracts tables world caller plan raw requirements receiving)
    (typed : ScopedPorts.PlanTyped operations.erase.ports world [] plan) : raw = [] := by
  induction source with
  | nil => rfl
  | release rest ih => cases typed with | release next => exact ih next
  | retire known rest ih => cases typed with | retire next => exact ih next
  | @invoke latent dependencies tail raw requirements receiving action callback rest ih =>
    cases typed with
    | invoke ports effects next =>
      have bounded := SourceDependencyFrames.function_latent_bound callback action.closed
      have provided : ∀ request ∈ latent, request.effect ∈ ScopedPorts.planProvides tail := by
        intro request member
        simpa only [List.append_nil] using effects (bounded request member)
      have filtered : latent.filter (fun request => decide (request.effect ∉ ScopedPorts.planProvides tail)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro request member
        simp [provided request member]
      simp only [DisposalProtection.callbackResidual, filtered, qualify, List.map_nil, List.nil_append, ih next]

theorem Template.closed_budget
    (source : Template operations policy contracts tables world caller plan raw requirements receiving)
    (typed : ScopedPorts.PlanTyped operations.erase.ports world [] plan) :
    DeclaredCallbackAdmission.checkClosing interpretations outside raw budget = true := by
  rw [source.empty_raw typed]
  simp [DeclaredCallbackAdmission.checkClosing, ProtectionResiduals.residual_empty, checkFootprint]

theorem Contents.template (contents : Contents operations policy contracts world plan receiving) :
    ∃ raw, ∃ requirements : Requirements (retirements plan),
      Template operations policy contracts tables world caller plan raw requirements receiving := by
  induction contents with
  | nil => exact ⟨[], _, .nil⟩
  | release rest ih => obtain ⟨raw, requirements, template⟩ := ih; exact ⟨raw, _, .release template⟩
  | retire known rest ih => obtain ⟨raw, requirements, template⟩ := ih; exact ⟨raw, _, .retire known template⟩
  | invoke callback rest ih => obtain ⟨raw, requirements, template⟩ := ih; exact ⟨_, _, .invoke callback template⟩

theorem Template.scope (source : Template operations policy contracts tables world first plan raw requirements receiving) :
    Template operations policy contracts tables world second plan raw requirements receiving := by
  induction source with
  | nil => exact .nil
  | release rest ih =>
      simpa only [RecursiveRecords.plan_context_scope (first := first) (second := second)] using Template.release ih
  | retire known rest ih => exact .retire known ih
  | invoke callback rest ih =>
      simpa only [RecursiveRecords.plan_context_scope (first := first) (second := second)] using Template.invoke callback ih

theorem Template.transport
    (source : Template operations policy contracts tables world caller plan raw requirements receiving)
    (extension : contracts.Extends nextContracts) (larger : world ⊆ nextWorld) :
    Template operations policy nextContracts tables nextWorld caller plan raw requirements receiving := by
  induction source with
  | nil => exact .nil
  | release rest ih => exact .release ih
  | retire known rest ih => exact .retire (extension _ _ known) ih
  | invoke callback rest ih =>
      exact .invoke (SourceDependencyAnnotations.Values.world_weaken
        (SourceDependencyAnnotations.Values.extension callback extension) larger) ih

/-- Materialization preserves the exact requirements already fixed by the
stored template, rather than choosing another typing of the same callback. -/
theorem Template.source
    (template : Template operations policy contracts tables world caller plan raw requirements receiving)
    (typed : ScopedPorts.PlanTyped operations.erase.ports world closing plan)
    (scope : ScopedPorts.EffectScopeKnown contracts.erase.ports caller) :
    Segment operations policy contracts tables families actions world (closeControl caller plan) .unit .unit
      (retirements plan) requirements [] receiving (ScopedPorts.planProvides plan ++ closing) closing := by
  have scopeTypes := ScopedPorts.effect_scope_known_has_types scope
  induction template with
  | nil => exact .nil (List.Subset.refl _)
  | release rest ih => cases typed with
      | release typed =>
          exact .push (.cell scopeTypes (by simp [ScopedPorts.eraseType, ScopedPorts.Port.resources]) rfl
            (.cell scope (by simp [ScopedPorts.eraseType, ScopedPorts.Port.resources]))) (ih typed) (List.Subset.refl _)
  | retire known rest ih => cases typed with
      | retire typed =>
          exact .push (.retiring known (.retiring (CoherentSourceTypes.Owners.ports_lookup
            (SourceDependencyAnnotations.contract_erase_known known)))) (ih typed) (List.Subset.refl _)
  | @invoke latent dependencies tail raw requirements receiving action callback rest ih => cases typed with
      | invoke callable effects typed =>
          exact .push (.armed (action := { action with scope := caller, answer := .unit }) scopeTypes callback rfl
            (.armed scope callable effects)) (ih typed) (List.Subset.refl _)

/-- Extract and materialize a template when no store entry has yet fixed it. -/
theorem Contents.source
    (contents : Contents operations policy contracts world plan receiving)
    (typed : ScopedPorts.PlanTyped operations.erase.ports world closing plan)
    (scope : ScopedPorts.EffectScopeKnown contracts.erase.ports caller) :
    ∃ raw, ∃ requirements : Requirements (retirements plan),
      DeclaredSourceClosing.PlanTemplate operations.erase policy contracts.erase tables world caller plan raw requirements ∧
      Segment operations policy contracts tables families actions world (closeControl caller plan) .unit .unit
        (retirements plan) requirements [] receiving (ScopedPorts.planProvides plan ++ closing) closing := by
  obtain ⟨raw, requirements, template⟩ := contents.template (tables := tables) (caller := caller)
  exact ⟨raw, requirements, template.erase, template.source typed scope⟩

inductive Certified (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (annotations : Nat → Option Receiving) (world : List Nat) (root : Stack) :
    RecursiveRequirements.Key → RecursiveRequirements.Template → Prop where
  | dispose (located : SourceTemplates.CapturedIn owner capture root)
      (built : makePlan capture = some plan)
      (recorded : annotations owner = some capturedScope)
      (template : Template operations policy contracts tables world .none plan raw requirements capturedScope.forClosing) :
      Certified operations policy contracts tables annotations world root ⟨owner, .dispose⟩ ⟨retirements plan, requirements⟩

/-- Finite source certificates supplement the existing disposal-store layout.
They refer to the actual captured stack and exact stored requirement body. -/
inductive Records (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (annotations : Nat → Option Receiving) (world : List Nat) (root : Stack) : RecursiveRequirements.Store → Prop where
  | nil : Records operations policy contracts tables annotations world root []
  | cons (head : Certified operations policy contracts tables annotations world root key body)
      (tail : Records operations policy contracts tables annotations world root rest) :
      Records operations policy contracts tables annotations world root ((key, body) :: rest)

theorem Records.member (records : Records operations policy contracts tables annotations world root entries)
    (member : (key, body) ∈ entries) : Certified operations policy contracts tables annotations world root key body := by
  induction records with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with same | rest
      · cases same; exact head
      · exact ih rest

theorem Records.of_members
    (certified : ∀ key body, (key, body) ∈ entries → Certified operations policy contracts tables annotations world root key body) :
    Records operations policy contracts tables annotations world root entries := by
  induction entries with
  | nil => exact .nil
  | cons entry rest ih =>
      exact .cons (certified entry.1 entry.2 List.mem_cons_self)
        (ih (fun key body member => certified key body (List.mem_cons_of_mem entry member)))

/-- Transport retained certificates without changing any stored template or
callback annotation. Capture supplies the actual location transformation. -/
theorem Records.transport
    (records : Records operations policy contracts tables annotations world root entries)
    (extension : contracts.Extends nextContracts)
    (annotationExtension : ∀ owner captured, annotations owner = some captured → nextAnnotations owner = some captured)
    (larger : world ⊆ nextWorld)
    (locations : ∀ owner captured, SourceTemplates.CapturedIn owner captured root → SourceTemplates.CapturedIn owner captured nextRoot) :
    Records operations policy nextContracts tables nextAnnotations nextWorld nextRoot entries := by
  induction records with
  | nil => exact .nil
  | cons head tail ih => cases head with
      | dispose located built recorded template =>
          exact .cons (.dispose (locations _ _ located) built (annotationExtension _ _ recorded)
            (template.transport extension larger)) ih

/-- At the actual handler cut, retain the chosen rich closing template and
allocate its recorded annotation and store entry together. Existing
layout allocation and capture-location splitting supply the ownership links. -/
theorem capture_records
    (cut : HandlerCut requested whole capture tail handler)
    (template : Template operations policy contracts tables world .none plan raw closingRequirements capturedScope.forClosing)
    (scopeSame : receiving = capturedScope.append tailScope)
    (layout : DeclaredSourceClosing.Records operations.erase policy contracts.erase tables world whole disposals)
    (records : Records operations policy contracts tables annotations world whole disposals)
    (bound : Bound annotations receiving) (fresh : annotations owner = none)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (extension : contracts.Extends nextContracts) :
    let nextAnnotations := fun other => if other = owner then some capturedScope else annotations other;
      Template operations policy nextContracts tables world .none plan raw closingRequirements capturedScope.forClosing ∧
      Bound nextAnnotations (.live owner capturedScope tailScope) ∧
      DeclaredSourceClosing.Records operations.erase policy nextContracts.erase tables world
        (.live owner inputType answerType capture caller tail)
        ((⟨owner, .dispose⟩, ⟨retirements plan, closingRequirements⟩) :: disposals) ∧
      Records operations policy nextContracts tables nextAnnotations world
        (.live owner inputType answerType capture caller tail)
        ((⟨owner, .dispose⟩, ⟨retirements plan, closingRequirements⟩) :: disposals) := by
  let nextAnnotations := fun other => if other = owner then some capturedScope else annotations other
  have annotationExtension : ∀ other captured, annotations other = some captured → nextAnnotations other = some captured := by
    intro other captured known
    by_cases same : other = owner
    · subst other; rw [fresh] at known; cases known
    · simpa only [nextAnnotations, if_neg same] using known
  have locations : ∀ other captured, SourceTemplates.CapturedIn other captured whole →
      SourceTemplates.CapturedIn other captured (.live owner inputType answerType capture caller tail) := by
    intro other captured located
    rw [handler_cut_reconstructs cut] at located
    rcases SavedCaptureIdentity.located_append.mp located with inside | outside
    · exact .saved inside
    · exact .tail outside
  have oldRecords := records.transport extension annotationExtension (List.Subset.refl _) locations
  have nextTemplate := template.transport extension (List.Subset.refl _)
  have nextLayout := DeclaredSourceClosing.capture_records_with_template cut
    (owner := owner) (input := inputType) (answer := answerType) (caller := caller)
    (DeclaredSourceClosing.records_extension layout (SourceDependencyFrames.erased_contract_extension extension))
    built internal nextTemplate.erase
  have scopedBound := scopeSame ▸ bound
  obtain ⟨savedBound, tailBound⟩ := Bound.append_iff.mp scopedBound
  exact ⟨nextTemplate,
    savedBound.capture tailBound fresh, nextLayout,
    .cons (.dispose .here built (by simp) nextTemplate) oldRecords⟩

/-- Retained records keep their rich template. The existing post-step layout
locates the surviving capture; the existing origin and uniqueness proofs show
that it is the very same capture certified before the step. -/
theorem Records.after_step
    (records : Records operations policy contracts tables annotations world before.stack entries)
    (layout : DeclaredSourceClosing.Records operations.erase policy contracts.erase tables world after.stack retained)
    (included : retained ⊆ entries)
    (step : RawStep before after created discharged)
    (old : ∀ owner, Owner.ticket owner ∉ created)
    (unique : (ownedTickets before.stack).Nodup) :
    Records operations policy contracts tables annotations world after.stack retained := by
  apply Records.of_members
  intro key body member
  have previous := records.member (included member)
  have current := DeclaredSourceClosing.records_certified layout member
  have locatedNow : ∃ capture, SourceTemplates.CapturedIn key.owner capture after.stack := by
    cases current with
    | dispose nextLocated nextBuilt internal nextTemplate => exact ⟨_, nextLocated⟩
  obtain ⟨nextCapture, nextLocated⟩ := locatedNow
  cases previous with
  | dispose located built recorded template =>
      have origin := SavedCaptureIdentity.raw_step_origin step (old _) nextLocated
      cases SourceTemplates.captured_in_unique unique located origin
      exact .dispose nextLocated built recorded template

/-- Existing lookup membership and capture uniqueness select the richer
template for the same record that the invocation checker evaluated. -/
theorem selected_template
    (source : Segment operations policy contracts tables families actions world stack input output
      demand requirements resumes receiving incoming outgoing)
    (closing : Records operations policy contracts tables annotations world stack disposals)
    (looked : RecursiveRequirements.lookup ⟨owner, .dispose⟩ (resumes ++ disposals) = some body)
    (unique : (ownedTickets stack).Nodup)
    (located : SourceTemplates.CapturedIn owner capture stack) :
    ∃ (plan : List CloseEntry) (raw : Footprint) (requirements : Requirements (retirements plan)) (capturedScope : Receiving),
      makePlan capture = some plan ∧ body = ⟨retirements plan, requirements⟩ ∧
      annotations owner = some capturedScope ∧
      Template operations policy contracts tables world .none plan raw requirements capturedScope.forClosing := by
  rcases List.mem_append.mp (SourceTemplates.lookup_member looked) with resume | disposal
  · have impossible := RecursiveRecords.resume_mode source.erase.source.erase resume
    cases impossible
  · cases closing.member disposal with
    | dispose actual built recorded template =>
        cases SourceTemplates.captured_in_unique unique actual located
        exact ⟨_, _, _, _, built, rfl, recorded, template⟩

theorem checked_plan {front capture tail : Stack}
    (source : Segment operations policy contracts tables families actions world
      (front.append (.live owner inputType answerType capture savedCaller tail)) input output
      demand requirements resumes receiving incoming outgoing)
    (closing : Records operations policy contracts tables annotations world
      (front.append (.live owner inputType answerType capture savedCaller tail)) disposals)
    (bound : Bound annotations receiving)
    (contextual : Checked outward actions phases world (.invoke ⟨owner, .dispose⟩) receiving)
    (unique : (ownedTickets (front.append (.live owner inputType answerType capture savedCaller tail))).Nodup)
    (invocation : RecursiveRequirements.Checked (resumes ++ disposals)
      (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType capture savedCaller tail)))
      (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture savedCaller tail))))
      (.invoke ⟨owner, .dispose⟩ closingDemand []) closingRow) :
    ∃ (plan : List CloseEntry) (raw : Footprint) (requirements : Requirements (retirements plan)) (capturedScope : Receiving),
      makePlan capture = some plan ∧ closingDemand = retirements plan ∧
      annotations owner = some capturedScope ∧
      Template operations policy contracts tables world .none plan raw requirements capturedScope.forClosing ∧
      (∃ selected, findOwner owner receiving = some selected ∧
        Bound annotations (selected.disposed owner) ∧
        Retained outward actions (spend phases owner) world
          (capturedScope.forClosing.append (.running (selected.front.append (.spent owner selected.tail)))) .nil) ∧
      RecursiveRequirements.Checked (resumes ++ disposals)
        (OwnerPhases.ofStack tables (front.append (.spent owner answerType savedCaller tail)))
        (spend (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture savedCaller tail)))) owner)
        requirements closingRow := by
  obtain ⟨body, selectedContext, looked, ready, selection, bodyChecked⟩ := RecursiveRequirements.checked_invocation invocation
  obtain ⟨plan, raw, requirements, capturedScope, built, sameTemplate, recorded, template⟩ :=
    selected_template source closing looked unique (RecursiveRecords.located_below front .here)
  have sameDemand := congrArg Sigma.fst sameTemplate
  change closingDemand = retirements plan at sameDemand
  subst closingDemand
  cases eq_of_heq (Sigma.mk.inj sameTemplate).2
  refine ⟨plan, raw, requirements, capturedScope, built, rfl, recorded, template, bound.disposal contextual recorded, ?_⟩
  apply RecursiveTransport.checked_transport bodyChecked (fun _ _ => rfl)
  simpa only [List.append_nil, List.nil_append] using
    (RecursiveRecomposition.normalize_replaced (front := front) (capture := capture) (tail := tail)
      (input := inputType) (answer := answerType) (caller := savedCaller) (tables := tables) (receiving := [])
      (OwnerPhaseTransitions.spend_self _ owner))

/-- Disposal recomposes the rich source and the actual ownership transition.
Closing-effect admission remains an explicit obligation. The evaluation equation
uses the old pending requirements after the selected owner is consumed. -/
theorem recompose {front capture tail : Stack}
    (source : Segment operations policy contracts tables families actions world
      (front.append (.live owner inputType answerType capture savedCaller tail)) .unit output
      demand requirements records receiving incoming outgoing)
    (closing : Records operations policy contracts tables annotations world
      (front.append (.live owner inputType answerType capture savedCaller tail)) disposals)
    (bound : Bound annotations receiving)
    (contextual : Checked outward actions (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture savedCaller tail)))) world (.invoke ⟨owner, .dispose⟩) receiving)
    (layout : DeclaredSourceClosing.Records operations.erase policy contracts.erase tables world
      (front.append (.live owner inputType answerType capture savedCaller tail)) disposals)
    (invocation : RecursiveRequirements.Checked (records ++ disposals)
      (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType capture savedCaller tail)))
      (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture savedCaller tail))))
      (.invoke ⟨owner, .dispose⟩ closingDemand []) closingRow)
    (known : contracts owner = some contract) (actionKnown : actions owner = some rights)
    (built : makePlan capture = some plan)
    (typed : ScopedPorts.PlanTyped operations.erase.ports world contract.closeEffects plan)
    (admitted : contract.closeEffects ⊆ incoming)
    (scope : ScopedPorts.EffectScopeKnown contracts.erase.ports caller)
    (resolved : caller.resolve binder = some owner)
    (unique : (ownedTickets (front.append (.live owner inputType answerType capture savedCaller tail))).Nodup) :
    let fixed := Stack.push (.closing closeId caller) (front.append (.spent owner answerType savedCaller tail))
    let restored := (closeControl caller plan).append fixed
    ∃ (closingScope waitingScope : Receiving) (raw : Footprint)
      (closingRequirements : Requirements (retirements plan))
      (combined : Requirements (retirements plan ++ demand)) (remaining remainingDisposals : RecursiveRequirements.Store),
      RawStep ⟨.discard binder, caller, front.append (.live owner inputType answerType capture savedCaller tail)⟩
        ⟨.unit, caller, restored⟩ [.close closeId] [.ticket owner] ∧
      closingDemand = retirements plan ∧
      annotations owner = some closingScope ∧
      Template operations policy contracts tables world caller plan raw closingRequirements closingScope.forClosing ∧
      (∃ selected, findOwner owner receiving = some selected ∧
        Bound annotations (selected.disposed owner) ∧
        Retained outward actions (spend (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture savedCaller tail)))) owner) world
          (closingScope.forClosing.append (.running (selected.front.append (.spent owner selected.tail)))) .nil) ∧
      RecursiveRequirements.Checked (records ++ disposals)
        (OwnerPhases.ofStack tables (front.append (.spent owner answerType savedCaller tail)))
        (spend (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture savedCaller tail)))) owner)
        closingRequirements closingRow ∧
      Segment operations policy contracts tables families actions world restored .unit output
        (retirements plan ++ demand) combined remaining
        (closingScope.forClosing.append (.running waitingScope)) [] outgoing ∧
      Bound annotations (closingScope.forClosing.append (.running waitingScope)) ∧
      Retained outward actions (OwnerPhaseTransitions.available (ownedTickets restored)) world
        (closingScope.forClosing.append (.running waitingScope)) .nil ∧
      DeclaredSourceClosing.Records operations.erase policy contracts.erase tables world restored remainingDisposals ∧
      Records operations policy contracts tables annotations world restored remainingDisposals ∧
      (ownedTickets restored).Nodup ∧
      (ownedTickets (front.append (.live owner inputType answerType capture savedCaller tail))).Perm
        (owner :: ownedTickets restored) ∧
      OwnerPhaseTransitions.Trace
        (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture savedCaller tail)))) [owner]
        (OwnerPhaseTransitions.available (ownedTickets restored)) ∧
      (∀ pendingRow,
        RecursiveRequirements.Checked (records ++ disposals) []
          (OwnerPhaseTransitions.spendAll
            (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture savedCaller tail))))
            (owner :: retirements plan)) requirements pendingRow →
        RecursiveRequirements.Checked (remaining ++ remainingDisposals) []
          (OwnerPhaseTransitions.available (ownedTickets restored)) combined (closingRow ++ pendingRow)) ∧
      ∀ store outside phases, phases owner = .consumed →
        RecursiveRequirements.evaluate store outside phases combined =
          ProtectionResiduals.merge
            (RecursiveRequirements.evaluate store (OwnerPhases.ofStack tables fixed ++ outside) phases closingRequirements)
            (RecursiveRequirements.evaluate store outside (OwnerPhaseTransitions.spendAll phases (retirements plan)) requirements) := by
  obtain ⟨capReq, capRecords, waitingReq, waitingRecords, capScope, waitingScope, capBoundary,
    saved, savedInterface, waiting, permutation, scopeSplit, waitingEvaluation⟩ := SourceDependencyFrames.extract_live source known actionKnown
  obtain ⟨selectedPlan, raw, closeReq, closingScope, selectedBuilt, sameDemand, recorded, selectedTemplate, scheduled, selectedCheck⟩ :=
    checked_plan source closing bound contextual unique invocation
  cases Option.some.inj (selectedBuilt.symm.trans built)
  obtain ⟨frontScope, tailScope, frontRealized, wholeSame, waitingSame⟩ := scopeSplit
  have prefixUnique : (ownedTickets front ++ owner :: (ownedTickets capture ++ ownedTickets tail)).Nodup := by
    simpa only [owned_tickets_append, ownedTickets] using unique
  have absent : owner ∉ ownedTickets front := fun member =>
    (List.nodup_append.mp prefixUnique).2.2 owner member owner List.mem_cons_self rfl
  have cut : OwnerCut owner receiving ⟨frontScope, capScope, tailScope⟩ := by
    rw [wholeSame]
    exact prefix_owner_cut frontRealized absent
  obtain ⟨selected, selectedFound, selectedBound, selectedRetained⟩ := scheduled
  have sameSelection := Option.some.inj (cut.lookup.symm.trans selectedFound)
  have waitingSelected : waitingScope = selected.front.append (.spent owner selected.tail) := by
    rw [← sameSelection]
    exact waitingSame
  have sameCapture : closingScope = selected.captured :=
    Option.some.inj (recorded.symm.trans (bound.selected (find_owner_sound selectedFound)))
  have boundActual : Bound annotations (closingScope.forClosing.append (.running waitingScope)) := by
    simpa only [OwnerSelection.disposed, waitingSelected, sameCapture] using selectedBound
  have retainedActual := selectedRetained
  rw [← waitingSelected] at retainedActual
  have template := selectedTemplate.scope (second := caller)
  have closingSource := template.source (families := families) (actions := actions) typed scope
  have fixedSource := Segment.push (SourceDependencyFrames.Frame.closing
    (identity := closeId) (ScopedPorts.effect_scope_known_has_types scope) (ScopedPorts.EffectFrame.closing scope))
    waiting (List.Subset.refl incoming)
  have ready := (closingSource.input_weaken (List.nil_subset _)).outgoing_weaken admitted
  obtain ⟨combined, restoredSource, evaluation⟩ := SourceDependencyFrames.segment_append ready fixedSource
  have accounting := OwnerClosingSource.discard_owned_permutation (front := front) (owner := owner)
    (inputType := inputType) (answerType := answerType) (caller := savedCaller) (tail := tail)
    (scope := caller) (closeId := closeId) built
  obtain ⟨selectedDisposals, capturedDisposals, waitingDisposals, savedLayout, waitingLayout, disposalPermutation, selectedNames⟩ :=
    DeclaredSourceClosing.split_live layout
  let initial := OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture savedCaller tail)))
  let afterPlan := OwnerPhaseTransitions.spendAll initial (owner :: retirements plan)
  have captureConsumed : ∀ other ∈ ownedTickets capture, afterPlan other = .consumed := by
    intro other member
    have scheduled := (OwnerClosingSource.retirements_capture built).mem_iff.mpr member
    simp only [afterPlan, OwnerPhaseTransitions.spendAll_at]
    exact if_pos (List.mem_cons_of_mem owner scheduled)
  have outerConsumed : afterPlan owner = .consumed := by
    simp only [afterPlan, OwnerPhaseTransitions.spendAll_at, List.mem_cons_self, if_true]
  have storePermutation := RecursiveConsumption.discard_store_permutation permutation disposalPermutation
  have removedConsumed : ∀ key body,
      (key, body) ∈ ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capReq⟩) :: (capRecords ++ selectedDisposals ++ capturedDisposals)) →
      afterPlan key.owner = .consumed := by
    intro key body member
    rcases List.mem_cons.mp member with same | rest
    · cases same; exact outerConsumed
    · rcases List.mem_append.mp rest with first | last
      · rcases List.mem_append.mp first with captured | selected
        · exact captureConsumed key.owner ((RecursiveTransport.record_owners_sublist saved.erase.source.erase).subset
            (RecursiveTransport.record_owner_member captured))
        · rw [selectedNames key body selected]; exact outerConsumed
      · exact captureConsumed key.owner ((DeclaredSourceClosing.owners_sublist savedLayout).subset
          (RecursiveTransport.record_owner_member last))
  have stores : ∀ key : RecursiveRequirements.Key, afterPlan key.owner = .available →
      RecursiveRequirements.lookup key (records ++ disposals) = RecursiveRequirements.lookup key (waitingRecords ++ waitingDisposals) := by
    intro key ready
    exact (RecursiveTransport.lookup_permuted
      (RecursiveRecords.combined_unique source.erase.source.erase (DeclaredSourceClosing.records_erase layout) unique)
      storePermutation).trans (RecursiveConsumption.lookup_drop_consumed removedConsumed ready)
  have nextLayout := DeclaredSourceClosing.records_append
    (DeclaredSourceClosing.plan_records (operations := operations.erase) (contracts := contracts.erase) (tables := tables)
      (world := world) (scope := caller) plan)
    (DeclaredSourceClosing.Records.push (frame := .closing closeId caller) waitingLayout)
  have combinedEvaluation : ∀ store outside phases, phases owner = .consumed →
      RecursiveRequirements.evaluate store outside phases combined =
        ProtectionResiduals.merge
          (RecursiveRequirements.evaluate store
            (OwnerPhases.ofStack tables (Stack.push (.closing closeId caller) (front.append (.spent owner answerType savedCaller tail))) ++ outside)
            phases closeReq)
          (RecursiveRequirements.evaluate store outside (OwnerPhaseTransitions.spendAll phases (retirements plan)) requirements) := by
    intro store outside phases consumed
    rw [evaluation]
    simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
      RecursiveRecomposition.evaluate_empty, RecursiveRecomposition.merge_empty_left,
      OwnerPhaseTransitions.spendAll]
    rw [waitingEvaluation store outside _ (RecursiveTransport.phases_spendAll_later owner consumed)]
  have transition := OwnerClosingSource.discard_phase_trace (front := front) (owner := owner)
    (inputType := inputType) (answerType := answerType) (caller := savedCaller) (tail := tail)
    (scope := caller) (closeId := closeId) built unique
  have rawStep := RawStep.discard binder owner closeId caller savedCaller inputType answerType front capture tail plan resolved built
  have retainedIncluded : waitingDisposals ⊆ disposals := by
    intro entry member
    exact disposalPermutation.mem_iff.mpr (List.mem_append_right _ member)
  have richNext := Records.after_step closing nextLayout
    (by simpa only [List.nil_append] using retainedIncluded) rawStep (fun _ => by simp) unique
  refine ⟨closingScope, waitingScope, raw, closeReq, combined, waitingRecords, waitingDisposals,
    RawStep.discard binder owner closeId caller savedCaller inputType answerType front capture tail plan resolved built,
    sameDemand, recorded, template, ⟨selected, selectedFound, selectedBound, selectedRetained⟩, selectedCheck, ?_, boundActual, ?_, ?_, ?_, (List.nodup_cons.mp (accounting.nodup unique)).2, accounting,
    transition, ?_, combinedEvaluation⟩
  · simpa only [List.nil_append] using restoredSource
  · have phases := OwnerPhaseTransitions.trace_result transition
    change OwnerPhaseTransitions.available (ownedTickets ((closeControl caller plan).append
      (.push (.closing closeId caller) (front.append (.spent owner answerType savedCaller tail))))) =
      spend (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture savedCaller tail)))) owner at phases
    rw [phases]
    exact retainedActual
  · simpa only [List.nil_append] using nextLayout
  · simpa only [List.nil_append] using richNext
  · intro pendingRow pendingCheck
    have pendingCollected := RecursiveTransport.checked_transport pendingCheck stores rfl
    have phases := OwnerPhaseTransitions.trace_result transition
    change OwnerPhaseTransitions.available (ownedTickets ((closeControl caller plan).append
      (.push (.closing closeId caller) (front.append (.spent owner answerType savedCaller tail))))) =
      spend (OwnerPhaseTransitions.available (ownedTickets (front.append (.live owner inputType answerType capture savedCaller tail)))) owner at phases
    apply RecursiveRequirements.evaluate_sound
    rw [phases, combinedEvaluation _ [] _ (OwnerPhaseTransitions.spend_self _ owner), List.append_nil,
      RecursiveConsumption.template_guard (DeclaredSourceClosing.template_erase template.erase),
      ← RecursiveConsumption.template_store (first := records ++ disposals)
        (DeclaredSourceClosing.template_erase template.erase), RecursiveRequirements.checked_complete selectedCheck]
    simp only [OwnerPhaseTransitions.spendAll] at pendingCollected
    rw [RecursiveRequirements.checked_complete pendingCollected]
    rfl

end Closing

/-- At a disposing request with an empty outward guard, actual source and
support construct the plan and an empty closing footprint. Budget checking
therefore succeeds without a supplied plan, typed-plan premise or row bound.
The owner-use condition and full capture successor are separate obligations. -/
theorem closed_capture_budget
    (cut : HandlerCut requested whole capture tail handler)
    (source : SourceDependencyFrames.Segment operations policy contracts tables families actions world
      whole input output demand requirements records wholeScope incoming outgoing)
    (checked : Checked [] actions phases world (.request requested operation) wholeScope)
    (known : lookup operation (tables handler) = some offered)
    (disposes : offered.dispose = true)
    (supported : Supported capture.erase (Admission.outsideResources capture.erase)) :
    ∃ (plan : List CloseEntry) (closingRequirements : RecursiveRequirements.Requirements (OwnerClosingSource.retirements plan))
      (capturedScope : Receiving),
      makePlan capture = some plan ∧
      ScopedPorts.PlanTyped operations.erase.ports world [] plan ∧
      Closing.Template operations policy contracts tables world .none plan [] closingRequirements capturedScope.forClosing ∧
      DeclaredCallbackAdmission.checkClosing (CallableProtectionFrames.contextOf tables tail) outside [] budget = true ∧
      (planOwners (plan.map CloseEntry.erase)).Perm capture.erase.owners := by
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
    plan, built, typed, closes, saved, waiting, sameScope, sameDemand, sameRecords, owners⟩ :=
    SourceDependencyFrames.capture_plan cut source (checked_request checked) known disposes supported
  obtain ⟨raw, closingRequirements, template⟩ :=
    (Closing.plan_contents saved built).template (tables := tables) (caller := .none)
  have empty := template.empty_raw typed
  subst raw
  exact ⟨plan, closingRequirements, capScope, built, typed, template, template.closed_budget typed, owners⟩

/-- Construct the concrete rich contract and live source segment using the
existing canonical allocation shape and checked pending computation. The
closing row is the actual template evaluation. The same saved-source derivation constructs
the captured annotation and closing records on this actual successor. -/
/- Shared allocation proof after the actual source interfaces have been
constructed. The certificate payload is transported unchanged at the same
answer, effect interfaces, dependency family, scopes and saved/waiting requirement
indices; both uniform and
contextual wrappers construct the interface premise from their stored forests.
This is proof factoring, not an additional source-admission rule. -/
theorem allocate_capture_source_from_closing_interfaces
    (cut : HandlerCut requested whole capture tail handler)
    (source : SourceDependencyFrames.Segment operations policy contracts tables families actions world
      whole input output demand requirements records wholeScope incoming outgoing)
    {certificate : SourceDependencyAnnotations.Value → List Instance → (Nat → Dependencies) →
      Receiving → Receiving → List Instance → List Instance →
      (capDemand tailDemand : List Nat) → RecursiveRequirements.Requirements capDemand →
      RecursiveRequirements.Requirements tailDemand → Prop}
    (interfaces :
    ∃ (answer : SourceDependencyAnnotations.Value) (residual : List Instance) (capDemand tailDemand : List Nat)
      (capReq : RecursiveRequirements.Requirements capDemand) (tailReq : RecursiveRequirements.Requirements tailDemand)
      (capRecords tailRecords : RecursiveRequirements.Store) (capScope tailScope : Receiving)
      (resumeEffects closeEffects : List Instance) (family : Nat → Dependencies),
      answer.erase.port = ScopedPorts.eraseType handler.answer ∧
      ScopedPorts.EffectScopeKnown contracts.erase.ports handler.scope ∧
      DeclaredSourceFrames.Frame operations.erase policy contracts.erase tables world
        (.handler handler) answer.erase answer.erase [] (.request [] []) ∧
      SourceDependencyFrames.Segment operations policy contracts tables families actions world
        capture input answer capDemand capReq capRecords capScope incoming residual ∧
      SourceDependencyFrames.Segment operations policy contracts tables families actions world
        tail answer output tailDemand tailReq tailRecords tailScope residual outgoing ∧
      wholeScope = capScope.append tailScope ∧ demand = capDemand ++ tailDemand ∧ records = capRecords ++ tailRecords ∧
      (code.requiredActions.resume = true → resumeEffects = residual) ∧
      (code.requiredActions.dispose = true → closeEffects = residual) ∧
      (lookupDependencies operation (families handler)).bind (modeDependencies capScope.held) = some family ∧
      Checked outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner)
        world (family owner) (.live owner capScope tailScope) ∧
      Retained outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner)
        world (.live owner capScope tailScope) .nil ∧
      certificate answer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq ∧
      (∀ store receiving before, RecursiveRequirements.evaluate store receiving before requirements =
        ProtectionResiduals.merge
          (RecursiveRequirements.evaluate store (OwnerPhases.ofStack tables tail ++ receiving) before capReq)
          (RecursiveRequirements.evaluate store receiving (OwnerPhaseTransitions.spendAll before capDemand) tailReq)) ∧
      ∀ (contract : SourceDependencyAnnotations.Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = capScope.held → contract.closeDemand.Perm contract.resumeDemand →
        SourceDependencyAnnotations.Body operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
          (SourceDependencyAnnotations.Environment.empty.extend parameter argument) code answer
          ⟨owner, contract.erase, offered.dispose, row⟩ (family owner))
    {closingCertificate : SourceDependencyAnnotations.Value → List Instance → (Nat → Dependencies) →
      Receiving → Receiving → List Instance → List Instance →
      (capDemand tailDemand : List Nat) → RecursiveRequirements.Requirements capDemand →
      RecursiveRequirements.Requirements tailDemand → Footprint →
      RecursiveRequirements.Requirements (OwnerClosingSource.retirements plan) → Prop}
    (closing : ∀ {answer residual capDemand capReq capRecords capScope},
      SourceDependencyFrames.Segment operations policy contracts tables families actions world
        capture input answer capDemand capReq capRecords capScope incoming residual →
      ∀ {family tailScope resumeEffects closeEffects tailDemand tailReq},
      certificate answer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq →
      ∃ raw, ∃ closingRequirements : RecursiveRequirements.Requirements (OwnerClosingSource.retirements plan),
        Closing.Template operations policy contracts tables world .none plan raw closingRequirements capScope.forClosing ∧
        closingCertificate answer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq raw closingRequirements)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase) = some row)
    (operationKnown : operations requested operation = some (argument, input))
    (payload : SourceDependencyAnnotations.ValueSummary operations policy contracts world
      SourceDependencyAnnotations.Environment.empty payloadAllowed operand argument)
    (closed : ClosedValue operand)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (layout : DeclaredSourceClosing.Records operations.erase policy contracts.erase tables world whole disposals)
    (closingRecords : Closing.Records operations policy contracts tables annotations world whole disposals)
    (annotationBound : Closing.Bound annotations wholeScope) (freshAnnotation : annotations owner = none)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (pendingCheck : RecursiveRequirements.Checked (records ++ disposals) []
      (OwnerPhaseTransitions.available (ownedTickets whole)) requirements pendingRow)
    (unique : (ownedTickets whole).Nodup)
    (requestCheck : RecursiveRequirements.Checked (records ++ disposals) (OwnerPhases.ofStack tables whole)
      (OwnerPhaseTransitions.available (ownedTickets whole))
      (.request [] [⟨requested, operation, false⟩]) requestRow) :
    ∃ (answer : SourceDependencyAnnotations.Value) (residual : List Instance) (capDemand tailDemand : List Nat)
      (capReq : RecursiveRequirements.Requirements capDemand) (tailReq : RecursiveRequirements.Requirements tailDemand)
      (capScope tailScope : Receiving) (resumeEffects closeEffects : List Instance) (family : Nat → Dependencies) (captureRow tailRow raw : Footprint)
      (closingRequirements : RecursiveRequirements.Requirements (OwnerClosingSource.retirements plan)),
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩
        ⟨code.subst parameter operand, .ticket binder owner,
          .live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail⟩ [.ticket owner] [] ∧
      ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail) =
        owner :: ownedTickets whole ∧
      (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)).Nodup ∧
      wholeScope = capScope.append tailScope ∧ demand = capDemand ++ tailDemand ∧
      Checked outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)))
        world (family owner) (.live owner capScope tailScope) ∧
      Retained outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)))
        world (.live owner capScope tailScope) .nil ∧
      certificate answer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq ∧
      closingCertificate answer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq raw closingRequirements ∧
      pendingRow = captureRow ++ tailRow ∧
      RecursiveRequirements.Checked (records ++ disposals) (OwnerPhases.ofStack tables tail)
        (OwnerPhaseTransitions.available (ownedTickets whole)) capReq captureRow ∧
      RecursiveRequirements.Checked (records ++ disposals) []
        (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets whole)) capDemand) tailReq tailRow ∧
      (OwnerClosingSource.retirements plan).Perm capDemand ∧
      let closeRow := RecursiveRequirements.evaluate [] (OwnerPhases.ofStack tables tail)
        (OwnerPhaseTransitions.available (ownedTickets whole)) closingRequirements;
      let contract : SourceDependencyAnnotations.Contract := ⟨input, answer, capScope.held,
          capDemand, captureRow, OwnerClosingSource.retirements plan, closeRow, resumeEffects, closeEffects⟩;
        SourceDependencyAnnotations.Body operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
          SourceDependencyAnnotations.Environment.empty (code.subst parameter operand) answer
          ⟨owner, contract.erase, offered.dispose, row⟩ (family owner) ∧
        SourceDependencyFrames.Segment operations policy (contracts.insert owner contract) tables families
          (actions.insert owner code.requiredActions) world
          (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)
          answer output tailDemand (.sequence (.spent owner) tailReq)
          ((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) (.live owner capScope tailScope) residual outgoing ∧
        let nextAnnotations := fun other => if other = owner then some capScope else annotations other;
        Closing.Bound nextAnnotations (.live owner capScope tailScope) ∧
          Closing.Template operations policy (contracts.insert owner contract) tables world .none
            plan raw closingRequirements capScope.forClosing ∧
          DeclaredSourceClosing.Records operations.erase policy (contracts.insert owner contract).erase tables world
            (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)
            ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩) :: disposals) ∧
          Closing.Records operations policy (contracts.insert owner contract) tables nextAnnotations world
            (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)
            ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩) :: disposals) ∧
          let store := ((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) ++
            ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩) :: disposals);
          RecursiveRequirements.Checked store (OwnerPhases.ofStack tables tail)
            (OwnerPhaseTransitions.available (ownedTickets whole)) capReq captureRow ∧
          RecursiveRequirements.Checked store []
            (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets whole)) capDemand) tailReq tailRow ∧
          RecursiveRequirements.Checked store
            (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail))
            (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)))
            (.invoke ⟨owner, .resume⟩ capDemand []) captureRow ∧
          (∀ closingRow, closeRow = some closingRow → RecursiveRequirements.Checked store
            (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail))
            (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)))
            (.invoke ⟨owner, .dispose⟩ (OwnerClosingSource.retirements plan) []) closingRow) ∧
          ((offered.dispose = true → DeclaredCallbackAdmission.checkClosing (CallableProtectionFrames.contextOf tables tail) outside
            raw (requestRow ++ captureRow) = true) →
            ∃ (clauseDemand : List Nat) (clauseRequirements : RecursiveRequirements.Requirements clauseDemand) (clauseRow : Footprint),
              SourceDependencyAnnotations.Expression operations policy (contracts.insert owner contract) world residual
                (.ticket binder owner) SourceDependencyAnnotations.Environment.empty (code.subst parameter operand)
                answer clauseDemand clauseRequirements (family owner) ∧
              RecursiveRequirements.Checked store
                (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail))
                (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)))
                clauseRequirements clauseRow ∧
              EffectBounds.Covers (requestRow ++ captureRow) clauseRow) := by
  have freshErased : contracts.erase owner = none := by
    simp [SourceDependencyAnnotations.Contracts.erase, freshContract]
  have absent := RecursiveCapture.fresh_unowned source.erase.source.erase freshErased
  have requestExport := RecursiveRequirements.checked_complete requestCheck
  simp only [RecursiveContexts.evaluate_request, OwnerSource.exportAt,
    OwnerPhaseTransitions.project_actual] at requestExport
  obtain ⟨actualOffer, advertised, offerKnown, mode, rowKnown, advertisedExport⟩ :=
    RecursiveDispatch.cut_residual cut requestExport
  have offerSame := Option.some.inj (offerKnown.symm.trans found)
  subst actualOffer
  simp only [Bool.false_or] at rowKnown
  have advertisedSame := Option.some.inj (rowKnown.symm.trans available)
  subst advertised
  have consumed : OwnerPhaseTransitions.available (ownedTickets whole) owner = .consumed := by
    simp [OwnerPhaseTransitions.available, absent]
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capRecords, tailRecords, capScope, tailScope,
    resumeEffects, closeEffects, family, annotation, scope, declaration, saved, waiting, scopeSame, demandSame, recordsSame,
    resume, close, located, clauseChecked, liveRetained, liveCertificates, evaluation, body⟩ :=
    interfaces
  have evaluated := RecursiveRequirements.checked_complete pendingCheck
  rw [evaluation] at evaluated
  obtain ⟨captureRow, tailRow, inside, outside, rowSame⟩ := PhaseRechecking.merge_split evaluated
  have savedCheck := RecursiveRequirements.evaluate_sound inside
  have tailCheck := RecursiveRequirements.evaluate_sound outside
  obtain ⟨closingRaw, closingRequirements, oldTemplate, closingEvidence⟩ := closing saved liveCertificates
  have erasedOperation : operations.erase requested operation = some (argument.erase, input.erase) := by
    simp [SourceDependencyAnnotations.Operations.erase, operationKnown]
  obtain ⟨oldContract, oldAllowed, oldClauseDemand, oldClauseReq, oldCapReq, oldTailDemand, oldTailReq, oldTailRow,
    resumeDemandSame, resumeRowSame, inputSame, closeDemandSame, closeRowSame, oldBalance, rest⟩ :=
    DeclaredSourceAllocation.allocate_selected_clause_from_split cut source.erase.source layout annotation declaration
      saved.erase.source waiting.erase.source demandSame recordsSame rowSame
      (by simpa only [List.append_nil] using savedCheck) tailCheck unique
      (show contracts.erase owner = none from by simp [SourceDependencyAnnotations.Contracts.erase, freshContract])
      selected erasedOperation found available built internal oldTemplate.erase none
  have balanced : (OwnerClosingSource.retirements plan).Perm capDemand := by
    simpa only [closeDemandSame, resumeDemandSame] using oldBalance
  have ready : ClosedExcept parameter code := by
    obtain ⟨savedTyped, tailTyped, handlerTyped⟩ := ScopedPorts.handler_cut_retains_typing cut
      (SourceTemplates.segment_ports source.erase.source.erase)
    cases handlerTyped with
    | handler scopeKnown clauses coverage unique =>
        obtain ⟨inputPort, outputPort, knownPort, bodyTyped⟩ := ScopedPorts.selected_clause_typed selected clauses
        exact ScopedPorts.typed_suffix_ready bodyTyped
  have raw := RawStep.capture requested operation parameter binder owner operand code caller whole capture tail handler
    (ScopedPorts.embedPort input.erase.port) cut selected closed ready
  refine ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capScope, tailScope,
    resumeEffects, closeEffects, family, captureRow, tailRow, closingRaw, closingRequirements, raw, RecursiveCapture.capture_owned cut,
    RecursiveCapture.capture_unique cut source.erase.source.erase unique freshErased,
    scopeSame, demandSame,
    (by simpa only [OwnerPhaseTransitions.capture_map cut] using clauseChecked),
    (by simpa only [OwnerPhaseTransitions.capture_map cut] using liveRetained),
    liveCertificates, closingEvidence, rowSame, (by simpa only [List.append_nil] using savedCheck), tailCheck, balanced, ?_⟩
  let closeRow := RecursiveRequirements.evaluate [] (OwnerPhases.ofStack tables tail)
    (OwnerPhaseTransitions.available (ownedTickets whole)) closingRequirements
  let contract : SourceDependencyAnnotations.Contract := ⟨input, answer, capScope.held,
    capDemand, captureRow, OwnerClosingSource.retirements plan, closeRow, resumeEffects, closeEffects⟩
  have extension := SourceDependencyAnnotations.insert_extends (contract := contract) contracts freshContract
  have permissions := Syntax.fresh_usage_insert_extends (rights := code.requiredActions) freshAction
  have ports := CoherentSourceTypes.Owners.port_contracts_extension (SourceDependencyFrames.erased_contract_extension extension)
  have payloadAfter := SourceDependencyAnnotations.Values.extension
    (SourceDependencyAnnotations.Values.change_allowed payload closed.1 residual) extension
  have bound := body contract freshContract rfl rfl rfl rfl rfl balanced
  have instantiated : SourceDependencyAnnotations.Body operations policy (contracts.insert owner contract)
      world residual (.ticket binder owner) SourceDependencyAnnotations.Environment.empty
      (code.subst parameter operand) answer ⟨owner, contract.erase, offered.dispose, row⟩ (family owner) := by
    cases bound with
    | typed expression rows => exact .typed (SourceDependencyAnnotations.substitution expression payloadAfter closed) rows
    | annotated expression annotation rows => exact .annotated (SourceDependencyAnnotations.substitution expression payloadAfter closed) annotation rows
  obtain ⟨template, boundAnnotations, closingLayout, richRecords⟩ :=
    Closing.capture_records cut oldTemplate scopeSame layout closingRecords annotationBound freshAnnotation built internal extension
      (inputType := ScopedPorts.embedPort input.erase.port) (answerType := handler.answer) (caller := handler.scope)
  let added : RecursiveRequirements.Store := [(⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩)]
  have keys : ∀ key body, (key, body) ∈ added → key.owner = owner ∧ key.mode = .dispose := by
    intro key body member
    cases List.mem_singleton.mp member
    exact ⟨rfl, rfl⟩
  have savedAfter := RecursiveCapture.checked_insert_consumed
    (RecursiveAllocation.checked_add_closing savedCheck consumed keys) consumed
      (mode := .resume) (body := ⟨capDemand, capReq⟩)
  have laterConsumed := RecursiveTransport.phases_spendAll_later (owners := capDemand) owner consumed
  have tailAfter := RecursiveCapture.checked_insert_consumed
    (RecursiveAllocation.checked_add_closing tailCheck laterConsumed keys) laterConsumed
      (mode := .resume) (body := ⟨capDemand, capReq⟩)
  have phaseSame := RecursiveCapture.capture_phase_consumed (input := ScopedPorts.embedPort input.erase.port) cut absent
  have resumeChecked := RecursiveClauses.fresh_resume_check
    (by simpa only [List.append_nil] using savedAfter) phaseSame
  have afterUnique := RecursiveCapture.capture_unique (inputType := ScopedPorts.embedPort input.erase.port)
    cut source.erase.source.erase unique freshErased
  let store : RecursiveRequirements.Store := ((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) ++
    ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩) :: disposals)
  let afterPhases := OwnerPhaseTransitions.available (ownedTickets
    (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail))
  have disposeChecked : ∀ closingRow, closeRow = some closingRow → RecursiveRequirements.Checked store
      (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail))
      afterPhases (.invoke ⟨owner, .dispose⟩ (OwnerClosingSource.retirements plan) []) closingRow := by
    intro closingRow evaluated
    refine RecursiveDisposalCapture.closing_invocation_from_record
      (DeclaredSourceClosing.template_erase template.erase) ?_ afterUnique built ?_
    · rw [RecursiveDisposalCapture.lookup_after_resumes]
      · simp [RecursiveRequirements.lookup]
      · intro key body member
        rcases List.mem_cons.mp member with same | old
        · cases same; rfl
        · exact RecursiveRecords.resume_mode source.erase.source.erase old
    · simpa only [phaseSame] using evaluated
  have boundary : SourceDependencyFrames.Segment operations policy (contracts.insert owner contract) tables families
      (actions.insert owner code.requiredActions) world
      (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)
      answer output tailDemand (.sequence (.spent owner) tailReq)
      ((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) (.live owner capScope tailScope) residual outgoing := by
    rw [recordsSame]
    have known : (contracts.insert owner contract) owner = some contract := by simp [SourceDependencyAnnotations.Contracts.insert]
    have actionKnown : (actions.insert owner code.requiredActions) owner = some code.requiredActions := by simp [Syntax.UsageTickets.insert]
    exact SourceDependencyFrames.Segment.live known actionKnown
      (ScopedPorts.erase_embed_port input.erase.port).symm annotation
      (ScopedPorts.effect_scope_known_extension scope ports) saved.realizes.held
      ((saved.input_weaken (List.nil_subset _)).transport extension permissions (List.Subset.refl _))
      (fun used => by simpa only [contract, resume used] using List.Subset.refl residual)
      (waiting.transport extension permissions (List.Subset.refl _))
      (fun used => by simpa only [contract, resume used] using List.Subset.refl residual)
      (fun used => by simpa only [contract, close used] using List.Subset.refl residual)
      (List.Subset.refl _)

  refine ⟨instantiated, boundary, boundAnnotations, template, closingLayout, richRecords,
    (by simpa only [added, List.cons_append, List.nil_append, List.append_nil] using savedAfter), tailAfter, resumeChecked, disposeChecked, ?_⟩
  · intro closingAccepted
    have closingFacts : offered.dispose = true → ∃ closingRow,
        closeRow = some closingRow ∧ EffectBounds.Covers (requestRow ++ captureRow) closingRow := by
      intro permitted
      obtain ⟨actualClosingRow, closingEvaluated, closingAllowed, closingCovered, callbackAllowed⟩ :=
        DeclaredCallbackAdmission.checked_template template.erase built afterUnique (closingAccepted permitted) (store := [])
      exact ⟨actualClosingRow, by simpa only [phaseSame] using closingEvaluated, closingCovered⟩
    have closeAvailable : offered.dispose = true → ∃ closingRow, closeRow = some closingRow := by
      intro permitted
      obtain ⟨closingRow, same, covered⟩ := closingFacts permitted
      exact ⟨closingRow, same⟩
    have closeCovered : offered.dispose = true → ∀ closingRow, closeRow = some closingRow →
        EffectBounds.Covers (requestRow ++ captureRow) closingRow := by
      intro permitted closingRow same
      obtain ⟨actual, found, covered⟩ := closingFacts permitted
      cases Option.some.inj (found.symm.trans same)
      exact covered
    have callerReady : ∀ other ∈ activeTickets tail, afterPhases other = .available := by
      intro other member
      apply if_pos
      exact List.mem_cons.mpr (Or.inr (List.mem_append_right _ (active_tickets_owned tail member)))
    have exported : OwnerSource.exportAt (OwnerPhases.ofStack tables tail) afterPhases row = some requestRow :=
      (RecursivePlanAdmission.caller_export callerReady).trans advertisedExport
    have interface : ClauseRowAdmission.Interface owner contract.erase offered.dispose store
        (OwnerPhases.ofStack tables tail) afterPhases requestRow := by
      refine ⟨?_, ?_, closeAvailable, closeCovered, OwnerPhaseTransitions.capture_tail_fresh cut absent⟩
      · simpa only [store, added, List.cons_append, List.nil_append, afterPhases, OwnerPhases.ofStack, contract, SourceDependencyAnnotations.Contract.erase, saved.realizes.held] using resumeChecked
      · intro _ closingRow same
        simpa only [OwnerPhases.ofStack, contract, SourceDependencyAnnotations.Contract.erase, saved.realizes.held] using disposeChecked closingRow same
    obtain ⟨_, _, expression, rows⟩ := instantiated.normal_rows
    obtain ⟨clauseRow, checkedClause, covered⟩ := rows.instantiate interface exported
      (ClauseRowAdmission.SourceStore.of_source boundary.erase.source.erase
        (DeclaredSourceClosing.records_erase closingLayout) (by simp [SourceDependencyAnnotations.Contracts.erase, SourceDependencyAnnotations.Contracts.insert]))
    refine ⟨_, _, clauseRow, expression, ?_, covered⟩
    simpa only [OwnerPhases.ofStack, contract, SourceDependencyAnnotations.Contract.erase, saved.realizes.held] using checkedClause

/-- The earlier interface constructs its closing template from retained source and reuses the shared allocation proof. -/
theorem allocate_capture_source_from_interfaces
    (cut : HandlerCut requested whole capture tail handler)
    (source : SourceDependencyFrames.Segment operations policy contracts tables families actions world
      whole input output demand requirements records wholeScope incoming outgoing)
    {certificate : SourceDependencyAnnotations.Value → List Instance → (Nat → Dependencies) →
      Receiving → Receiving → List Instance → List Instance →
      (capDemand tailDemand : List Nat) → RecursiveRequirements.Requirements capDemand →
      RecursiveRequirements.Requirements tailDemand → Prop}
    (interfaces :
    ∃ (answer : SourceDependencyAnnotations.Value) (residual : List Instance) (capDemand tailDemand : List Nat)
      (capReq : RecursiveRequirements.Requirements capDemand) (tailReq : RecursiveRequirements.Requirements tailDemand)
      (capRecords tailRecords : RecursiveRequirements.Store) (capScope tailScope : Receiving)
      (resumeEffects closeEffects : List Instance) (family : Nat → Dependencies),
      answer.erase.port = ScopedPorts.eraseType handler.answer ∧
      ScopedPorts.EffectScopeKnown contracts.erase.ports handler.scope ∧
      DeclaredSourceFrames.Frame operations.erase policy contracts.erase tables world
        (.handler handler) answer.erase answer.erase [] (.request [] []) ∧
      SourceDependencyFrames.Segment operations policy contracts tables families actions world
        capture input answer capDemand capReq capRecords capScope incoming residual ∧
      SourceDependencyFrames.Segment operations policy contracts tables families actions world
        tail answer output tailDemand tailReq tailRecords tailScope residual outgoing ∧
      wholeScope = capScope.append tailScope ∧ demand = capDemand ++ tailDemand ∧ records = capRecords ++ tailRecords ∧
      (code.requiredActions.resume = true → resumeEffects = residual) ∧
      (code.requiredActions.dispose = true → closeEffects = residual) ∧
      (lookupDependencies operation (families handler)).bind (modeDependencies capScope.held) = some family ∧
      Checked outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner)
        world (family owner) (.live owner capScope tailScope) ∧
      Retained outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.introduce (OwnerPhaseTransitions.available (ownedTickets whole)) owner)
        world (.live owner capScope tailScope) .nil ∧
      certificate answer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq ∧
      (∀ store receiving before, RecursiveRequirements.evaluate store receiving before requirements =
        ProtectionResiduals.merge
          (RecursiveRequirements.evaluate store (OwnerPhases.ofStack tables tail ++ receiving) before capReq)
          (RecursiveRequirements.evaluate store receiving (OwnerPhaseTransitions.spendAll before capDemand) tailReq)) ∧
      ∀ (contract : SourceDependencyAnnotations.Contract), contracts owner = none →
        contract.input = input → contract.answer = answer →
        contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
        contract.held = capScope.held → contract.closeDemand.Perm contract.resumeDemand →
        SourceDependencyAnnotations.Body operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
          (SourceDependencyAnnotations.Environment.empty.extend parameter argument) code answer
          ⟨owner, contract.erase, offered.dispose, row⟩ (family owner))
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase) = some row)
    (operationKnown : operations requested operation = some (argument, input))
    (payload : SourceDependencyAnnotations.ValueSummary operations policy contracts world
      SourceDependencyAnnotations.Environment.empty payloadAllowed operand argument)
    (closed : ClosedValue operand)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (layout : DeclaredSourceClosing.Records operations.erase policy contracts.erase tables world whole disposals)
    (closingRecords : Closing.Records operations policy contracts tables annotations world whole disposals)
    (annotationBound : Closing.Bound annotations wholeScope) (freshAnnotation : annotations owner = none)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (pendingCheck : RecursiveRequirements.Checked (records ++ disposals) []
      (OwnerPhaseTransitions.available (ownedTickets whole)) requirements pendingRow)
    (unique : (ownedTickets whole).Nodup)
    (requestCheck : RecursiveRequirements.Checked (records ++ disposals) (OwnerPhases.ofStack tables whole)
      (OwnerPhaseTransitions.available (ownedTickets whole))
      (.request [] [⟨requested, operation, false⟩]) requestRow) :
    ∃ (answer : SourceDependencyAnnotations.Value) (residual : List Instance) (capDemand tailDemand : List Nat)
      (capReq : RecursiveRequirements.Requirements capDemand) (tailReq : RecursiveRequirements.Requirements tailDemand)
      (capScope tailScope : Receiving) (resumeEffects closeEffects : List Instance) (family : Nat → Dependencies) (captureRow tailRow raw : Footprint)
      (closingRequirements : RecursiveRequirements.Requirements (OwnerClosingSource.retirements plan)),
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩
        ⟨code.subst parameter operand, .ticket binder owner,
          .live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail⟩ [.ticket owner] [] ∧
      ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail) =
        owner :: ownedTickets whole ∧
      (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)).Nodup ∧
      wholeScope = capScope.append tailScope ∧ demand = capDemand ++ tailDemand ∧
      Checked outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)))
        world (family owner) (.live owner capScope tailScope) ∧
      Retained outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)))
        world (.live owner capScope tailScope) .nil ∧
      certificate answer residual family capScope tailScope resumeEffects closeEffects capDemand tailDemand capReq tailReq ∧
      pendingRow = captureRow ++ tailRow ∧
      RecursiveRequirements.Checked (records ++ disposals) (OwnerPhases.ofStack tables tail)
        (OwnerPhaseTransitions.available (ownedTickets whole)) capReq captureRow ∧
      RecursiveRequirements.Checked (records ++ disposals) []
        (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets whole)) capDemand) tailReq tailRow ∧
      (OwnerClosingSource.retirements plan).Perm capDemand ∧
      let closeRow := RecursiveRequirements.evaluate [] (OwnerPhases.ofStack tables tail)
        (OwnerPhaseTransitions.available (ownedTickets whole)) closingRequirements;
      let contract : SourceDependencyAnnotations.Contract := ⟨input, answer, capScope.held,
          capDemand, captureRow, OwnerClosingSource.retirements plan, closeRow, resumeEffects, closeEffects⟩;
        SourceDependencyAnnotations.Body operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
          SourceDependencyAnnotations.Environment.empty (code.subst parameter operand) answer
          ⟨owner, contract.erase, offered.dispose, row⟩ (family owner) ∧
        SourceDependencyFrames.Segment operations policy (contracts.insert owner contract) tables families
          (actions.insert owner code.requiredActions) world
          (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)
          answer output tailDemand (.sequence (.spent owner) tailReq)
          ((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) (.live owner capScope tailScope) residual outgoing ∧
        let nextAnnotations := fun other => if other = owner then some capScope else annotations other;
        Closing.Bound nextAnnotations (.live owner capScope tailScope) ∧
          Closing.Template operations policy (contracts.insert owner contract) tables world .none
            plan raw closingRequirements capScope.forClosing ∧
          DeclaredSourceClosing.Records operations.erase policy (contracts.insert owner contract).erase tables world
            (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)
            ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩) :: disposals) ∧
          Closing.Records operations policy (contracts.insert owner contract) tables nextAnnotations world
            (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)
            ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩) :: disposals) ∧
          let store := ((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) ++
            ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩) :: disposals);
          RecursiveRequirements.Checked store (OwnerPhases.ofStack tables tail)
            (OwnerPhaseTransitions.available (ownedTickets whole)) capReq captureRow ∧
          RecursiveRequirements.Checked store []
            (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets whole)) capDemand) tailReq tailRow ∧
          RecursiveRequirements.Checked store
            (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail))
            (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)))
            (.invoke ⟨owner, .resume⟩ capDemand []) captureRow ∧
          (∀ closingRow, closeRow = some closingRow → RecursiveRequirements.Checked store
            (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail))
            (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)))
            (.invoke ⟨owner, .dispose⟩ (OwnerClosingSource.retirements plan) []) closingRow) ∧
          ((offered.dispose = true → DeclaredCallbackAdmission.checkClosing (CallableProtectionFrames.contextOf tables tail) outside
            raw (requestRow ++ captureRow) = true) →
            ∃ (clauseDemand : List Nat) (clauseRequirements : RecursiveRequirements.Requirements clauseDemand) (clauseRow : Footprint),
              SourceDependencyAnnotations.Expression operations policy (contracts.insert owner contract) world residual
                (.ticket binder owner) SourceDependencyAnnotations.Environment.empty (code.subst parameter operand)
                answer clauseDemand clauseRequirements (family owner) ∧
              RecursiveRequirements.Checked store
                (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail))
                (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)))
                clauseRequirements clauseRow ∧
              EffectBounds.Covers (requestRow ++ captureRow) clauseRow) := by
  have result := allocate_capture_source_from_closing_interfaces
    (outside := outside) (caller := caller) (certificate := certificate)
    (closingCertificate := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => True) cut source interfaces
    (by
      intro answer residual capDemand capReq capRecords capScope saved family tailScope resumeEffects closeEffects tailDemand tailReq data
      obtain ⟨raw, requirements, template⟩ := (Closing.plan_contents saved built).template (tables := tables) (caller := .none)
      exact ⟨raw, requirements, template, trivial⟩)
    selected found available operationKnown payload closed freshContract freshAction layout closingRecords annotationBound freshAnnotation
    built internal pendingCheck unique requestCheck
  obtain ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capScope, tailScope,
    resumeEffects, closeEffects, family, captureRow, tailRow, raw, closingRequirements,
    step, owners, uniqueAfter, scopeSame, demandSame, checked, retained, kept, closingEvidence, rest⟩ := result
  exact ⟨answer, residual, capDemand, tailDemand, capReq, tailReq, capScope, tailScope,
    resumeEffects, closeEffects, family, captureRow, tailRow, raw, closingRequirements,
    step, owners, uniqueAfter, scopeSame, demandSame, checked, retained, kept, rest⟩


theorem allocate_capture_source
    (cut : HandlerCut requested whole capture tail handler)
    (source : SourceDependencyFrames.Segment operations policy contracts tables families actions world
      whole input output demand requirements records wholeScope incoming outgoing)
    (certificates : Stored.Forest outward families whole)
    (checked : Checked outward actions (OwnerPhaseTransitions.available (ownedTickets whole)) world (.request requested operation) wholeScope)
    (retained : Retained outward actions (OwnerPhaseTransitions.available (ownedTickets whole)) world wholeScope .nil)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (found : lookup operation (tables handler) = some offered)
    (available : offered.row (ProtectionContexts.protectedMode capture.erase) = some row)
    (operationKnown : operations requested operation = some (argument, input))
    (payload : SourceDependencyAnnotations.ValueSummary operations policy contracts world
      SourceDependencyAnnotations.Environment.empty payloadAllowed operand argument)
    (closed : ClosedValue operand)
    (freshContract : contracts owner = none) (freshAction : actions owner = none)
    (layout : DeclaredSourceClosing.Records operations.erase policy contracts.erase tables world whole disposals)
    (closingRecords : Closing.Records operations policy contracts tables annotations world whole disposals)
    (annotationBound : Closing.Bound annotations wholeScope) (freshAnnotation : annotations owner = none)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (pendingCheck : RecursiveRequirements.Checked (records ++ disposals) []
      (OwnerPhaseTransitions.available (ownedTickets whole)) requirements pendingRow)
    (unique : (ownedTickets whole).Nodup)
    (requestCheck : RecursiveRequirements.Checked (records ++ disposals) (OwnerPhases.ofStack tables whole)
      (OwnerPhaseTransitions.available (ownedTickets whole))
      (.request [] [⟨requested, operation, false⟩]) requestRow) :
    ∃ (answer : SourceDependencyAnnotations.Value) (residual : List Instance) (capDemand tailDemand : List Nat)
      (capReq : RecursiveRequirements.Requirements capDemand) (tailReq : RecursiveRequirements.Requirements tailDemand)
      (capScope tailScope : Receiving) (resumeEffects closeEffects : List Instance) (family : Nat → Dependencies) (captureRow tailRow raw : Footprint)
      (closingRequirements : RecursiveRequirements.Requirements (OwnerClosingSource.retirements plan)),
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩
        ⟨code.subst parameter operand, .ticket binder owner,
          .live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail⟩ [.ticket owner] [] ∧
      ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail) =
        owner :: ownedTickets whole ∧
      (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)).Nodup ∧
      wholeScope = capScope.append tailScope ∧ demand = capDemand ++ tailDemand ∧
      Checked outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)))
        world (family owner) (.live owner capScope tailScope) ∧
      Retained outward (actions.insert owner code.requiredActions) (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)))
        world (.live owner capScope tailScope) .nil ∧
      Stored.Forest outward families (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail) ∧
      pendingRow = captureRow ++ tailRow ∧
      RecursiveRequirements.Checked (records ++ disposals) (OwnerPhases.ofStack tables tail)
        (OwnerPhaseTransitions.available (ownedTickets whole)) capReq captureRow ∧
      RecursiveRequirements.Checked (records ++ disposals) []
        (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets whole)) capDemand) tailReq tailRow ∧
      (OwnerClosingSource.retirements plan).Perm capDemand ∧
      let closeRow := RecursiveRequirements.evaluate [] (OwnerPhases.ofStack tables tail)
        (OwnerPhaseTransitions.available (ownedTickets whole)) closingRequirements;
      let contract : SourceDependencyAnnotations.Contract := ⟨input, answer, capScope.held,
          capDemand, captureRow, OwnerClosingSource.retirements plan, closeRow, resumeEffects, closeEffects⟩;
        SourceDependencyAnnotations.Body operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
          SourceDependencyAnnotations.Environment.empty (code.subst parameter operand) answer
          ⟨owner, contract.erase, offered.dispose, row⟩ (family owner) ∧
        SourceDependencyFrames.Segment operations policy (contracts.insert owner contract) tables families
          (actions.insert owner code.requiredActions) world
          (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)
          answer output tailDemand (.sequence (.spent owner) tailReq)
          ((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) (.live owner capScope tailScope) residual outgoing ∧
        let nextAnnotations := fun other => if other = owner then some capScope else annotations other;
        Closing.Bound nextAnnotations (.live owner capScope tailScope) ∧
          Closing.Template operations policy (contracts.insert owner contract) tables world .none
            plan raw closingRequirements capScope.forClosing ∧
          DeclaredSourceClosing.Records operations.erase policy (contracts.insert owner contract).erase tables world
            (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)
            ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩) :: disposals) ∧
          Closing.Records operations policy (contracts.insert owner contract) tables nextAnnotations world
            (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)
            ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩) :: disposals) ∧
          let store := ((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) ++
            ((⟨owner, .dispose⟩, ⟨OwnerClosingSource.retirements plan, closingRequirements⟩) :: disposals);
          RecursiveRequirements.Checked store (OwnerPhases.ofStack tables tail)
            (OwnerPhaseTransitions.available (ownedTickets whole)) capReq captureRow ∧
          RecursiveRequirements.Checked store []
            (OwnerPhaseTransitions.spendAll (OwnerPhaseTransitions.available (ownedTickets whole)) capDemand) tailReq tailRow ∧
          RecursiveRequirements.Checked store
            (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail))
            (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)))
            (.invoke ⟨owner, .resume⟩ capDemand []) captureRow ∧
          (∀ closingRow, closeRow = some closingRow → RecursiveRequirements.Checked store
            (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail))
            (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)))
            (.invoke ⟨owner, .dispose⟩ (OwnerClosingSource.retirements plan) []) closingRow) ∧
          ((offered.dispose = true → DeclaredCallbackAdmission.checkClosing (CallableProtectionFrames.contextOf tables tail) outside
            raw (requestRow ++ captureRow) = true) →
            ∃ (clauseDemand : List Nat) (clauseRequirements : RecursiveRequirements.Requirements clauseDemand) (clauseRow : Footprint),
              SourceDependencyAnnotations.Expression operations policy (contracts.insert owner contract) world residual
                (.ticket binder owner) SourceDependencyAnnotations.Environment.empty (code.subst parameter operand)
                answer clauseDemand clauseRequirements (family owner) ∧
              RecursiveRequirements.Checked store
                (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail))
                (OwnerPhaseTransitions.available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)))
                clauseRequirements clauseRow ∧
              EffectBounds.Covers (requestRow ++ captureRow) clauseRow) := by
  have freshErased : contracts.erase owner = none := by
    simp [SourceDependencyAnnotations.Contracts.erase, freshContract]
  have absent := RecursiveCapture.fresh_unowned source.erase.source.erase freshErased
  have consumed : OwnerPhaseTransitions.available (ownedTickets whole) owner = .consumed := by
    simp [OwnerPhaseTransitions.available, absent]
  have interfaces := capture_checked_interfaces cut source certificates checked retained selected found available operationKnown freshAction consumed
  exact allocate_capture_source_from_interfaces cut source interfaces selected found available operationKnown
    payload closed freshContract freshAction layout closingRecords annotationBound freshAnnotation built internal pendingCheck unique requestCheck


namespace Examples

def mixedFamily (owner : Nat) : Dependencies :=
  .choice (.sequence .pure (.invoke ⟨owner, .resume⟩)) (.invoke ⟨owner, .dispose⟩)

/-- The same one-shot clause may choose resume or disposal. This proves a
family over arbitrary captures, rather than checking one captured-stack fixture. -/
theorem mixed_family : ClauseFamily outward ⟨true, true⟩ mixedFamily :=
  (ClauseFamily.silent_prefix (resume_family rfl) .pure).choice (dispose_family rfl)

def resumeClauses : Clauses := .cons 0 1 2 (.resume 2 .unit) .nil

theorem resume_declarations : DeclarationSchemes outward resumeClauses SourceDependencyCapture.Examples.resumeDependencies := by
  apply DeclarationSchemes.cons
  · exact .available ((resume_family rfl).silent_prefix .pure)
  · exact .available ((resume_family rfl).silent_prefix .pure)
  · exact .nil

theorem selected_resume_scheme : ClauseFamily outward (Code.resume 2 .unit).requiredActions SourceDependencyCapture.Examples.resumeFamily :=
  resume_declarations.selected (ClauseAt.hit) (held := true) rfl

/-- Projection cannot restore invocation permission after consumption. -/
theorem consumed_resume_rejected : ¬ Checked outward actions (spend phases owner) world (.invoke ⟨owner, .resume⟩) receiving := by
  intro checked
  obtain ⟨after, computed, _⟩ := checked_resume checked
  rw [SourceDependencyCapture.consumed_resume_rejected] at computed
  cases computed

theorem consumed_dispose_rejected : ¬ Checked outward actions (spend phases owner) world (.invoke ⟨owner, .dispose⟩) receiving := by
  intro checked
  obtain ⟨after, computed, _⟩ := checked_dispose checked
  rw [SourceDependencyCapture.consumed_dispose_rejected] at computed
  cases computed

namespace ClosingBudget
open SourceDependencyChecks (Local Pending)
open SourceDependencyCapture.Examples (resumeDependencies)

def callback : Dependencies := .sequence .pure (.request SourceCallableExamples.effect 0)
def saved : Receiving := .cleanup [SourceCallableExamples.effect] callback .nil
def outside : Receiving := .handler SourceCallableExamples.effect (ClosingBudgetGap.tables ClosingBudgetGap.outer) resumeDependencies .nil
def receiver : Receiving := .handler SourceCallableExamples.effect (ClosingBudgetGap.tables ClosingBudgetGap.shadow) resumeDependencies (.live 19 saved outside)
def captured : Receiving := .plain (.sequence .pure (.invoke ⟨19, .resume⟩))
  (.handler SourceCallableExamples.effect (ClosingBudgetGap.tables ClosingBudgetGap.shadow) resumeDependencies (.live 19 saved .nil))
def families : SourceDependencyFrames.Families := fun _ => resumeDependencies
def actions : Syntax.UsageTickets := fun _ => some ⟨true, false⟩

/-- The dependency scope uses the actual frames of the existing budget gap.
Realization alone does not certify source typing of its annotations. -/
theorem actual_scope : Realizes ClosingBudgetGap.tables families (captured.append outside)
    (ClosingBudgetGap.capture.append ClosingBudgetGap.fixed) := by
  apply Realizes.append
  · exact .push .plain (.push (SourceDependencyCapture.Frame.handler (data := ClosingBudgetGap.shadow))
      (.live (.push (SourceDependencyCapture.Frame.cleanup (action := ClosingBudgetGap.action)) .nil) .nil))
  · exact .push (SourceDependencyCapture.Frame.handler (data := ClosingBudgetGap.outer)) .nil

private theorem callback_outer (phases : Phases) :
    Local [SourceCallableExamples.effect] actions phases [] callback (.running outside) := by
  apply Local.sequence .pure
  apply Local.request_selected (found := rfl) (ownerBound := by intro possible; cases possible <;> repeat constructor)
  · decide
  · intro impossible; cases impossible

/-- Both resumption's actual caller and the dormant callback pass the current
structural checks, despite their different effect-row interpretations. -/
theorem retained_checked : Retained [SourceCallableExamples.effect] actions (OwnerPhaseTransitions.available [19]) [] captured outside := by
  change Pending [SourceCallableExamples.effect] actions (OwnerPhaseTransitions.available [19]) [] captured outside
  apply Pending.plain
  · apply Local.sequence .pure
    apply Local.resume (after := saved.append
      (.handler SourceCallableExamples.effect (ClosingBudgetGap.tables ClosingBudgetGap.shadow) resumeDependencies (.spent 19 outside)))
      (check_resume_iff.mp (show checkResume actions (OwnerPhaseTransitions.available [19]) 19 receiver =
        some (saved.append (.handler SourceCallableExamples.effect (ClosingBudgetGap.tables ClosingBudgetGap.shadow) resumeDependencies (.spent 19 outside))) from rfl))
    apply Pending.cleanup
    · apply Local.sequence .pure
      apply Local.request_selected (found := rfl) (ownerBound := by intro possible; cases possible <;> repeat constructor)
      · decide
      · intro impossible; cases impossible
    · exact .handler (.handler .nil)
  · exact .handler (.live (.cleanup (callback_outer _) .nil) .nil)

/-- Explicitly checking the scheduled callback does not compare its exported
row with the normal computation's budget. -/
theorem scheduled_checked : Retained [SourceCallableExamples.effect] actions (OwnerPhaseTransitions.available [19]) []
    captured.forClosing (.running outside) := by
  change Pending [SourceCallableExamples.effect] actions (OwnerPhaseTransitions.available [19]) []
    (.cleanup [SourceCallableExamples.effect] callback (.running .nil)) (.running outside)
  apply Pending.cleanup
  · apply Local.sequence .pure
    apply Local.request_selected (found := rfl) (ownerBound := by intro possible; cases possible <;> repeat constructor)
    · decide
    · intro impossible; cases impossible
  · exact .running .nil

/-- The old checked normal row is empty; the closing row needs an explicit
nonempty budget even with the new contextual checks. -/
theorem budget_still_required :
    DeclaredCallbackAdmission.checkClosing (CallableProtectionFrames.contextOf ClosingBudgetGap.tables ClosingBudgetGap.fixed)
      [.handler SourceCallableExamples.effect 13 SourceCallableExamples.table] ClosingBudgetGap.forwarded [] = false ∧
    DeclaredCallbackAdmission.checkClosing (CallableProtectionFrames.contextOf ClosingBudgetGap.tables ClosingBudgetGap.fixed)
      [.handler SourceCallableExamples.effect 13 SourceCallableExamples.table] ClosingBudgetGap.forwarded ClosingBudgetGap.forwarded = true := by
  constructor <;> decide

end ClosingBudget

end Examples

end Ash.OneShot.SourceDependencySchemes

#print axioms Ash.OneShot.SourceDependencySchemes.checked_spent
#print axioms Ash.OneShot.SourceDependencySchemes.retained_spent
#print axioms Ash.OneShot.SourceDependencySchemes.retained_outside_spent
#print axioms Ash.OneShot.SourceDependencySchemes.retained_append
#print axioms Ash.OneShot.SourceDependencySchemes.retained_capture
#print axioms Ash.OneShot.SourceDependencySchemes.checked_request
#print axioms Ash.OneShot.SourceDependencySchemes.checked_sequence
#print axioms Ash.OneShot.SourceDependencySchemes.checked_cleanup
#print axioms Ash.OneShot.SourceDependencySchemes.checked_resume
#print axioms Ash.OneShot.SourceDependencySchemes.checked_dispose
#print axioms Ash.OneShot.SourceDependencySchemes.ClauseFamily.instantiate
#print axioms Ash.OneShot.SourceDependencySchemes.resume_family
#print axioms Ash.OneShot.SourceDependencySchemes.dispose_family
#print axioms Ash.OneShot.SourceDependencySchemes.ClauseFamily.silent_prefix
#print axioms Ash.OneShot.SourceDependencySchemes.ClauseFamily.choice
#print axioms Ash.OneShot.SourceDependencySchemes.ModeScheme.selected
#print axioms Ash.OneShot.SourceDependencySchemes.DeclarationSchemes.selected
#print axioms Ash.OneShot.SourceDependencySchemes.selected_checked_body
#print axioms Ash.OneShot.SourceDependencySchemes.resume_source_step
#print axioms Ash.OneShot.SourceDependencySchemes.dispose_source_step
#print axioms Ash.OneShot.SourceDependencySchemes.Examples.mixed_family
#print axioms Ash.OneShot.SourceDependencySchemes.Examples.resume_declarations
#print axioms Ash.OneShot.SourceDependencySchemes.Examples.selected_resume_scheme
#print axioms Ash.OneShot.SourceDependencySchemes.Examples.consumed_resume_rejected
#print axioms Ash.OneShot.SourceDependencySchemes.Examples.consumed_dispose_rejected

#print axioms Ash.OneShot.SourceDependencySchemes.PhaseExtension.spend
#print axioms Ash.OneShot.SourceDependencySchemes.introduce_extends
#print axioms Ash.OneShot.SourceDependencySchemes.local_phase_transport
#print axioms Ash.OneShot.SourceDependencySchemes.pending_phase_transport
#print axioms Ash.OneShot.SourceDependencySchemes.retained_capture_introduce

#print axioms Ash.OneShot.SourceDependencySchemes.local_transport
#print axioms Ash.OneShot.SourceDependencySchemes.pending_transport

#print axioms Ash.OneShot.SourceDependencySchemes.checked_request_schedule
#print axioms Ash.OneShot.SourceDependencySchemes.capture_source_from_request
#print axioms Ash.OneShot.SourceDependencySchemes.allocate_checked_clause

#print axioms Ash.OneShot.SourceDependencySchemes.allocate_declared_clause

#print axioms Ash.OneShot.SourceDependencySchemes.DeclarationSchemes.substitution
#print axioms Ash.OneShot.SourceDependencySchemes.DeclarationSchemes.instantiation

#print axioms Ash.OneShot.SourceDependencySchemes.Stored.Forest.append_iff

#print axioms Ash.OneShot.SourceDependencySchemes.Stored.Forest.cut

#print axioms Ash.OneShot.SourceDependencySchemes.Stored.Forest.capture

#print axioms Ash.OneShot.SourceDependencySchemes.Stored.Forest.resume

#print axioms Ash.OneShot.SourceDependencySchemes.Stored.Forest.close_control

#print axioms Ash.OneShot.SourceDependencySchemes.Stored.Forest.dispose

#print axioms Ash.OneShot.SourceDependencySchemes.capture_checked_interfaces

#print axioms Ash.OneShot.SourceDependencySchemes.allocate_capture_source
#print axioms Ash.OneShot.SourceDependencySchemes.Closing.Contents.append
#print axioms Ash.OneShot.SourceDependencySchemes.Closing.plan_contents
#print axioms Ash.OneShot.SourceDependencySchemes.Closing.Contents.source
#print axioms Ash.OneShot.SourceDependencySchemes.Closing.recompose

#print axioms Ash.OneShot.SourceDependencySchemes.Closing.Template.erase
#print axioms Ash.OneShot.SourceDependencySchemes.Closing.Template.empty_raw
#print axioms Ash.OneShot.SourceDependencySchemes.Closing.Template.closed_budget
#print axioms Ash.OneShot.SourceDependencySchemes.closed_capture_budget
#print axioms Ash.OneShot.SourceDependencySchemes.Closing.Contents.template
#print axioms Ash.OneShot.SourceDependencySchemes.Closing.Template.scope
#print axioms Ash.OneShot.SourceDependencySchemes.Closing.Template.source

#print axioms Ash.OneShot.SourceDependencySchemes.Closing.Records.member
#print axioms Ash.OneShot.SourceDependencySchemes.Closing.selected_template
#print axioms Ash.OneShot.SourceDependencySchemes.Closing.checked_plan

#print axioms Ash.OneShot.SourceDependencySchemes.Closing.Records.of_members
#print axioms Ash.OneShot.SourceDependencySchemes.Closing.Records.after_step

#print axioms Ash.OneShot.SourceDependencySchemes.Closing.Bound.selected
#print axioms Ash.OneShot.SourceDependencySchemes.Closing.Bound.transport
#print axioms Ash.OneShot.SourceDependencySchemes.Closing.Bound.capture
#print axioms Ash.OneShot.SourceDependencySchemes.Closing.Bound.disposal

#print axioms Ash.OneShot.SourceDependencySchemes.Closing.Bound.append_iff
#print axioms Ash.OneShot.SourceDependencySchemes.Closing.Bound.forClosing
#print axioms Ash.OneShot.SourceDependencySchemes.Closing.Bound.invocations

#print axioms Ash.OneShot.SourceDependencySchemes.Closing.prefix_owner_cut

#print axioms Ash.OneShot.SourceDependencySchemes.Closing.Template.transport
#print axioms Ash.OneShot.SourceDependencySchemes.Closing.Records.transport
#print axioms Ash.OneShot.SourceDependencySchemes.Closing.capture_records

#print axioms Ash.OneShot.SourceDependencySchemes.Examples.ClosingBudget.actual_scope

#print axioms Ash.OneShot.SourceDependencySchemes.Examples.ClosingBudget.retained_checked

#print axioms Ash.OneShot.SourceDependencySchemes.Examples.ClosingBudget.scheduled_checked

#print axioms Ash.OneShot.SourceDependencySchemes.Examples.ClosingBudget.budget_still_required

#print axioms Ash.OneShot.SourceDependencySchemes.owners_project

#print axioms Ash.OneShot.SourceDependencySchemes.pending_owners_unproject

#print axioms Ash.OneShot.SourceDependencySchemes.checked_request_owners

#print axioms Ash.OneShot.SourceDependencySchemes.capture_internal_uses

#print axioms Ash.OneShot.SourceDependencySchemes.allocate_capture_source_from_interfaces

#print axioms Ash.OneShot.SourceDependencySchemes.allocate_capture_source_from_closing_interfaces


namespace Ash.OneShot.SourceDependencySchemes.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyAnnotations (Dependencies)
open SourceDependencyCapture
open SourceDependencyChecks.Lexical (Local Pending Unwind)
open OwnerPhaseTransitions (Phases spend)
open SourceContextualHints (Hints)
open SourcePlannedNeutralFrames (Expansion)
open SourceDependencyNeutral (bare)

/-- The existing fresh-phase/permission transport induction now includes the
    lexical unwind checks carried by disposing requests. -/
theorem local_transport (source : Local outward actions before world dependencies receiving)
    (extension : PhaseExtension before after) (permissions : Syntax.UsageExtension actions nextActions)
    (larger : world ⊆ nextWorld) : Local outward nextActions after nextWorld dependencies receiving := by
  refine (Local.rec
    (motive_1 := fun before world dependencies receiving _ => ∀ after nextActions nextWorld,
      PhaseExtension before after → Syntax.UsageExtension actions nextActions → world ⊆ nextWorld →
      Local outward nextActions after nextWorld dependencies receiving)
    (motive_2 := fun before world forest outside _ => ∀ after nextActions nextWorld,
      PhaseExtension before after → Syntax.UsageExtension actions nextActions → world ⊆ nextWorld →
      Pending outward nextActions after nextWorld forest outside)
    (motive_3 := fun before world forest outside _ => ∀ after nextActions nextWorld,
      PhaseExtension before after → Syntax.UsageExtension actions nextActions → world ⊆ nextWorld →
      Unwind outward nextActions after nextWorld forest outside)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (t := source))
    after nextActions nextWorld extension permissions larger
  · intros; exact .pure
  · intros
    rename_i guard callbacks bound ihCallbacks after nextActions nextWorld extension permissions larger
    exact .request guard
      (fun captured tail contract modes selected disposes =>
        ihCallbacks captured tail contract modes selected disposes after nextActions nextWorld extension permissions larger)
      (fun captured tail contract modes selected disposes =>
        (bound captured tail contract modes selected disposes).world_weaken larger)
  · intros
    rename_i access restored ih after nextActions nextWorld extension permissions larger
    cases access with
    | checked located known permission available =>
        exact .resume (.checked located (permissions _ _ known) permission (extension _ available))
          (ih _ nextActions nextWorld extension.spend permissions larger)
  · intros
    rename_i located known permission available unprotected callbacks waiting ihCallbacks ihWaiting after nextActions nextWorld extension permissions larger
    exact .dispose located (permissions _ _ known) permission (extension _ available) unprotected
      (ihCallbacks _ nextActions nextWorld extension.spend permissions larger)
      (ihWaiting _ nextActions nextWorld extension.spend permissions larger)
  · intros
    rename_i first second ihFirst ihSecond after nextActions nextWorld extension permissions larger
    exact .sequence (ihFirst after nextActions nextWorld extension permissions larger)
      (ihSecond after nextActions nextWorld extension permissions larger)
  · intros
    rename_i first second ihFirst ihSecond after nextActions nextWorld extension permissions larger
    exact .choice (ihFirst after nextActions nextWorld extension permissions larger)
      (ihSecond after nextActions nextWorld extension permissions larger)
  · intros
    rename_i body ih after nextActions nextWorld extension permissions larger
    exact .handler (ih after nextActions nextWorld extension permissions larger)
  · intros
    rename_i body callback ihBody ihCallback after nextActions nextWorld extension permissions larger
    exact .cleanup (ihBody after nextActions nextWorld extension permissions larger)
      (ihCallback after nextActions nextWorld extension permissions larger)
  · intros
    rename_i body ih after nextActions nextWorld extension permissions larger
    exact .resource (fun identity fresh => ih identity (fun member => fresh (larger member))
      after nextActions (nextWorld ++ [identity]) extension permissions
      (ScopedExpressions.append_subset larger (List.Subset.refl _)))
  · intros; exact .nil
  · intros
    rename_i first second ihFirst ihSecond after nextActions nextWorld extension permissions larger
    exact .plain (ihFirst after nextActions nextWorld extension permissions larger)
      (ihSecond after nextActions nextWorld extension permissions larger)
  · intros
    rename_i tail ih after nextActions nextWorld extension permissions larger
    exact .handler (ih after nextActions nextWorld extension permissions larger)
  · intros
    rename_i tail ih after nextActions nextWorld extension permissions larger
    exact .cell (ih after nextActions nextWorld extension permissions larger)
  · intros
    rename_i first second ihFirst ihSecond after nextActions nextWorld extension permissions larger
    exact .cleanup (ihFirst after nextActions nextWorld extension permissions larger)
      (ihSecond after nextActions nextWorld extension permissions larger)
  · intros
    rename_i tail ih after nextActions nextWorld extension permissions larger
    exact .running (ih after nextActions nextWorld extension permissions larger)
  · intros
    rename_i first second ihFirst ihSecond after nextActions nextWorld extension permissions larger
    exact .live (ihFirst after nextActions nextWorld extension permissions larger)
      (ihSecond after nextActions nextWorld extension permissions larger)
  · intros
    rename_i tail ih after nextActions nextWorld extension permissions larger
    exact .spent (ih after nextActions nextWorld extension permissions larger)
  · intros; exact .nil
  · intros
    rename_i tail ih after nextActions nextWorld extension permissions larger
    exact .plain (ih after nextActions nextWorld extension permissions larger)
  · intros
    rename_i tail ih after nextActions nextWorld extension permissions larger
    exact .handler (ih after nextActions nextWorld extension permissions larger)
  · intros
    rename_i tail ih after nextActions nextWorld extension permissions larger
    exact .cell (ih after nextActions nextWorld extension permissions larger)
  · intros
    rename_i first second ihFirst ihSecond after nextActions nextWorld extension permissions larger
    exact .cleanup (ihFirst after nextActions nextWorld extension permissions larger)
      (ihSecond after nextActions nextWorld extension permissions larger)
  · intros
    rename_i tail ih after nextActions nextWorld extension permissions larger
    exact .running (ih after nextActions nextWorld extension permissions larger)
  · intros
    rename_i first second ihFirst ihSecond after nextActions nextWorld extension permissions larger
    exact .live (ihFirst after nextActions nextWorld extension permissions larger)
      (ihSecond after nextActions nextWorld extension permissions larger)
  · intros
    rename_i tail ih after nextActions nextWorld extension permissions larger
    exact .spent (ih after nextActions nextWorld extension permissions larger)

theorem pending_transport (source : Pending outward actions before world forest outside)
    (extension : PhaseExtension before after) (permissions : Syntax.UsageExtension actions nextActions)
    (larger : world ⊆ nextWorld) : Pending outward nextActions after nextWorld forest outside := by
  induction forest generalizing outside with
  | nil => exact .nil
  | plain dependencies rest ih => cases source with
    | plain code tail => exact .plain (local_transport code extension permissions larger) (ih tail)
  | handler effect table families rest ih => cases source with | handler tail => exact .handler (ih tail)
  | cell identity rest ih => cases source with | cell tail => exact .cell (ih tail)
  | cleanup needs dependencies rest ih => cases source with
    | cleanup callback tail => exact .cleanup (local_transport callback extension permissions larger) (ih tail)
  | running rest ih => cases source with | running tail => exact .running (ih tail)
  | live owner captured rest ihCaptured ihRest => cases source with
    | live saved tail => exact .live (ihCaptured saved) (ihRest tail)
  | spent owner rest ih => cases source with | spent tail => exact .spent (ih tail)

theorem unwind_transport (source : Unwind outward actions before world forest outside)
    (extension : PhaseExtension before after) (permissions : Syntax.UsageExtension actions nextActions)
    (larger : world ⊆ nextWorld) : Unwind outward nextActions after nextWorld forest outside := by
  induction forest generalizing outside with
  | nil => exact .nil
  | plain dependencies rest ih => cases source with | plain tail => exact .plain (ih tail)
  | handler effect table families rest ih => cases source with | handler tail => exact .handler (ih tail)
  | cell identity rest ih => cases source with | cell tail => exact .cell (ih tail)
  | cleanup needs dependencies rest ih => cases source with
    | cleanup callback tail => exact .cleanup (local_transport callback extension permissions larger) (ih tail)
  | running rest ih => cases source with | running tail => exact .running (ih tail)
  | live owner captured rest ihCaptured ihRest => cases source with
    | live saved tail => exact .live (ihCaptured saved) (ihRest tail)
  | spent owner rest ih => cases source with | spent tail => exact .spent (ih tail)

/-- Preserve retained checks when their enclosing suffix gains only neutral
    frames. The same scope-expansion proof is used for each callback. -/
theorem pending_outside_transport
    (source : Pending outward actions phases world forest outside)
    {hints : Hints outside} {next : Hints nextOutside} (changed : Expansion hints next) :
    Pending outward actions phases world forest nextOutside := by
  induction forest generalizing outside nextOutside with
  | nil => exact .nil
  | plain dependencies rest ih => cases source with
    | plain code tail =>
      exact .plain
        (SourceDependencyNeutral.Lexical.local_transport code (changed.prefix (bare rest))) (ih tail changed)
  | handler effect table families rest ih => cases source with | handler tail => exact .handler (ih tail changed)
  | cell identity rest ih => cases source with | cell tail => exact .cell (ih tail changed)
  | cleanup needs dependencies rest ih => cases source with
    | cleanup callback tail =>
      exact .cleanup
        (SourceDependencyNeutral.Lexical.local_transport callback (.running (changed.prefix (bare rest)))) (ih tail changed)
  | running rest ih => cases source with | running tail => exact .running (ih tail changed)
  | live owner captured rest ihCaptured ihRest => cases source with
    | live saved tail => exact .live (ihCaptured saved (changed.prefix (bare rest))) (ihRest tail changed)
  | spent owner rest ih => cases source with | spent tail => exact .spent (ih tail changed)

/-- Preserve retained checks when their enclosing suffix gains only neutral
    frames. The same scope-expansion proof is used for each callback. -/
theorem unwind_outside_transport
    (source : Unwind outward actions phases world forest outside)
    {hints : Hints outside} {next : Hints nextOutside} (changed : Expansion hints next) :
    Unwind outward actions phases world forest nextOutside := by
  induction forest generalizing outside nextOutside with
  | nil => exact .nil
  | plain dependencies rest ih => cases source with | plain tail => exact .plain (ih tail changed)
  | handler effect table families rest ih => cases source with | handler tail => exact .handler (ih tail changed)
  | cell identity rest ih => cases source with | cell tail => exact .cell (ih tail changed)
  | cleanup needs dependencies rest ih => cases source with
    | cleanup callback tail =>
      exact .cleanup
        (SourceDependencyNeutral.Lexical.local_transport callback (.running (changed.prefix (bare rest)))) (ih tail changed)
  | running rest ih => cases source with | running tail => exact .running (ih tail changed)
  | live owner captured rest ihCaptured ihRest => cases source with
    | live saved tail => exact .live (ihCaptured saved (.running (changed.prefix (bare rest)))) (ihRest tail changed)
  | spent owner rest ih => cases source with | spent tail => exact .spent (ih tail changed)

/-- Finite checks of the actual captured scopes and caller, after the newly
    allocated owner is consumed. No execution trace or closing plan is assumed. -/
structure CaptureSource (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : Phases) (world : List Nat) (owner : Nat) (rights : Syntax.OneShotRights)
    (captured tail : SourceDependencyCapture.Scope) : Prop where
  saved : rights.resume = true → Pending outward actions (spend phases owner) world captured tail
  waiting : Pending outward actions (spend phases owner) world tail .nil
  disposal : rights.dispose = true → captured.held = false ∧
    Unwind outward actions (spend phases owner) world captured (.running tail)

inductive ClauseFamily (outward : List Instance) (rights : Syntax.OneShotRights)
    (family : Nat → Dependencies) : Prop where
  | checked (body : ∀ actions phases world owner captured tail,
      actions owner = some rights → phases owner = .available →
      CaptureSource outward actions phases world owner rights captured tail →
      Local outward actions phases world (family owner) (.live owner captured tail)) :
      ClauseFamily outward rights family

theorem ClauseFamily.instantiate (scheme : ClauseFamily outward rights family)
    (known : actions owner = some rights) (available : phases owner = .available)
    (source : CaptureSource outward actions phases world owner rights captured tail) :
    Local outward actions phases world (family owner) (.live owner captured tail) := by
  cases scheme with | checked body => exact body actions phases world owner captured tail known available source

theorem resume_family {rights : Syntax.OneShotRights} (permission : rights.resume = true) :
    ClauseFamily outward rights (fun owner => .invoke ⟨owner, .resume⟩) := by
  constructor
  intro actions phases world owner captured tail known available source
  apply Local.resume (after := captured.append (.spent owner tail))
    (ResumeChecked.checked OwnerCut.hit known permission available)
  apply Pending.append_iff.mpr
  exact ⟨by simpa only [SourceDependencyProjection.scope_append_nil] using
    pending_outside_transport (source.saved permission) (hints := bare tail) (.history (owner := owner) .refl),
    .spent source.waiting⟩

theorem dispose_family {rights : Syntax.OneShotRights} (permission : rights.dispose = true) :
    ClauseFamily outward rights (fun owner => .invoke ⟨owner, .dispose⟩) := by
  constructor
  intro actions phases world owner captured tail known available source
  obtain ⟨unprotected, callbacks⟩ := source.disposal permission
  apply Local.dispose OwnerCut.hit known permission available unprotected
  · exact unwind_outside_transport callbacks (hints := .running (bare tail))
      (.running (.history (owner := owner) .refl))
  · exact .spent source.waiting

theorem ClauseFamily.silent_prefix (scheme : ClauseFamily outward rights family)
    (silent : Dependencies.Silent dependencies) :
    ClauseFamily outward rights (fun owner => .sequence dependencies (family owner)) := by
  constructor
  intro actions phases world owner captured tail known available source
  exact .sequence (.silent silent) (scheme.instantiate known available source)

theorem ClauseFamily.choice (first : ClauseFamily outward rights family) (second : ClauseFamily outward rights alternative) :
    ClauseFamily outward rights (fun owner => .choice (family owner) (alternative owner)) := by
  constructor
  intro actions phases world owner captured tail known available source
  exact .choice (first.instantiate known available source) (second.instantiate known available source)

/-- Fresh-owner admission follows from checks of the current request and stack.
    Spending the newly introduced owner restores the original phase map. -/
theorem capture_source_from_request
    (checked : Local outward actions phases world (.request effect operation) (captured.append tail))
    (retained : Pending outward actions phases world (captured.append tail) .nil)
    (found : select effect operation (captured.append tail) = some (.handler captured tail contract modes))
    (disposalPermission : rights.dispose = true → contract.dispose = true)
    (fresh : actions owner = none) (consumed : phases owner = .consumed) :
    CaptureSource outward (actions.insert owner rights) (OwnerPhaseTransitions.introduce phases owner)
      world owner rights captured tail := by
  have permissions := Syntax.fresh_usage_insert_extends (rights := rights) fresh
  have samePhases := OwnerCaptureContracts.spend_introduced consumed
  have joined := pending_transport retained (fun _ ready => ready) permissions (List.Subset.refl _)
  obtain ⟨saved, waiting⟩ := Pending.append_iff.mp joined
  refine ⟨?_, ?_, ?_⟩
  · intro _
    simpa only [samePhases, SourceDependencyProjection.scope_append_nil] using saved
  · simpa only [samePhases] using waiting
  · intro disposes
    cases checked with
    | request guard callbacks ownerBound =>
      have permission := disposalPermission disposes
      have unprotected : captured.held = false := by
        cases guard with
        | builtin actual => cases Option.some.inj (found.symm.trans actual)
        | handler actual permitted row body =>
          cases Option.some.inj (found.symm.trans actual)
          cases held : captured.held with
          | false => rfl
          | true => simp [modeCheck, permission, held] at permitted
      refine ⟨unprotected, ?_⟩
      rw [samePhases]
      exact unwind_transport (callbacks _ _ _ _ found permission)
        (fun _ ready => ready) permissions (List.Subset.refl _)

end Ash.OneShot.SourceDependencySchemes.Lexical

#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.local_transport
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.pending_transport
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.unwind_transport
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.pending_outside_transport
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.unwind_outside_transport
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.ClauseFamily.instantiate
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.resume_family
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.dispose_family
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.ClauseFamily.silent_prefix
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.ClauseFamily.choice
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.capture_source_from_request


namespace Ash.OneShot.SourceDependencySchemes.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations SourceDependencyFrames
open RecursiveRequirements (Requirements Store evaluate)
open OwnerPhaseTransitions (available spend spendAll)

/-- Fresh allocation retains the exact split source and checked requirements.
    Closing data is chosen before extension; the generic record-insertion
    theorems preserve old checks without rechecking future execution. -/
theorem allocate_split
    (cut : HandlerCut requested whole capture tail handler)
    (source : LexicalSegment operations policy contracts tables families actions world
      whole input output demand requirements records wholeScope incoming outgoing)
    (annotation : answer.erase.port = ScopedPorts.eraseType handler.answer)
    (scope : ScopedPorts.EffectScopeKnown contracts.erase.ports handler.scope)
    (saved : LexicalSegment operations policy contracts tables families actions world
      capture input answer capDemand capReq capRecords capScope incoming residual)
    (waiting : LexicalSegment operations policy contracts tables families actions world
      tail answer output tailDemand tailReq tailRecords tailScope residual outgoing)
    (sameRecords : records = capRecords ++ tailRecords)
    (savedCheck : RecursiveRequirements.Checked (records ++ disposals) (OwnerPhases.ofStack tables tail)
      (available (ownedTickets whole)) capReq capRow)
    (tailCheck : RecursiveRequirements.Checked (records ++ disposals) []
      (spendAll (available (ownedTickets whole)) capDemand) tailReq tailRow)
    (unique : (ownedTickets whole).Nodup)
    (fresh : contracts owner = none) (freshAction : actions owner = none)
    (resume : rights.resume = true → resumeEffects = residual)
    (close : rights.dispose = true → closeEffects = residual)
    (closingDemand : List Nat) (closingRow : Option Footprint)
    (chosen : UnwindRecords operations policy contracts tables world
      (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail) (added ++ disposals))
    (keys : ∀ key body, (key, body) ∈ added → key.owner = owner ∧ key.mode = .dispose) :
    let contract : Contract := ⟨input, answer, capScope.held,
      capDemand, capRow, closingDemand, closingRow, resumeEffects, closeEffects⟩
    let nextStack := Stack.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail
    let nextResumes : Store := (⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records
    let store := nextResumes ++ (added ++ disposals)
    LexicalSegment operations policy (contracts.insert owner contract) tables families
      (actions.insert owner rights) world nextStack answer output tailDemand
      (.sequence (.spent owner) tailReq) nextResumes (.live owner capScope tailScope) residual outgoing ∧
    UnwindRecords operations policy (contracts.insert owner contract) tables world nextStack (added ++ disposals) ∧
    RecursiveRequirements.Checked store (OwnerPhases.ofStack tables tail) (available (ownedTickets whole)) capReq capRow ∧
    RecursiveRequirements.Checked store [] (spendAll (available (ownedTickets whole)) capDemand) tailReq tailRow ∧
    (ownedTickets nextStack).Nodup ∧
    spend (available (ownedTickets nextStack)) owner = available (ownedTickets whole) ∧
    RecursiveRequirements.Checked store (OwnerPhases.ofStack tables nextStack) (available (ownedTickets nextStack))
      (.invoke ⟨owner, .resume⟩ capDemand []) capRow := by
  let contract : Contract := ⟨input, answer, capScope.held,
    capDemand, capRow, closingDemand, closingRow, resumeEffects, closeEffects⟩
  have extension := SourceDependencyAnnotations.insert_extends (contract := contract) contracts fresh
  have permissions := Syntax.fresh_usage_insert_extends (rights := rights) freshAction
  have ports := CoherentSourceTypes.Owners.port_contracts_extension (erased_contract_extension extension)
  have absent := source.fresh_unowned fresh
  have consumed : available (ownedTickets whole) owner = .consumed := by
    simp [available, absent]
  have laterConsumed := RecursiveTransport.phases_spendAll_later (owners := capDemand) owner consumed
  have savedAfter := RecursiveCapture.checked_insert_consumed
    (RecursiveAllocation.checked_add_closing savedCheck consumed keys) consumed
      (mode := .resume) (body := ⟨capDemand, capReq⟩)
  have tailAfter := RecursiveCapture.checked_insert_consumed
    (RecursiveAllocation.checked_add_closing tailCheck laterConsumed keys) laterConsumed
      (mode := .resume) (body := ⟨capDemand, capReq⟩)
  have phaseSame := RecursiveCapture.capture_phase_consumed (input := ScopedPorts.embedPort input.erase.port) cut absent
  refine ⟨?_, chosen.transport extension (List.Subset.refl _), savedAfter, tailAfter,
    source.capture_unique cut unique fresh, phaseSame, RecursiveClauses.fresh_resume_check savedAfter phaseSame⟩
  rw [sameRecords]
  have known : (contracts.insert owner contract) owner = some contract := by simp [Contracts.insert]
  have actionKnown : (actions.insert owner rights) owner = some rights := by simp [Syntax.UsageTickets.insert]
  exact LexicalSegment.live known actionKnown
    (ScopedPorts.erase_embed_port input.erase.port).symm annotation
    (ScopedPorts.effect_scope_known_extension scope ports) saved.realizes.held
    ((saved.input_weaken (List.nil_subset _)).transport extension permissions (List.Subset.refl _))
    (fun used => by simpa only [contract, resume used] using List.Subset.refl residual)
    (waiting.transport extension permissions (List.Subset.refl _))
    (fun used => by simpa only [contract, resume used] using List.Subset.refl residual)
    (fun used => by simpa only [contract, close used] using List.Subset.refl residual)
    (List.Subset.refl _)

/-- Lexical disposal uses the established invocation-check construction;
    summary ownership and store independence replace plan-specific lemmas. -/
theorem closing_invocation_from_record
    (summary : UnwindTemplate operations policy contracts tables world capture closingDemand closingRequirements)
    (looked : RecursiveRequirements.lookup ⟨owner, .dispose⟩ records = some ⟨closingDemand, closingRequirements⟩)
    (unique : (ownedTickets (.live owner input answer capture caller tail)).Nodup)
    (evaluated : evaluate [] (OwnerPhases.ofStack tables tail)
      (spend (available (ownedTickets (.live owner input answer capture caller tail))) owner) closingRequirements = some row) :
    RecursiveRequirements.Checked records (OwnerPhases.ofStack tables (.live owner input answer capture caller tail))
      (available (ownedTickets (.live owner input answer capture caller tail)))
      (.invoke ⟨owner, .dispose⟩ closingDemand []) row := by
  let initial := available (ownedTickets (.live owner input answer capture caller tail))
  have capturedOwners := summary.ownership
  have splitUnique := List.nodup_cons.mp unique
  have demandUnique : (owner :: closingDemand).Nodup := by
    refine List.nodup_cons.mpr ⟨?_, capturedOwners.symm.nodup (List.nodup_append.mp splitUnique.2).1⟩
    intro member
    exact splitUnique.1 (List.mem_append_left _ (capturedOwners.mem_iff.mp member))
  have transition : OwnerPhaseTransitions.Trace initial (owner :: closingDemand)
      (spendAll initial (owner :: closingDemand)) :=
    OwnerPhaseTransitions.trace_of_available demandUnique (by
      intro actual member
      apply if_pos
      rcases List.mem_cons.mp member with same | nested
      · exact List.mem_cons.mpr (Or.inl same)
      · exact List.mem_cons.mpr (Or.inr (List.mem_append_left _ (capturedOwners.mem_iff.mp nested))))
  have checked : RecursiveRequirements.Checked records (OwnerPhases.ofStack tables tail) (spend initial owner) closingRequirements row := by
    apply RecursiveRequirements.evaluate_sound
    rw [summary.store (first := records) (second := [])]
    exact evaluated
  have body : RecursiveRequirements.Checked records (OwnerPhases.ofStack tables (.live owner input answer capture caller tail))
      (spend initial owner) closingRequirements row := by
    apply RecursiveTransport.checked_transport checked (fun _ _ => rfl)
    simp only [OwnerPhases.ofStack, RecursiveTransport.normalize, OwnerPhaseTransitions.spend_self, if_true]
  exact .invoke looked (PhaseRechecking.check_owners_iff.mpr transition)
    (by exact OwnerPhases.Consumes.hit) (by simpa only [List.nil_append] using body)

/-- Construct a fresh disposing contract with the actual lexical closing
    row. Ownership balance is derived on the constructed live source, not
    assumed as a premise of allocation. A structural cleanup-effect annotation
    supplies row success and coverage, completing the local clause interface. -/
theorem allocate_disposing_split
    (cut : HandlerCut requested whole capture tail handler)
    (source : LexicalSegment operations policy contracts tables families actions world
      whole input output demand requirements records wholeScope incoming outgoing)
    (annotation : answer.erase.port = ScopedPorts.eraseType handler.answer)
    (scope : ScopedPorts.EffectScopeKnown contracts.erase.ports handler.scope)
    (saved : LexicalSegment operations policy contracts tables families actions world
      capture input answer capDemand capReq capRecords capScope incoming residual)
    (waiting : LexicalSegment operations policy contracts tables families actions world
      tail answer output tailDemand tailReq tailRecords tailScope residual outgoing)
    (sameRecords : records = capRecords ++ tailRecords)
    (savedCheck : RecursiveRequirements.Checked (records ++ disposals) (OwnerPhases.ofStack tables tail)
      (available (ownedTickets whole)) capReq capRow)
    (tailCheck : RecursiveRequirements.Checked (records ++ disposals) []
      (spendAll (available (ownedTickets whole)) capDemand) tailReq tailRow)
    (unique : (ownedTickets whole).Nodup)
    (fresh : contracts owner = none) (freshAction : actions owner = none)
    (resume : rights.resume = true → resumeEffects = residual)
    (close : rights.dispose = true → closeEffects = residual)
    (closing : UnwindRecords operations policy contracts tables world whole disposals)
    (unprotected : ProtectionContexts.protectedMode capture.erase = false)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (summary : UnwindTemplate operations policy contracts tables world capture closingDemand closingRequirements) :
    let closingRow := evaluate [] (OwnerPhases.ofStack tables tail) (available (ownedTickets whole)) closingRequirements
    let added : Store := [(⟨owner, .dispose⟩, ⟨closingDemand, closingRequirements⟩)]
    let contract : Contract := ⟨input, answer, capScope.held,
      capDemand, capRow, closingDemand, closingRow, resumeEffects, closeEffects⟩
    let nextStack := Stack.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail
    let nextResumes : Store := (⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records
    let store := nextResumes ++ (added ++ disposals)
    LexicalSegment operations policy (contracts.insert owner contract) tables families
      (actions.insert owner rights) world nextStack answer output tailDemand
      (.sequence (.spent owner) tailReq) nextResumes (.live owner capScope tailScope) residual outgoing ∧
    UnwindRecords operations policy (contracts.insert owner contract) tables world nextStack (added ++ disposals) ∧
    RecursiveRequirements.Checked store (OwnerPhases.ofStack tables tail) (available (ownedTickets whole)) capReq capRow ∧
    RecursiveRequirements.Checked store [] (spendAll (available (ownedTickets whole)) capDemand) tailReq tailRow ∧
    (ownedTickets nextStack).Nodup ∧
    spend (available (ownedTickets nextStack)) owner = available (ownedTickets whole) ∧
    RecursiveRequirements.Checked store (OwnerPhases.ofStack tables nextStack) (available (ownedTickets nextStack))
      (.invoke ⟨owner, .resume⟩ capDemand []) capRow ∧
    closingDemand.Perm capDemand ∧
    (∀ row, closingRow = some row →
      RecursiveRequirements.Checked store (OwnerPhases.ofStack tables nextStack) (available (ownedTickets nextStack))
        (.invoke ⟨owner, .dispose⟩ closingDemand []) row) ∧
    (ClosingEffects (requestRow ++ capRow) (OwnerPhases.ofStack tables tail)
      (available (ownedTickets whole)) closingRequirements →
      ClauseRowAdmission.Interface owner contract.erase permitsDisposal store
        (OwnerPhases.ofStack tables tail) (available (ownedTickets nextStack)) requestRow) := by
  let closingRow := evaluate [] (OwnerPhases.ofStack tables tail) (available (ownedTickets whole)) closingRequirements
  let added : Store := [(⟨owner, .dispose⟩, ⟨closingDemand, closingRequirements⟩)]
  let contract : Contract := ⟨input, answer, capScope.held,
    capDemand, capRow, closingDemand, closingRow, resumeEffects, closeEffects⟩
  have chosen := closing.capture_with_template (owner := owner)
    (input := ScopedPorts.embedPort input.erase.port) (answer := handler.answer) (caller := handler.scope)
    cut unprotected summary
  have keys : ∀ key body, (key, body) ∈ added → key.owner = owner ∧ key.mode = .dispose := by
    intro key body member
    cases List.mem_singleton.mp member
    exact ⟨rfl, rfl⟩
  obtain ⟨boundary, closingAfter, savedAfter, tailAfter, afterUnique, phaseSame, resumeChecked⟩ :=
    allocate_split cut source annotation scope saved waiting sameRecords savedCheck tailCheck unique fresh freshAction
      resume close closingDemand closingRow chosen keys
  have extension := SourceDependencyAnnotations.insert_extends (contract := contract) contracts fresh
  have permissions := Syntax.fresh_usage_insert_extends (rights := rights) freshAction
  have ready : ∀ nested ∈ ownedTickets capture, available (ownedTickets whole) nested = .available := by
    intro nested member
    apply if_pos
    rw [handler_cut_reconstructs cut, owned_tickets_append]
    exact List.mem_append_left _ member
  have balanced := SourceDependencyOwners.Lexical.captured_modes_balance boundary closingAfter afterUnique
    SourceTemplates.CapturedIn.here internal
    (saved.transport extension permissions (List.Subset.refl _)) savedAfter ready
    (summary.transport extension (List.Subset.refl _))
  have closingChecked : ∀ row, closingRow = some row →
      RecursiveRequirements.Checked
        (((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) ++ (added ++ disposals))
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail))
        (available (ownedTickets (.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail)))
        (.invoke ⟨owner, .dispose⟩ closingDemand []) row := by
    intro row evaluated
    apply closing_invocation_from_record summary ?_ afterUnique ?_
    · rw [RecursiveDisposalCapture.lookup_after_resumes]
      · simp [added, RecursiveRequirements.lookup]
      · intro key body member
        rcases List.mem_cons.mp member with same | old
        · cases same; rfl
        · exact source.record_mode old
    · simpa only [phaseSame] using evaluated
  refine ⟨boundary, closingAfter, savedAfter, tailAfter, afterUnique, phaseSame, resumeChecked, balanced, closingChecked, ?_⟩
  intro effects
  have captureUnique : (ownedTickets capture).Nodup := by
    have decomposed := unique
    rw [handler_cut_reconstructs cut, owned_tickets_append] at decomposed
    exact (List.nodup_append.mp decomposed).1
  obtain ⟨actualRow, evaluated, covered⟩ := summary.checked_effects (entries := []) effects captureUnique ready
  have callerFresh := OwnerPhaseTransitions.capture_tail_fresh (tables := tables) cut (source.fresh_unowned fresh)
  refine ⟨?_, ?_, ?_, ?_, callerFresh⟩
  · simpa only [OwnerPhases.ofStack, contract, Contract.erase, saved.realizes.held] using resumeChecked
  · intro _ row same
    simpa only [OwnerPhases.ofStack, contract, Contract.erase, saved.realizes.held] using closingChecked row same
  · intro _
    exact ⟨actualRow, evaluated⟩
  · intro _ row same
    have sameRow : actualRow = row := Option.some.inj (evaluated.symm.trans same)
    exact sameRow ▸ covered

#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.allocate_disposing_split

#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.allocate_split
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.closing_invocation_from_record
end Ash.OneShot.SourceDependencySchemes.Lexical

namespace Ash.OneShot.SourceDependencySchemes.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations SourceDependencyFrames
open RecursiveRequirements (Requirements Store)
open OwnerPhaseTransitions (available spend spendAll)

/-- Clause usage supplies consumption; the established demand balance then
joins the checked clause and waiting source at their actual owner phases. -/
theorem complete_allocated_clause
    (known : contracts owner = some contract)
    (selected : ClauseAt operation clauses parameter binder code)
    (capabilities : ClausesUse policy clauses)
    (payload : ValueSummary operations policy contracts world Environment.empty payloadAllowed operand argument)
    (closed : ClosedValue operand)
    (current : Expression operations policy contracts world allowed (.ticket binder owner) Environment.empty
      (code.subst parameter operand) answer clauseDemand clauseRequirements dependencies)
    (currentCheck : RecursiveRequirements.Checked entries (OwnerPhases.ofStack tables stack) initial clauseRequirements clauseRow)
    (ready : initial owner = .available)
    (phases : spend initial owner = before)
    (balanced : contract.closeDemand.Perm contract.resumeDemand)
    (tailCheck : RecursiveRequirements.Checked entries [] (spendAll before contract.resumeDemand) tailRequirements tailRow) :
    clauseDemand.Perm (owner :: contract.resumeDemand) ∧
    RecursiveRequirements.Checked entries [] initial
      (.sequence (clauseRequirements.prepend (OwnerPhases.ofStack tables stack))
        (.sequence (.spent owner) tailRequirements)) (clauseRow ++ tailRow) := by
  have operandUsage := SourceOwnerClosure.expression_usage
    (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase payload)) rfl
  have usage := ScopedExpressions.usage_substitution (ScopedExecution.selected_clause_usage selected capabilities) closed.1 operandUsage parameter
  have erased := DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase current)
  have completed := RecursiveClauseUsage.consuming_usage_completed erased usage currentCheck
  have sameDemand := RecursiveClauseOwnership.consuming_clause_balance (contract := contract.erase) erased
    (by simp only [Contracts.erase, known, Option.map_some]) currentCheck ready completed balanced
  have consumed : before owner = .consumed := phases ▸ OwnerPhaseTransitions.spend_self initial owner
  have afterOwner : spendAll before contract.resumeDemand owner = .consumed :=
    RecursiveTransport.phases_spendAll_later owner consumed
  have waiting : RecursiveRequirements.Checked entries [] (spendAll initial clauseDemand)
      (.sequence (.spent owner) tailRequirements) tailRow := by
    rw [PhaseRechecking.spendAll_permutation sameDemand]
    simpa only [spendAll, phases, List.nil_append, Contract.erase] using
      (RecursiveRequirements.Checked.sequence (RecursiveRequirements.Checked.spent (store := entries) (receiving := []) afterOwner) tailCheck)
  exact ⟨sameDemand, RecursiveRequirements.Checked.sequence
    (RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.append_nil] using currentCheck)) waiting⟩
end Ash.OneShot.SourceDependencySchemes.Lexical
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.complete_allocated_clause

namespace Ash.OneShot.SourceDependencySchemes.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations SourceDependencyFrames
open RecursiveRequirements (Requirements Store evaluate)
open OwnerPhaseTransitions (available spend spendAll)

theorem allocate_disposing_clause_from_split
    (cut : HandlerCut requested whole capture tail handler)
    (source : LexicalSegment operations policy contracts tables families actions world
      whole input output demand requirements records wholeScope incoming outgoing)
    (annotation : answer.erase.port = ScopedPorts.eraseType handler.answer)
    (scope : ScopedPorts.EffectScopeKnown contracts.erase.ports handler.scope)
    (saved : LexicalSegment operations policy contracts tables families actions world
      capture input answer capDemand capReq capRecords capScope incoming residual)
    (waiting : LexicalSegment operations policy contracts tables families actions world
      tail answer output tailDemand tailReq tailRecords tailScope residual outgoing)
    (sameRecords : records = capRecords ++ tailRecords)
    (savedCheck : RecursiveRequirements.Checked (records ++ disposals) (OwnerPhases.ofStack tables tail)
      (available (ownedTickets whole)) capReq capRow)
    (tailCheck : RecursiveRequirements.Checked (records ++ disposals) []
      (spendAll (available (ownedTickets whole)) capDemand) tailReq tailRow)
    (unique : (ownedTickets whole).Nodup)
    (fresh : contracts owner = none) (freshAction : actions owner = none)
    (resume : code.requiredActions.resume = true → resumeEffects = residual)
    (close : code.requiredActions.dispose = true → closeEffects = residual)
    (closing : UnwindRecords operations policy contracts tables world whole disposals)
    (unprotected : ProtectionContexts.protectedMode capture.erase = false)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (summary : UnwindTemplate operations policy contracts tables world capture closingDemand closingRequirements)
    (declaration : DeclaredSourceFrames.Frame operations.erase policy contracts.erase tables world
      (.handler handler) answer.erase answer.erase [] (.request [] []))
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (body : ∀ (contract : Contract), contracts owner = none →
      contract.input = input → contract.answer = answer →
      contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
      contract.held = capScope.held → contract.closeDemand.Perm contract.resumeDemand →
      Body operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
        (Environment.empty.extend parameter argument) code answer
        ⟨owner, contract.erase, permitsDisposal, advertised⟩ dependencies)
    (payload : ValueSummary operations policy contracts world Environment.empty payloadAllowed operand argument)
    (closed : ClosedValue operand)
    (exported : residualize (CallableProtectionFrames.contextOf tables tail) advertised = some requestRow)
    (effects : ClosingEffects (requestRow ++ capRow) (OwnerPhases.ofStack tables tail)
      (available (ownedTickets whole)) closingRequirements) :
    let closingRow := evaluate [] (OwnerPhases.ofStack tables tail) (available (ownedTickets whole)) closingRequirements
    let contract : Contract := ⟨input, answer, capScope.held,
      capDemand, capRow, closingDemand, closingRow, resumeEffects, closeEffects⟩
    let nextStack := Stack.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail
    let nextResumes : Store := (⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records
    let nextDisposals : Store := (⟨owner, .dispose⟩, ⟨closingDemand, closingRequirements⟩) :: disposals
    let entries := nextResumes ++ nextDisposals
    RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩
      ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩ [.ticket owner] [] ∧
    ownedTickets nextStack = owner :: ownedTickets whole ∧
    (ownedTickets nextStack).Nodup ∧
    closingDemand.Perm capDemand ∧
    LexicalSegment operations policy (contracts.insert owner contract) tables families
      (actions.insert owner code.requiredActions) world nextStack answer output tailDemand
      (.sequence (.spent owner) tailReq) nextResumes (.live owner capScope tailScope) residual outgoing ∧
    UnwindRecords operations policy (contracts.insert owner contract) tables world nextStack nextDisposals ∧
    RecursiveRequirements.Checked entries [] (spendAll (available (ownedTickets whole)) capDemand) tailReq tailRow ∧
    ∃ clauseDemand, ∃ clauseRequirements : Requirements clauseDemand, ∃ clauseRow,
      Expression operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
        Environment.empty (code.subst parameter operand) answer clauseDemand clauseRequirements dependencies ∧
      RecursiveRequirements.Checked entries (OwnerPhases.ofStack tables nextStack)
        (available (ownedTickets nextStack)) clauseRequirements clauseRow ∧
      EffectBounds.Covers (requestRow ++ capRow) clauseRow ∧
      clauseDemand.Perm (owner :: capDemand) ∧
      RecursiveRequirements.Checked entries [] (available (ownedTickets nextStack))
        (.sequence (clauseRequirements.prepend (OwnerPhases.ofStack tables nextStack))
          (.sequence (.spent owner) tailReq)) (clauseRow ++ tailRow) ∧
      (clauseDemand ++ tailDemand).Perm (ownedTickets nextStack) := by
  let closingRow := evaluate [] (OwnerPhases.ofStack tables tail) (available (ownedTickets whole)) closingRequirements
  let contract : Contract := ⟨input, answer, capScope.held,
    capDemand, capRow, closingDemand, closingRow, resumeEffects, closeEffects⟩
  let nextStack := Stack.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail
  obtain ⟨boundary, closingAfter, savedAfter, tailAfter, afterUnique, phaseSame,
    resumeChecked, balanced, closingChecked, buildInterface⟩ :=
    allocate_disposing_split (requestRow := requestRow) (permitsDisposal := permitsDisposal)
      cut source annotation scope saved waiting sameRecords savedCheck tailCheck unique fresh freshAction
      resume close closing unprotected internal summary
  have interface := buildInterface effects
  have extension := SourceDependencyAnnotations.insert_extends (contract := contract) contracts fresh
  have operandAfter := Values.extension (Values.change_allowed payload closed.1 residual) extension
  have selectedBody := body contract fresh rfl rfl rfl rfl rfl balanced
  have known : (contracts.insert owner contract) owner = some contract := by simp [Contracts.insert]
  have callerReady : ∀ other ∈ activeTickets tail, available (ownedTickets nextStack) other = .available := by
    intro other member
    apply if_pos
    exact List.mem_cons.mpr (Or.inr (List.mem_append_right _ (active_tickets_owned tail member)))
  have actualExport : OwnerSource.exportAt (OwnerPhases.ofStack tables tail)
      (available (ownedTickets nextStack)) advertised = some requestRow :=
    (RecursivePlanAdmission.caller_export callerReady).trans exported
  obtain ⟨clauseDemand, clauseRequirements, clauseRow, expression, checked, covered⟩ :=
    boundary.instantiate_clause closingAfter known selectedBody operandAfter closed interface actualExport
  have ready : ClosedExcept parameter code := by
    cases declaration with
    | handler typed annotation declarations capabilities modes => cases typed with
      | handler scope clauses coverage unique =>
          obtain ⟨inputPort, outputPort, knownPort, bodyTyped⟩ := ScopedPorts.selected_clause_typed selected clauses
          exact ScopedPorts.typed_suffix_ready bodyTyped
  have raw := RawStep.capture requested operation parameter binder owner operand code caller whole capture tail handler
    (ScopedPorts.embedPort input.erase.port) cut selected closed ready
  have actualChecked : RecursiveRequirements.Checked (((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) ++ ((⟨owner, .dispose⟩, ⟨closingDemand, closingRequirements⟩) :: disposals))
      (OwnerPhases.ofStack tables nextStack) (available (ownedTickets nextStack)) clauseRequirements clauseRow := by
    simpa only [nextStack, OwnerPhases.ofStack, contract, Contract.erase, saved.realizes.held, List.cons_append, List.nil_append] using checked
  have capabilities : ClausesUse policy handler.clauses := by
    cases declaration with | handler typed annotation declarations capabilities modes => exact capabilities
  obtain ⟨clauseBalance, combined⟩ := complete_allocated_clause known selected capabilities operandAfter closed
    expression actualChecked (by simp [available, nextStack, ownedTickets]) phaseSame balanced tailAfter
  have owned := SourceDependencyOwners.Lexical.source_ownership_balance expression boundary closingAfter afterUnique combined
  refine ⟨raw, RecursiveCapture.capture_owned cut, afterUnique, balanced, boundary, closingAfter, tailAfter,
    clauseDemand, clauseRequirements, clauseRow, expression, actualChecked, covered, clauseBalance, combined, owned⟩

end Ash.OneShot.SourceDependencySchemes.Lexical
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.allocate_disposing_clause_from_split

namespace Ash.OneShot.SourceDependencySchemes.Lexical
open ScopedExpressions ScopedExecution
open SourceDependencyAnnotations
open SourceDependencyFrames
open SourceDependencyCapture (Scope OwnerCut OwnerSelection)
open RecursiveRequirements (Requirements Store Key)
open SourceDependencySchemes.Closing (Bound)

/-- A disposal entry retains its actual source and the annotation recorded at
capture. Bound connects that annotation to the live source scope at invocation. -/
inductive UnwindAnnotated (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Contracts) (tables : CallableProtectionFrames.Tables) (families : Families)
    (annotations : Nat → Option SourceDependencyCapture.Scope) (world : List Nat) (root : Stack) :
    Key → RecursiveRequirements.Template → Prop where
  | dispose (located : SourceTemplates.CapturedIn owner capture root)
      (unprotected : ProtectionContexts.protectedMode capture.erase = false)
      (recorded : annotations owner = some capturedScope)
      (source : UnwindSource operations policy contracts tables families world capture demand requirements capturedScope) :
      UnwindAnnotated operations policy contracts tables families annotations world root
        ⟨owner, .dispose⟩ ⟨demand, requirements⟩

/-- Reuse the existing source and capture-provenance transports. -/
theorem UnwindAnnotated.transport
    (record : UnwindAnnotated operations policy contracts tables families annotations world root key body)
    (extension : contracts.Extends nextContracts)
    (annotationExtension : ∀ owner captured, annotations owner = some captured → nextAnnotations owner = some captured)
    (larger : world ⊆ nextWorld)
    (locations : ∀ owner capture, SourceTemplates.CapturedIn owner capture root →
      SourceTemplates.CapturedIn owner capture nextRoot) :
    UnwindAnnotated operations policy nextContracts tables families nextAnnotations nextWorld nextRoot key body := by
  cases record with
  | dispose located unprotected recorded source =>
      exact .dispose (locations _ _ located) unprotected (annotationExtension _ _ recorded)
        (source.transport extension larger)

theorem UnwindAnnotated.certified
    (record : UnwindAnnotated operations policy contracts tables families annotations world root key body) :
    UnwindCertified operations policy contracts tables world root key body := by
  cases record with
  | dispose located unprotected recorded source => exact .dispose located unprotected source.template

/-- The selected store body and the selected lexical dependency scope name
one captured source, even when its code admits multiple valid annotations. -/
theorem selected_unwind_source
    (records : ∀ key body, (key, body) ∈ (disposals : Store) →
      UnwindAnnotated operations policy contracts tables families annotations world root key body)
    (found : RecursiveRequirements.lookup ⟨owner, .dispose⟩ disposals = some ⟨demand, requirements⟩)
    (bound : Bound annotations receiving)
    (cut : OwnerCut owner receiving selected)
    (located : SourceTemplates.CapturedIn owner capture root)
    (unique : (ownedTickets root).Nodup) :
    UnwindSource operations policy contracts tables families world capture demand requirements selected.captured := by
  cases records _ _ (SourceTemplates.lookup_member found) with
  | dispose actual unprotected recorded source =>
      cases SourceTemplates.captured_in_unique unique actual located
      cases Option.some.inj (recorded.symm.trans (bound.selected cut))
      exact source

/-- Administrative record filtering retains the same annotation and actual
saved source for every surviving payload. -/
theorem annotated_records_advance
    (step : LexicalUnwind.Advance before after discharged)
    (records : ∀ key body, (key, body) ∈ (entries : Store) →
      UnwindAnnotated operations policy contracts tables families annotations world before key body) :
    ∀ key body, (key, body) ∈ unwindStore before entries →
      UnwindAnnotated operations policy contracts tables families annotations world after key body := by
  intro key body member
  have previous := records key body (unwind_store_sublist.subset member)
  cases previous with
  | dispose located unprotected recorded source =>
      exact .dispose (SourceDependencyOwners.Lexical.unwind_record_location step located member)
        unprotected recorded source

/-- Source-scope unwinding retains the already recorded live annotations.
Opening a dormant capture preserves its children before retiring its owner. -/
theorem bound_advance
    (step : LexicalUnwind.Advance before after discharged)
    (realized : SourceDependencyCapture.Realizes tables families scope before)
    (bound : Bound annotations scope) : Bound annotations scope.afterUnwind := by
  cases step with
  | plain => cases realized with | push frame tail => cases frame with
      | plain => cases bound with | plain rest => exact rest
  | handler => cases realized with | push frame tail => cases frame with
      | handler => cases bound with | handler rest => exact rest
  | cell => cases realized with | push frame tail => cases frame with
      | cell => cases bound with | cell rest => exact rest
  | spent => cases realized with | spent tail => cases bound with | spent rest => exact rest
  | retire => cases realized with | push frame tail => cases frame with
      | retiring => cases bound with | running rest => exact rest
  | live => cases realized with | live saved tail => cases bound with
      | live recorded inside rest => exact Bound.append_iff.mpr ⟨inside, .running rest⟩

/-- Capture records the chosen annotation together with the actual stored
requirements; existing records retain their prior annotations and provenance. -/
theorem capture_annotated_records
    (cut : HandlerCut requested whole capture tail handler)
    (source : UnwindSource operations policy contracts tables families world capture demand requirements capturedScope)
    (unprotected : ProtectionContexts.protectedMode capture.erase = false)
    (scopeSame : receiving = capturedScope.append tailScope)
    (bound : Bound annotations receiving) (fresh : annotations owner = none)
    (records : ∀ key body, (key, body) ∈ (entries : Store) →
      UnwindAnnotated operations policy contracts tables families annotations world whole key body)
    (extension : contracts.Extends nextContracts) :
    let nextAnnotations := fun other => if other = owner then some capturedScope else annotations other
    Bound nextAnnotations (.live owner capturedScope tailScope) ∧
    ∀ key body, (key, body) ∈ ((⟨owner, .dispose⟩, ⟨demand, requirements⟩) :: entries) →
      UnwindAnnotated operations policy nextContracts tables families nextAnnotations world
        (.live owner input answer capture caller tail) key body := by
  let nextAnnotations := fun other => if other = owner then some capturedScope else annotations other
  have annotationExtension : ∀ other scope, annotations other = some scope → nextAnnotations other = some scope := by
    intro other scope known
    by_cases same : other = owner
    · subst other; rw [fresh] at known; cases known
    · simpa only [nextAnnotations, if_neg same] using known
  obtain ⟨savedBound, tailBound⟩ := Bound.append_iff.mp (scopeSame ▸ bound)
  refine ⟨savedBound.capture tailBound fresh, ?_⟩
  intro key body member
  rcases List.mem_cons.mp member with same | previous
  · cases same
    exact .dispose .here unprotected (by simp) (source.transport extension (List.Subset.refl _))
  · exact (records key body previous).transport extension annotationExtension (List.Subset.refl _) (by
      intro other saved located
      rw [handler_cut_reconstructs cut] at located
      rcases SavedCaptureIdentity.located_append.mp located with inside | outside
      · exact .saved inside
      · exact .tail outside)
/-- Lexical disposal retains captured scopes behind the actual closing marker.
Reuse annotation splitting, without the old materialized-plan projection. -/
theorem bound_lexical_discard
    (bound : Bound annotations receiving) (cut : OwnerCut owner receiving selected) :
    Bound annotations (selected.captured.append
      (.running (selected.front.append (.spent owner selected.tail)))) := by
  rw [cut.reconstruct] at bound
  obtain ⟨front, boundary⟩ := Bound.append_iff.mp bound
  cases boundary with
  | live recorded saved tail =>
      exact Bound.append_iff.mpr ⟨saved, .running (Bound.append_iff.mpr ⟨front, .spent tail⟩)⟩

/-- Reordering the saved scopes and waiting caller preserves every surviving
record's exact source witness. Only the invoked owner's entries are removed. -/
theorem annotated_records_discard {front capture tail : Stack}
    (records : ∀ key body, (key, body) ∈ (entries : Store) →
      UnwindAnnotated operations policy contracts tables families annotations world
        (front.append (.live owner input answer capture caller tail)) key body)
    (same : (RecursiveTransport.removeOwner owner entries).Perm nextEntries) :
    ∀ key body, (key, body) ∈ nextEntries →
      UnwindAnnotated operations policy contracts tables families annotations world
        (capture.append (.push (.closing identity runtimeScope)
          (front.append (.spent owner answer caller tail)))) key body := by
  intro key body member
  have kept := same.mem_iff.mpr member
  cases records key body (RecursiveTransport.remove_owner_sublist.subset kept) with
  | dispose located unprotected recorded source =>
      have moved := SourceDependencyOwners.Lexical.resume_record_location located kept
      refine .dispose ?_ unprotected recorded source
      rcases SavedCaptureIdentity.located_append.mp moved with inside | outside
      · exact SavedCaptureIdentity.located_append.mpr (Or.inl inside)
      · exact SavedCaptureIdentity.located_append.mpr (Or.inr (.push outside))

end Ash.OneShot.SourceDependencySchemes.Lexical
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.UnwindAnnotated.transport
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.UnwindAnnotated.certified
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.selected_unwind_source
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.annotated_records_advance
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.bound_advance
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.capture_annotated_records

#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.bound_lexical_discard
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.annotated_records_discard


namespace Ash.OneShot.SourceDependencySchemes.Lexical
open ScopedExpressions ScopedExecution
open SourceDependencyAnnotations SourceDependencyFrames
open RecursiveRequirements (Store)

/-- Resumption uses the same record removal and saved-source recomposition.
The existing lexical disposal proof differs only by an inert closing marker. -/
theorem annotated_records_resume {front capture tail : Stack}
    (records : ∀ key body, (key, body) ∈ (entries : Store) →
      UnwindAnnotated operations policy contracts tables families annotations world
        (front.append (.live owner input answer capture caller tail)) key body)
    (same : (RecursiveTransport.removeOwner owner entries).Perm nextEntries) :
    ∀ key body, (key, body) ∈ nextEntries →
      UnwindAnnotated operations policy contracts tables families annotations world
        (capture.append (front.append (.spent owner answer caller tail))) key body := by
  intro key body member
  have checked := annotated_records_discard (identity := 0) (runtimeScope := .none) records same key body member
  exact checked.transport (fun _ _ known => known) (fun _ _ known => known) (List.Subset.refl _) (by
    intro other saved located
    rcases SavedCaptureIdentity.located_append.mp located with inside | outside
    · exact SavedCaptureIdentity.located_append.mpr (Or.inl inside)
    · cases outside with
      | push rest => exact SavedCaptureIdentity.located_append.mpr (Or.inr rest))
end Ash.OneShot.SourceDependencySchemes.Lexical
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.annotated_records_resume

namespace Ash.OneShot.SourceDependencySchemes.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations SourceDependencyFrames
open RecursiveRequirements (Requirements Store evaluate)
open OwnerPhaseTransitions (available spend spendAll)

theorem allocate_resuming_clause_from_split
    (cut : HandlerCut requested whole capture tail handler)
    (source : LexicalSegment operations policy contracts tables families actions world
      whole input output demand requirements records wholeScope incoming outgoing)
    (annotation : answer.erase.port = ScopedPorts.eraseType handler.answer)
    (scope : ScopedPorts.EffectScopeKnown contracts.erase.ports handler.scope)
    (saved : LexicalSegment operations policy contracts tables families actions world
      capture input answer capDemand capReq capRecords capScope incoming residual)
    (waiting : LexicalSegment operations policy contracts tables families actions world
      tail answer output tailDemand tailReq tailRecords tailScope residual outgoing)
    (sameRecords : records = capRecords ++ tailRecords)
    (savedCheck : RecursiveRequirements.Checked (records ++ disposals) (OwnerPhases.ofStack tables tail)
      (available (ownedTickets whole)) capReq capRow)
    (tailCheck : RecursiveRequirements.Checked (records ++ disposals) []
      (spendAll (available (ownedTickets whole)) capDemand) tailReq tailRow)
    (unique : (ownedTickets whole).Nodup)
    (fresh : contracts owner = none) (freshAction : actions owner = none)
    (resume : code.requiredActions.resume = true → resumeEffects = residual)
    (close : code.requiredActions.dispose = true → closeEffects = residual)
    (closing : UnwindRecords operations policy contracts tables world whole disposals)
    (recorded : ∀ key body, (key, body) ∈ disposals →
      UnwindAnnotated operations policy contracts tables families annotations world whole key body)
    (annotationBound : SourceDependencySchemes.Closing.Bound annotations (capScope.append tailScope))
    (freshAnnotation : annotations owner = none)
    (declaration : DeclaredSourceFrames.Frame operations.erase policy contracts.erase tables world
      (.handler handler) answer.erase answer.erase [] (.request [] []))
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (body : ∀ (contract : Contract), contracts owner = none →
      contract.input = input → contract.answer = answer →
      contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
      contract.held = capScope.held → contract.closeDemand.Perm contract.resumeDemand →
      Body operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
        (Environment.empty.extend parameter argument) code answer
        ⟨owner, contract.erase, permitsDisposal, advertised⟩ dependencies)
    (payload : ValueSummary operations policy contracts world Environment.empty payloadAllowed operand argument)
    (closed : ClosedValue operand)
    (exported : residualize (CallableProtectionFrames.contextOf tables tail) advertised = some requestRow)
    (noDispose : permitsDisposal = false) :
    let contract : Contract := ⟨input, answer, capScope.held,
      capDemand, capRow, capDemand, none, resumeEffects, closeEffects⟩
    let nextStack := Stack.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail
    let nextResumes : Store := (⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records
    let nextAnnotations := fun other => if other = owner then some capScope else annotations other
    ∃ nextDisposals : Store,
      SourceDependencySchemes.Closing.Bound nextAnnotations (.live owner capScope tailScope) ∧
      (∀ key body, (key, body) ∈ nextDisposals →
        UnwindAnnotated operations policy (contracts.insert owner contract) tables families nextAnnotations world nextStack key body) ∧
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩
        ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩ [.ticket owner] [] ∧
      ownedTickets nextStack = owner :: ownedTickets whole ∧
      (ownedTickets nextStack).Nodup ∧
      LexicalSegment operations policy (contracts.insert owner contract) tables families
        (actions.insert owner code.requiredActions) world nextStack answer output tailDemand
        (.sequence (.spent owner) tailReq) nextResumes (.live owner capScope tailScope) residual outgoing ∧
      UnwindRecords operations policy (contracts.insert owner contract) tables world nextStack nextDisposals ∧
      RecursiveRequirements.Checked (nextResumes ++ nextDisposals) []
        (spendAll (available (ownedTickets whole)) capDemand) tailReq tailRow ∧
      ∃ clauseDemand, ∃ clauseRequirements : Requirements clauseDemand, ∃ clauseRow,
        Expression operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
          Environment.empty (code.subst parameter operand) answer clauseDemand clauseRequirements dependencies ∧
        RecursiveRequirements.Checked (nextResumes ++ nextDisposals) (OwnerPhases.ofStack tables nextStack)
          (available (ownedTickets nextStack)) clauseRequirements clauseRow ∧
        EffectBounds.Covers (requestRow ++ capRow) clauseRow ∧
        clauseDemand.Perm (owner :: capDemand) ∧
        RecursiveRequirements.Checked (nextResumes ++ nextDisposals) [] (available (ownedTickets nextStack))
          (.sequence (clauseRequirements.prepend (OwnerPhases.ofStack tables nextStack))
            (.sequence (.spent owner) tailReq)) (clauseRow ++ tailRow) ∧
        (clauseDemand ++ tailDemand).Perm (ownedTickets nextStack) := by
  let contract : Contract := ⟨input, answer, capScope.held,
    capDemand, capRow, capDemand, none, resumeEffects, closeEffects⟩
  let nextStack := Stack.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail
  let nextAnnotations := fun other => if other = owner then some capScope else annotations other
  have annotationExtension : ∀ other captured, annotations other = some captured → nextAnnotations other = some captured := by
    intro other captured known
    by_cases same : other = owner
    · subst other; rw [freshAnnotation] at known; cases known
    · simpa only [nextAnnotations, if_neg same] using known
  obtain ⟨savedBound, tailBound⟩ := SourceDependencySchemes.Closing.Bound.append_iff.mp annotationBound
  have nextBound := savedBound.capture tailBound freshAnnotation
  have preserved : ∀ key body, (key, body) ∈ disposals →
      UnwindAnnotated operations policy contracts tables families nextAnnotations world nextStack key body := by
    intro key body member
    exact (recorded key body member).transport (fun _ _ known => known) annotationExtension (List.Subset.refl _) (by
      intro other captured located
      rw [handler_cut_reconstructs cut] at located
      rcases SavedCaptureIdentity.located_append.mp located with inside | outside
      · exact .saved inside
      · exact .tail outside)
  obtain ⟨added, chosen, keys, annotated⟩ : ∃ added : Store,
      UnwindRecords operations policy contracts tables world nextStack (added ++ disposals) ∧
      (∀ key template, (key, template) ∈ added → key.owner = owner ∧ key.mode = .dispose) ∧
      (∀ key template, (key, template) ∈ added ++ disposals →
        UnwindAnnotated operations policy contracts tables families nextAnnotations world nextStack key template) := by
    cases held : ProtectionContexts.protectedMode capture.erase with
    | true =>
        exact ⟨[], closing.capture_protected cut held, (by intro key template member; cases member), preserved⟩
    | false =>
        obtain ⟨closingDemand, closingRequirements, summary⟩ := saved.unwind_source held
        refine ⟨[(⟨owner, .dispose⟩, ⟨closingDemand, closingRequirements⟩)],
          closing.capture_with_template cut held summary.template, ?_, ?_⟩
        · intro key template member
          cases List.mem_singleton.mp member
          exact ⟨rfl, rfl⟩
        · intro key template member
          rcases List.mem_cons.mp member with same | old
          · cases same
            exact .dispose .here held (by simp [nextAnnotations]) summary
          · exact preserved key template old
  obtain ⟨boundary, closingAfter, savedAfter, tailAfter, afterUnique, phaseSame, resumeChecked⟩ :=
    allocate_split cut source annotation scope saved waiting sameRecords savedCheck tailCheck unique fresh freshAction
      resume close capDemand none chosen keys
  have interface : ClauseRowAdmission.Interface owner contract.erase permitsDisposal
      (((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) ++ (added ++ disposals))
      (OwnerPhases.ofStack tables tail) (available (ownedTickets nextStack)) requestRow := by
    apply ClauseRowAdmission.Interface.of_resume _ noDispose
      (OwnerPhaseTransitions.capture_tail_fresh cut (source.fresh_unowned fresh))
    simpa only [OwnerPhases.ofStack, contract, Contract.erase, saved.realizes.held] using resumeChecked
  have extension := SourceDependencyAnnotations.insert_extends (contract := contract) contracts fresh
  have operandAfter := Values.extension (Values.change_allowed payload closed.1 residual) extension
  have selectedBody := body contract fresh rfl rfl rfl rfl rfl (List.Perm.refl _)
  have known : (contracts.insert owner contract) owner = some contract := by simp [Contracts.insert]
  have callerReady : ∀ other ∈ activeTickets tail, available (ownedTickets nextStack) other = .available := by
    intro other member
    apply if_pos
    exact List.mem_cons.mpr (Or.inr (List.mem_append_right _ (active_tickets_owned tail member)))
  have actualExport : OwnerSource.exportAt (OwnerPhases.ofStack tables tail)
      (available (ownedTickets nextStack)) advertised = some requestRow :=
    (RecursivePlanAdmission.caller_export callerReady).trans exported
  obtain ⟨clauseDemand, clauseRequirements, clauseRow, expression, checked, covered⟩ :=
    boundary.instantiate_clause closingAfter known selectedBody operandAfter closed interface actualExport
  have ready : ClosedExcept parameter code := by
    cases declaration with
    | handler typed annotation declarations capabilities modes => cases typed with
      | handler scope clauses coverage unique =>
          obtain ⟨inputPort, outputPort, knownPort, bodyTyped⟩ := ScopedPorts.selected_clause_typed selected clauses
          exact ScopedPorts.typed_suffix_ready bodyTyped
  have raw := RawStep.capture requested operation parameter binder owner operand code caller whole capture tail handler
    (ScopedPorts.embedPort input.erase.port) cut selected closed ready
  have actualChecked : RecursiveRequirements.Checked (((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: records) ++ (added ++ disposals))
      (OwnerPhases.ofStack tables nextStack) (available (ownedTickets nextStack)) clauseRequirements clauseRow := by
    simpa only [nextStack, OwnerPhases.ofStack, contract, Contract.erase, saved.realizes.held, List.cons_append, List.nil_append] using checked
  have capabilities : ClausesUse policy handler.clauses := by
    cases declaration with | handler typed annotation declarations capabilities modes => exact capabilities
  obtain ⟨clauseBalance, combined⟩ := complete_allocated_clause known selected capabilities operandAfter closed
    expression actualChecked (by simp [available, nextStack, ownedTickets]) phaseSame (List.Perm.refl _) tailAfter
  have owned := SourceDependencyOwners.Lexical.source_ownership_balance expression boundary closingAfter afterUnique combined
  have nextAnnotated : ∀ key template, (key, template) ∈ added ++ disposals →
      UnwindAnnotated operations policy (contracts.insert owner contract) tables families nextAnnotations world nextStack key template := by
    intro key template member
    exact (annotated key template member).transport extension (fun _ _ known => known) (List.Subset.refl _) (fun _ _ located => located)
  refine ⟨added ++ disposals, nextBound, nextAnnotated, raw, RecursiveCapture.capture_owned cut, afterUnique, boundary, closingAfter, tailAfter,
    clauseDemand, clauseRequirements, clauseRow, expression, actualChecked, covered, clauseBalance, combined, owned⟩

end Ash.OneShot.SourceDependencySchemes.Lexical
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.allocate_resuming_clause_from_split

namespace Ash.OneShot.SourceDependencySchemes.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations SourceDependencyFrames
open SourceDependencyChecks.Lexical (Local Pending)
open SourceDependencyCapture (OwnerCut OwnerSelection)
open RecursiveRequirements (Requirements Store evaluate)
open OwnerPhaseTransitions (Phases Trace available spend spendAll)
open RecursiveConsumption (remove_owner_append)
variable {front capture tail : Stack}

/-- Reuse recursive removal, phase transport and rich append to check the
recomposed source with its actual lexical cleanup records. -/
theorem resume_segments
    (source : LexicalSegment operations policy contracts tables families actions world
      (front.append (.live owner inputType answerType capture caller tail)) contract.answer output pendingDemand pendingRequirements resumes wholeScope incoming outgoing)
    (closing : UnwindRecords operations policy contracts tables world
      (front.append (.live owner inputType answerType capture caller tail)) disposals)
    (recorded : ∀ key body, (key, body) ∈ disposals →
      UnwindAnnotated operations policy contracts tables families annotations world
        (front.append (.live owner inputType answerType capture caller tail)) key body)
    (bound : SourceDependencySchemes.Closing.Bound annotations wholeScope)
    (known : contracts owner = some contract) (actionKnown : actions owner = some rights)
    (permitted : rights.resume = true) (allowed : contract.resumeEffects ⊆ incoming)
    (unique : (ownedTickets (front.append (.live owner inputType answerType capture caller tail))).Nodup)
    (invocation : RecursiveRequirements.Checked (resumes ++ disposals)
      (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType capture caller tail)))
      (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
      (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) resumeRow)
    (localCheck : Local outward actions
      (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
      world (.invoke ⟨owner, .resume⟩) wholeScope)
    (pending : RecursiveRequirements.Checked (resumes ++ disposals) []
      (spendAll (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
        (owner :: contract.resumeDemand)) pendingRequirements pendingRow) :
    ∃ (combined : Requirements (contract.resumeDemand ++ pendingDemand)) (nextResumes nextDisposals : Store) (nextScope : DependencyScope),
      LexicalSegment operations policy contracts tables families actions world (capture.append (front.append (.spent owner answerType caller tail)))
        contract.input output (contract.resumeDemand ++ pendingDemand) combined nextResumes nextScope [] outgoing ∧
      UnwindRecords operations policy contracts tables world (capture.append (front.append (.spent owner answerType caller tail))) nextDisposals ∧
      SourceDependencySchemes.Closing.Bound annotations nextScope ∧
      (∀ key body, (key, body) ∈ nextDisposals →
        UnwindAnnotated operations policy contracts tables families annotations world
          (capture.append (front.append (.spent owner answerType caller tail))) key body) ∧
      RecursiveRequirements.Checked (nextResumes ++ nextDisposals) []
        (available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))))
        combined (resumeRow ++ pendingRow) ∧
      (RecursiveTransport.removeOwner owner (resumes ++ disposals)).Perm (nextResumes ++ nextDisposals) ∧
      (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))).Nodup ∧
      Trace (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))) [owner]
        (available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail))))) ∧
      Pending outward actions
        (available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))))
        world nextScope .nil ∧
      (contract.resumeDemand ++ pendingDemand).Perm
        (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))) := by
  obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, capturedScope, waitingScope,
    capturedBoundary, savedOriginal, savedInterface, waiting, permutation, scopeSplit, waitingEvaluation⟩ :=
    lexical_extract_live source known actionKnown
  have saved := savedOriginal.outgoing_weaken (savedInterface permitted)
  obtain ⟨nextDisposals, nextClosing, disposalPermutation⟩ := UnwindRecords.resume closing unique
  have resumeUnique := RecursiveTransport.record_keys_unique (source.record_owners_sublist.nodup unique)
  have ownersUnique := source.record_owners_sublist.nodup unique
  have resumePermutation := RecursiveRecomposition.removed_records ownersUnique permutation
  have erasedPermutation : (RecursiveTransport.removeOwner owner (resumes ++ disposals)).Perm
      ((capturedRecords ++ waitingRecords) ++ nextDisposals) := by
    rw [remove_owner_append]
    exact resumePermutation.append disposalPermutation
  have keysUnique := source.combined_unwind_keys_unique closing unique
  have erasedUnique := RecursiveTransport.remove_owner_unique (owner := owner) keysUnique
  have capturedKnown := RecursiveRecords.lookup_append (second := disposals)
    (RecursiveTransport.lookup_of_member resumeUnique (permutation.mem_iff.mpr List.mem_cons_self))
  obtain ⟨body, selectedContext, actual, ready, selection, bodyChecked⟩ := RecursiveRequirements.checked_invocation invocation
  have sameTemplate := Option.some.inj (actual.symm.trans capturedKnown)
  have sameBody := eq_of_heq (Sigma.mk.inj sameTemplate).2
  subst body
  let initial := available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))
  have consumed : spend initial owner owner = .consumed := OwnerPhaseTransitions.spend_self initial owner
  have contexts : RecursiveTransport.normalize (spend initial owner)
      (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType capture caller tail))) =
      RecursiveTransport.normalize (spend initial owner)
        (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail))) := by
    simpa only [List.append_nil] using (RecursiveRecomposition.normalize_replaced (front := front) (capture := capture) (tail := tail)
      (input := inputType) (answer := answerType) (caller := caller) (tables := tables) (receiving := []) consumed)
  have bodyWaiting := RecursiveTransport.checked_transport bodyChecked
    (RecursiveTransport.remove_consumed_agrees consumed) contexts
  have bodyCollected := RecursiveTransport.checked_permuted bodyWaiting erasedUnique erasedPermutation
  have consumedAfter : spendAll initial (owner :: contract.resumeDemand) owner = .consumed := by
    rw [OwnerPhaseTransitions.spendAll_at, if_pos List.mem_cons_self]
  have pendingWaiting : RecursiveRequirements.Checked (resumes ++ disposals) []
      (spendAll initial (owner :: contract.resumeDemand)) waitingReq pendingRow := by
    apply RecursiveRequirements.evaluate_sound
    rw [waitingEvaluation (resumes ++ disposals) [] _ consumedAfter]
    exact RecursiveRequirements.checked_complete pending
  have pendingErased := RecursiveTransport.checked_remove_consumed pendingWaiting consumedAfter
  have pendingCollected := RecursiveTransport.checked_permuted pendingErased erasedUnique erasedPermutation
  obtain ⟨combined, combinedSource, combinedEvaluation⟩ := lexical_segment_append saved (waiting.input_weaken allowed)
  have combinedCheck : RecursiveRequirements.Checked ((capturedRecords ++ waitingRecords) ++ nextDisposals) []
      (spend initial owner) combined (resumeRow ++ pendingRow) := by
    apply RecursiveRequirements.evaluate_sound
    rw [combinedEvaluation]
    have first := RecursiveRequirements.checked_complete bodyCollected
    have second := RecursiveRequirements.checked_complete pendingCollected
    change evaluate _ _ (spend initial owner) capturedReq = some resumeRow at first
    change evaluate _ [] (spendAll (spend initial owner) contract.resumeDemand) waitingReq = some pendingRow at second
    rw [List.append_nil, first, second]
    rfl
  have trace := OwnerPhaseTransitions.resume_phase_trace unique
  have actualPhases := OwnerPhaseTransitions.trace_result trace
  change available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))) =
    spend initial owner at actualPhases
  rw [← actualPhases] at combinedCheck
  have afterUnique := (List.nodup_cons.mp (OwnerPhaseTransitions.resume_owned_permutation.nodup unique)).2
  obtain ⟨frontScope, tailScope, frontRealized, wholeSame, waitingSame⟩ := scopeSplit
  have prefixUnique : (ownedTickets front ++ owner :: (ownedTickets capture ++ ownedTickets tail)).Nodup := by
    simpa only [owned_tickets_append, ownedTickets] using unique
  have absent : owner ∉ ownedTickets front := fun member =>
    (List.nodup_append.mp prefixUnique).2.2 owner member owner List.mem_cons_self rfl
  have cut : OwnerCut owner wholeScope ⟨frontScope, capturedScope, tailScope⟩ := by
    rw [wholeSame]
    exact SourceDependencySchemes.Closing.prefix_owner_cut frontRealized absent
  have retained : Pending outward actions
      (available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))))
      world (capturedScope.append waitingScope) .nil := by
    cases localCheck with
    | resume access restored => cases access with
      | checked located known permission ready =>
          have same := Option.some.inj (located.lookup.symm.trans cut.lookup)
          cases same
          simpa only [OwnerSelection.resumed, waitingSame, actualPhases] using restored
  have balanced := SourceDependencyOwners.Lexical.segment_ownership_balance
    combinedSource nextClosing afterUnique combinedCheck
  have nextBound := (bound.invocations cut).1
  have nextAnnotated := annotated_records_resume recorded disposalPermutation
  exact ⟨combined, _, nextDisposals, _, combinedSource, nextClosing,
    (by simpa only [OwnerSelection.resumed, waitingSame] using nextBound), nextAnnotated, combinedCheck, erasedPermutation, afterUnique, trace,
    retained, balanced⟩

end Ash.OneShot.SourceDependencySchemes.Lexical
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.resume_segments

namespace Ash.OneShot.SourceDependencySchemes.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations SourceDependencyFrames
open SourceDependencyChecks.Lexical (Local Pending)
open RecursiveRequirements (Requirements Store)
open OwnerPhaseTransitions (available spendAll)
variable {front capture tail : Stack}

/-- A typed current resume supplies the invocation and waiting checks to
recomposition. The actual runtime step retains the same source annotations. -/
theorem resume_source
    (current : Expression operations policy contracts world allowed runtimeScope Environment.empty
      (.resume binder value) input currentDemand currentRequirements dependencies)
    (source : LexicalSegment operations policy contracts tables families actions world
      (front.append (.live owner inputType answerType capture caller tail)) input output
      pendingDemand pendingRequirements resumes wholeScope allowed outgoing)
    (closing : UnwindRecords operations policy contracts tables world
      (front.append (.live owner inputType answerType capture caller tail)) disposals)
    (recorded : ∀ key body, (key, body) ∈ disposals →
      UnwindAnnotated operations policy contracts tables families annotations world
        (front.append (.live owner inputType answerType capture caller tail)) key body)
    (bound : SourceDependencySchemes.Closing.Bound annotations wholeScope)
    (known : contracts owner = some contract) (actionKnown : actions owner = some rights)
    (permitted : rights.resume = true)
    (resolved : runtimeScope.resolve binder = some owner) (isValue : value.IsValue)
    (bounds : LexicalUnwind.ReentryBounds front capture tail (LexicalUnwind.returnMode capture .ordinary))
    (unique : (ownedTickets (front.append (.live owner inputType answerType capture caller tail))).Nodup)
    (localCheck : Local outward actions
      (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
      world dependencies wholeScope)
    (checked : RecursiveRequirements.Checked (resumes ++ disposals) []
      (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
      (.sequence (currentRequirements.prepend
        (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType capture caller tail))))
        pendingRequirements) row) :
    ∃ nextRequirements : Requirements (contract.resumeDemand ++ pendingDemand),
    ∃ nextResumes nextDisposals nextScope,
      currentDemand ++ pendingDemand = owner :: (contract.resumeDemand ++ pendingDemand) ∧
      ValueSummary operations policy contracts world Environment.empty [] value contract.input ∧
      LexicalUnwind.UseTransition
        (.eval ⟨.resume binder value, runtimeScope, front.append (.live owner inputType answerType capture caller tail)⟩)
        (.eval ⟨value, runtimeScope, capture.append (front.append (.spent owner answerType caller tail))⟩)
        [] [.ticket owner] ∧
      LexicalSegment operations policy contracts tables families actions world
        (capture.append (front.append (.spent owner answerType caller tail))) contract.input output
        (contract.resumeDemand ++ pendingDemand) nextRequirements nextResumes nextScope [] outgoing ∧
      UnwindRecords operations policy contracts tables world
        (capture.append (front.append (.spent owner answerType caller tail))) nextDisposals ∧
      SourceDependencySchemes.Closing.Bound annotations nextScope ∧
      (∀ key body, (key, body) ∈ nextDisposals →
        UnwindAnnotated operations policy contracts tables families annotations world
          (capture.append (front.append (.spent owner answerType caller tail))) key body) ∧
      RecursiveRequirements.Checked (nextResumes ++ nextDisposals) []
        (available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))))
        nextRequirements row ∧
      (RecursiveTransport.removeOwner owner (resumes ++ disposals)).Perm (nextResumes ++ nextDisposals) ∧
      (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))).Nodup ∧
      Pending outward actions
        (available (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))))
        world nextScope .nil ∧
      (contract.resumeDemand ++ pendingDemand).Perm
        (ownedTickets (capture.append (front.append (.spent owner answerType caller tail)))) := by
  cases current with
  | resume currentKnown currentResolved permission operand admitted formed =>
      cases Option.some.inj (currentResolved.symm.trans resolved)
      cases Option.some.inj (currentKnown.symm.trans known)
      have empty := SourceTemplates.expression_value_demand
        (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase operand)) isValue
      have payload := Values.change_allowed (Values.summary operand isValue) isValue []
      have closed := ScopedPorts.typed_value_closed
        ((DeclaredSourceValues.erase (value_erase payload)).ports .none) isValue
      have invokeLocal := (Local.silent_prefix (value_silent operand isValue)).mp localCheck
      obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, rows⟩ :=
        RecursiveRequirements.checked_sequence_parts checked
      have atStack := RecursiveRequirements.checked_prepend_iff.mp currentCheck
      simp only [List.append_nil] at atStack
      obtain ⟨operandRow, resumeRow, operandCheck, invocation, currentRows⟩ :=
        RecursiveRequirements.checked_sequence_parts atStack
      have operandEmpty := Option.some.inj ((RecursiveRequirements.checked_complete operandCheck).symm.trans
        (RecursiveRecomposition.value_evaluation
          (DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase operand)) isValue))
      subst operandRow
      simp only [List.nil_append] at currentRows
      subst currentRow
      simp only [empty, List.nil_append, spendAll] at invocation pendingCheck
      obtain ⟨combined, nextResumes, nextDisposals, nextScope, nextSource, nextClosing, nextBound, nextAnnotated, combinedCheck,
        permutation, afterUnique, trace, retained, balanced⟩ :=
        resume_segments source closing recorded bound known actionKnown permitted admitted unique invocation invokeLocal pendingCheck
      refine ⟨combined, nextResumes, nextDisposals, nextScope, ?_, payload,
        .resume binder owner runtimeScope caller inputType answerType front capture tail value closed resolved bounds,
        nextSource, nextClosing, nextBound, nextAnnotated, ?_, permutation, afterUnique, retained, balanced⟩
      · simp only [empty, List.nil_append, List.cons_append]
      · simpa only [rows] using combinedCheck
end Ash.OneShot.SourceDependencySchemes.Lexical
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.resume_source


namespace Ash.OneShot.SourceDependencySchemes.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations SourceDependencyFrames
open SourceDependencyChecks.Lexical (Local Pending Unwind)
open SourceDependencyCapture (OwnerCut OwnerSelection)
open RecursiveRequirements (Requirements Store evaluate)
open OwnerPhaseTransitions (available spend spendAll)
variable {front capture tail : Stack}

/-- Disposal retains the actual stored summary and waiting source. Cleanup
coverage is checked at the surviving closing marker and actual caller. -/
theorem discard_source
    (current : Expression operations policy contracts world allowed runtimeScope Environment.empty
      (.discard binder) input currentDemand currentRequirements dependencies)
    (source : LexicalSegment operations policy contracts tables families actions world
      (front.append (.live owner inputType answerType capture caller tail)) input output
      pendingDemand pendingRequirements resumes wholeScope allowed outgoing)
    (closing : UnwindRecords operations policy contracts tables world
      (front.append (.live owner inputType answerType capture caller tail)) disposals)
    (recorded : ∀ key body, (key, body) ∈ disposals →
      UnwindAnnotated operations policy contracts tables families annotations world
        (front.append (.live owner inputType answerType capture caller tail)) key body)
    (bound : SourceDependencySchemes.Closing.Bound annotations wholeScope)
    (known : contracts owner = some contract) (actionKnown : actions owner = some rights)
    (resolved : runtimeScope.resolve binder = some owner)
    (unique : (ownedTickets (front.append (.live owner inputType answerType capture caller tail))).Nodup)
    (frontBound : InternalUses (ownedTickets front ++ ownedTickets tail) front.erase.pending)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending)
    (tailBound : InternalUses (ownedTickets tail) tail.erase.pending)
    (localCheck : Local outward actions
      (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
      world dependencies wholeScope)
    (checked : RecursiveRequirements.Checked (resumes ++ disposals) []
      (available (ownedTickets (front.append (.live owner inputType answerType capture caller tail))))
      (.sequence (currentRequirements.prepend
        (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType capture caller tail))))
        pendingRequirements) row) :
    ∃ capturedReq : Requirements contract.resumeDemand,
    ∃ waitingReq : Requirements pendingDemand,
    ∃ closingReq : Requirements contract.closeDemand,
    ∃ capturedRecords waitingRecords nextDisposals capturedScope waitingScope capturedBoundary closingRow pendingRow,
      let waitingStack := front.append (.spent owner answerType caller tail)
      let nextStack := capture.append (.push (.closing identity runtimeScope) waitingStack)
      let after := available (ownedTickets nextStack)
      let entries := (capturedRecords ++ waitingRecords) ++ nextDisposals
      currentDemand ++ pendingDemand = owner :: (contract.closeDemand ++ pendingDemand) ∧
      row = closingRow ++ pendingRow ∧
      LexicalSegment operations policy contracts tables families actions world capture contract.input contract.answer
        contract.resumeDemand capturedReq capturedRecords capturedScope [] capturedBoundary ∧
      LexicalSegment operations policy contracts tables families actions world waitingStack .unit output
        pendingDemand waitingReq waitingRecords waitingScope allowed outgoing ∧
      UnwindSource operations policy contracts tables families world capture contract.closeDemand closingReq capturedScope ∧
      SourceDependencySchemes.Closing.Bound annotations (capturedScope.append (.running waitingScope)) ∧
      (∀ key body, (key, body) ∈ nextDisposals →
        UnwindAnnotated operations policy contracts tables families annotations world nextStack key body) ∧
      UnwindRecords operations policy contracts tables world nextStack nextDisposals ∧
      (RecursiveTransport.removeOwner owner (resumes ++ disposals)).Perm entries ∧
      (ownedTickets nextStack).Nodup ∧
      (contract.closeDemand ++ pendingDemand).Perm (ownedTickets nextStack) ∧
      LexicalUnwind.UseTransition
        (.eval ⟨.discard binder, runtimeScope, front.append (.live owner inputType answerType capture caller tail)⟩)
        (.unwind runtimeScope nextStack) [.close identity] [.ticket owner] ∧
      Unwind outward actions after world capturedScope (.running waitingScope) ∧
      Pending outward actions after world waitingScope .nil ∧
      RecursiveRequirements.Checked entries [] (spendAll after contract.closeDemand) waitingReq pendingRow ∧
      (ClosingEffects closingRow (OwnerPhases.ofStack tables (.push (.closing identity runtimeScope) waitingStack))
        after closingReq →
        ∃ actualRow, RecursiveRequirements.Checked entries [] after
          (.sequence (closingReq.prepend (OwnerPhases.ofStack tables (.push (.closing identity runtimeScope) waitingStack)))
            waitingReq) (actualRow ++ pendingRow) ∧
          EffectBounds.Covers row (actualRow ++ pendingRow)) := by
  have originalBalance := SourceDependencyOwners.Lexical.source_ownership_balance current source closing unique checked
  cases current with
  | discard currentKnown currentResolved permission unprotected admitted =>
      cases Option.some.inj (currentResolved.symm.trans resolved)
      cases Option.some.inj (currentKnown.symm.trans known)
      obtain ⟨capturedReq, capturedRecords, waitingReq, waitingRecords, capturedScope, waitingScope,
        capturedBoundary, saved, savedInterface, waiting, permutation, scopeSplit, waitingEvaluation⟩ :=
        lexical_extract_live source known actionKnown
      obtain ⟨closingRow, pendingRow, invoked, pendingCheck, rows⟩ :=
        RecursiveRequirements.checked_sequence_parts checked
      have invocation := RecursiveRequirements.checked_prepend_iff.mp invoked
      simp only [List.append_nil] at invocation
      obtain ⟨closingReq, selectedContext, looked, ready, selection, bodyChecked⟩ :=
        RecursiveRequirements.checked_invocation invocation
      have stored := looked
      rw [RecursiveDisposalCapture.lookup_after_resumes (fun key body member => source.record_mode member)] at stored
      obtain ⟨actualUnprotected, summary⟩ := closing.selected_template unique stored
      obtain ⟨nextDisposals, nextClosing, disposalPermutation⟩ := closing.discard (identity := identity) (runtimeScope := runtimeScope) unique
      have resumePermutation := RecursiveRecomposition.removed_records (source.record_owners_sublist.nodup unique) permutation
      have removed : (RecursiveTransport.removeOwner owner (resumes ++ disposals)).Perm
          ((capturedRecords ++ waitingRecords) ++ nextDisposals) := by
        rw [RecursiveConsumption.remove_owner_append]
        exact resumePermutation.append disposalPermutation
      have keysUnique := source.combined_unwind_keys_unique closing unique
      let initial := available (ownedTickets (front.append (.live owner inputType answerType capture caller tail)))
      let waitingStack := front.append (.spent owner answerType caller tail)
      let nextStack := capture.append (.push (.closing identity runtimeScope) waitingStack)
      have phaseSame : available (ownedTickets nextStack) = spend initial owner := by
        have actual := OwnerPhaseTransitions.trace_result (OwnerPhaseTransitions.resume_phase_trace unique)
        simpa only [nextStack, waitingStack, initial, spendAll, owned_tickets_append, ownedTickets] using actual
      have afterUnique : (ownedTickets nextStack).Nodup := by
        have actual := (List.nodup_cons.mp (OwnerPhaseTransitions.resume_owned_permutation.nodup unique)).2
        simpa only [nextStack, waitingStack, owned_tickets_append, ownedTickets] using actual
      have afterBalance : (contract.closeDemand ++ pendingDemand).Perm (ownedTickets nextStack) := by
        apply List.Perm.cons_inv (a := owner)
        have combined := originalBalance.trans OwnerPhaseTransitions.resume_owned_permutation
        simpa only [nextStack, waitingStack, owned_tickets_append, ownedTickets, List.cons_append] using combined
      have consumed : spendAll initial (owner :: contract.closeDemand) owner = .consumed := by
        rw [OwnerPhaseTransitions.spendAll_at, if_pos List.mem_cons_self]
      have pendingWaiting : RecursiveRequirements.Checked (resumes ++ disposals) []
          (spendAll initial (owner :: contract.closeDemand)) waitingReq pendingRow := by
        apply RecursiveRequirements.evaluate_sound
        rw [waitingEvaluation (resumes ++ disposals) [] _ consumed]
        exact RecursiveRequirements.checked_complete pendingCheck
      have pendingErased := RecursiveTransport.checked_remove_consumed pendingWaiting consumed
      have pendingCollected := RecursiveTransport.checked_permuted pendingErased
        (RecursiveTransport.remove_owner_unique (owner := owner) keysUnique) removed
      have actualPending : RecursiveRequirements.Checked ((capturedRecords ++ waitingRecords) ++ nextDisposals) []
          (spendAll (available (ownedTickets nextStack)) contract.closeDemand) waitingReq pendingRow := by
        simpa only [phaseSame, spendAll] using pendingCollected
      obtain ⟨frontScope, tailScope, frontRealized, wholeSame, waitingSame⟩ := scopeSplit
      have prefixUnique : (ownedTickets front ++ owner :: (ownedTickets capture ++ ownedTickets tail)).Nodup := by
        simpa only [owned_tickets_append, ownedTickets] using unique
      have absent : owner ∉ ownedTickets front := fun member =>
        (List.nodup_append.mp prefixUnique).2.2 owner member owner List.mem_cons_self rfl
      have cut : OwnerCut owner wholeScope ⟨frontScope, capturedScope, tailScope⟩ := by
        rw [wholeSame]
        exact SourceDependencySchemes.Closing.prefix_owner_cut frontRealized absent
      have authenticated := selected_unwind_source recorded stored bound cut
        (RecursiveRecords.located_below front .here) unique
      have nextBound := bound_lexical_discard bound cut
      have nextAnnotated := annotated_records_discard (identity := identity) (runtimeScope := runtimeScope)
        recorded disposalPermutation
      have checkedScopes : Unwind outward actions (available (ownedTickets nextStack)) world capturedScope (.running waitingScope) ∧
          Pending outward actions (available (ownedTickets nextStack)) world waitingScope .nil := by
        cases localCheck with
        | dispose located known permission available unprotected callbacks retained =>
            have same := Option.some.inj (located.lookup.symm.trans cut.lookup)
            cases same
            simpa only [waitingSame, phaseSame] using And.intro callbacks retained
      refine ⟨capturedReq, waitingReq, closingReq, capturedRecords, waitingRecords, nextDisposals,
        capturedScope, waitingScope, capturedBoundary, closingRow, pendingRow,
        by simp only [List.cons_append], rows, saved, waiting, authenticated, (by simpa only [waitingSame] using nextBound), nextAnnotated, nextClosing, removed, afterUnique, afterBalance,
        .discard binder owner identity runtimeScope caller inputType answerType front capture tail resolved
          actualUnprotected frontBound internal tailBound, checkedScopes.1, checkedScopes.2, actualPending, ?_⟩
      intro effects
      have captureUnique : (ownedTickets capture).Nodup :=
        (List.nodup_append.mp (List.nodup_cons.mp (List.nodup_append.mp prefixUnique).2.1).2).1
      have captureReady : ∀ other ∈ ownedTickets capture, available (ownedTickets nextStack) other = .available := by
        intro other member
        apply if_pos
        simpa only [nextStack, owned_tickets_append] using
          List.mem_append_left (ownedTickets (.push (.closing identity runtimeScope) waitingStack)) member
      obtain ⟨actualRow, evaluated, covered⟩ := summary.checked_effects effects captureUnique captureReady
      refine ⟨actualRow, RecursiveRequirements.Checked.sequence
        (RecursiveRequirements.checked_prepend_iff.mpr ?_) actualPending, ?_⟩
      · simpa only [List.append_nil] using RecursiveRequirements.evaluate_sound evaluated
      · rw [rows]
        exact ScopedExpressions.append_subset covered (List.Subset.refl _)
end Ash.OneShot.SourceDependencySchemes.Lexical
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.discard_source

namespace Ash.OneShot.SourceScheduledPhaseRestriction
open ScopedExpressions
open SourceDependencyCapture (Scope OwnerSelection OwnerCut)
open SourceDependencyOwners (owners)
open SourceDependencyProjection (project)
open OwnerPhaseTransitions (Phases spend)
open SourceContextualHints (Hints)
/-- The phase-transport obligation is restricted to an explicit finite owner
set. It grants no permission and makes no claim that a continuation exists. -/
def AvailableOn (names : List Nat) (before after : Phases) : Prop :=
  ∀ owner ∈ names, before owner = .available → after owner = .available

theorem AvailableOn.weaken (extension : AvailableOn names before after) (included : smaller ⊆ names) :
    AvailableOn smaller before after := fun owner member ready => extension owner (included member) ready

theorem AvailableOn.spend (extension : AvailableOn names before after) :
    AvailableOn names (spend before owner) (spend after owner) := by
  intro other member ready
  by_cases same : other = owner
  · subst other; rw [OwnerPhaseTransitions.spend_self] at ready; cases ready
  · rw [OwnerPhaseTransitions.spend_other same] at ready ⊢
    exact extension other member ready

theorem owners_append (first second : Scope) : owners (first.append second) = owners first ++ owners second := by
  induction first <;> simp_all [Scope.append, owners, List.append_assoc]

theorem owners_closing (scope : Scope) : owners scope.forClosing ⊆ owners scope := by
  induction scope with
  | nil => exact List.Subset.refl _
  | plain dependencies rest ih | handler effect table families rest ih | spent owner rest ih
  | cell identity rest ih | cleanup needs body rest ih | running rest ih => exact ih
  | live owner saved rest ihSaved ihRest =>
      simp only [Scope.forClosing, owners_append, owners]
      exact List.Subset.trans (ScopedExpressions.append_subset ihSaved ihRest) (List.subset_cons_self _ _)

private theorem scope_hints (scope : Scope) : Nonempty (Hints scope) := by
  induction scope with
  | nil => exact ⟨.nil⟩
  | plain dependencies rest ih => obtain ⟨rest⟩ := ih; exact ⟨.plain rest⟩
  | handler effect table families rest ih => obtain ⟨rest⟩ := ih; exact ⟨.handler [] rest⟩
  | cell identity rest ih => obtain ⟨rest⟩ := ih; exact ⟨.cell rest⟩
  | cleanup needs body rest ih => obtain ⟨rest⟩ := ih; exact ⟨.cleanup rest⟩
  | running rest ih => obtain ⟨rest⟩ := ih; exact ⟨.running rest⟩
  | spent owner rest ih => obtain ⟨rest⟩ := ih; exact ⟨.spent rest⟩
  | live owner saved rest ihSaved ihRest => obtain ⟨saved⟩ := ihSaved; obtain ⟨rest⟩ := ihRest; exact ⟨.live saved rest⟩

/-- Reuse annotated lookup's existing cut theorem solely to recover its
underlying scope equation; no checking certificate is constructed here. -/
theorem selected_scope
    (found : SourceDependencyCapture.select effect operation scope = some (.handler saved tail contract modes)) :
    scope = saved.append tail := by
  obtain ⟨hints⟩ := scope_hints scope
  obtain ⟨savedHints, waitingHints, cut⟩ := SourcePlannedCuts.of_lookup hints found
  exact cut.reconstruct_scope

theorem selected_owner (cut : OwnerCut owner scope selected) : owner ∈ owners scope := by
  rw [cut.reconstruct, owners_append]
  exact List.mem_append_right _ List.mem_cons_self

theorem resumed_owners (cut : OwnerCut owner scope selected) : owners (selected.resumed owner) ⊆ owners scope := by
  rw [cut.reconstruct]
  simp only [OwnerSelection.resumed, owners_append, owners]
  intro other member
  simp only [List.mem_append, List.mem_cons] at member ⊢
  rcases member with inside | front | tail
  · exact Or.inr (Or.inr (Or.inl inside))
  · exact Or.inl front
  · exact Or.inr (Or.inr (Or.inr tail))

theorem disposed_owners (cut : OwnerCut owner scope selected) : owners (selected.disposed owner) ⊆ owners scope := by
  apply List.Subset.trans (l₂ := owners (selected.resumed owner))
  · simp only [OwnerSelection.disposed, OwnerSelection.resumed, owners_append, owners]
    exact ScopedExpressions.append_subset (owners_closing _) (List.Subset.refl _)
  · exact resumed_owners cut

end Ash.OneShot.SourceScheduledPhaseRestriction

#print axioms Ash.OneShot.SourceScheduledPhaseRestriction.AvailableOn.weaken
#print axioms Ash.OneShot.SourceScheduledPhaseRestriction.AvailableOn.spend
#print axioms Ash.OneShot.SourceScheduledPhaseRestriction.owners_append
#print axioms Ash.OneShot.SourceScheduledPhaseRestriction.owners_closing
#print axioms Ash.OneShot.SourceScheduledPhaseRestriction.selected_scope
#print axioms Ash.OneShot.SourceScheduledPhaseRestriction.selected_owner
#print axioms Ash.OneShot.SourceScheduledPhaseRestriction.resumed_owners
#print axioms Ash.OneShot.SourceScheduledPhaseRestriction.disposed_owners

namespace Ash.OneShot.SourceDependencySchemes.Lexical
open SourceDependencyChecks.Lexical (Local Pending Unwind)
open SourceDependencyCapture (Scope OwnerSelection)
open SourceDependencyOwners (owners)
open SourceScheduledPhaseRestriction
open OwnerPhaseTransitions (spend)

/-- Lexical checks observe phases only at retained live owners. Reuse the
existing finite owner-set transport and exact cut equations. -/
theorem local_restrict
    (source : Local outward actions before world dependencies scope)
    (extension : AvailableOn (owners scope) before after) :
    Local outward actions after world dependencies scope := by
  refine Local.rec
    (motive_1 := fun before world dependencies scope _ => ∀ after, AvailableOn (owners scope) before after →
      Local outward actions after world dependencies scope)
    (motive_2 := fun before world forest outside _ => ∀ after, AvailableOn (owners (forest.append outside)) before after →
      Pending outward actions after world forest outside)
    (motive_3 := fun before world forest outside _ => ∀ after, AvailableOn (owners (forest.append outside)) before after →
      Unwind outward actions after world forest outside)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ source after extension
  · intros; exact .pure
  · intro scope effect operation phases world guarded callbacks ownerBound ih after extension
    apply Local.request guarded _ ownerBound
    intro captured tail contract modes found disposes
    apply ih captured tail contract modes found disposes after
    simpa only [selected_scope found, SourceScheduledPhaseRestriction.owners_append, owners] using extension
  · intro phases owner scope result world access restored ih after extension
    cases access with
    | checked located known permission available =>
      apply Local.resume (.checked located known permission (extension _ (selected_owner located) available))
      apply ih (spend after owner)
      apply extension.spend.weaken
      simpa only [SourceScheduledPhaseRestriction.owners_append, owners, List.append_nil] using resumed_owners located
  · intros
    rename_i located known permission available held callbacks waiting ihCallbacks ihWaiting after extension
    apply Local.dispose located known permission (extension _ (selected_owner located) available) held
    · apply ihCallbacks (spend after _)
      apply extension.spend.weaken
      simpa only [OwnerSelection.resumed, SourceScheduledPhaseRestriction.owners_append, owners] using resumed_owners located
    · apply ihWaiting (spend after _)
      apply extension.spend.weaken
      rw [located.reconstruct]
      simp only [SourceScheduledPhaseRestriction.owners_append, owners, List.append_nil]
      intro other member
      rcases List.mem_append.mp member with front | tail
      · exact List.mem_append_left _ front
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_append_right _ tail))
  · intro phases world before next scope first second ihFirst ihSecond after extension
    exact .sequence (ihFirst after extension) (ihSecond after extension)
  · intro phases world first scope second left right ihLeft ihRight after extension
    exact .choice (ihLeft after extension) (ihRight after extension)
  · intro phases world dependencies effect table families scope body ih after extension
    exact .handler (ih after extension)
  · intro phases world dependencies needs callback scope body completion ihBody ihCallback after extension
    exact .cleanup (ihBody after extension) (ihCallback after extension)
  · intro world phases family scope body ih after extension
    exact .resource (fun identity fresh => ih identity fresh after extension)
  · intros; exact .nil
  · intro phases world dependencies rest outside code tail ihCode ihTail after extension
    exact .plain (ihCode after extension) (ihTail after extension)
  · intro phases world rest outside effect table families tail ih after extension
    exact .handler (ih after extension)
  · intro phases world rest outside identity tail ih after extension
    exact .cell (ih after extension)
  · intro phases world dependencies rest outside needs completion tail ihCode ihTail after extension
    exact .cleanup (ihCode after extension) (ihTail after extension)
  · intro phases world rest outside tail ih after extension
    exact .running (ih after extension)
  · intro phases world captured rest outside owner saved tail ihSaved ihTail after extension
    apply Pending.live
    · apply ihSaved after
      apply extension.weaken
      simp only [Scope.append, owners, SourceScheduledPhaseRestriction.owners_append]
      exact List.subset_cons_self _ _
    · apply ihTail after
      apply extension.weaken
      simp only [Scope.append, owners, SourceScheduledPhaseRestriction.owners_append]
      intro name member
      exact List.mem_cons_of_mem _ (List.mem_append_right _ member)
  · intro phases world rest outside owner tail ih after extension
    exact .spent (ih after extension)
  · intros; exact .nil
  · intro phases world dependencies rest outside tail ih after extension
    exact .plain (ih after extension)
  · intro phases world rest outside effect table families tail ih after extension
    exact .handler (ih after extension)
  · intro phases world rest outside identity tail ih after extension
    exact .cell (ih after extension)
  · intro phases world dependencies rest outside needs completion tail ihCode ihTail after extension
    exact .cleanup (ihCode after extension) (ihTail after extension)
  · intro phases world rest outside tail ih after extension
    exact .running (ih after extension)
  · intro phases world captured rest outside owner saved tail ihSaved ihTail after extension
    apply Unwind.live
    · apply ihSaved after
      apply extension.weaken
      simp only [Scope.append, owners, SourceScheduledPhaseRestriction.owners_append]
      exact List.subset_cons_self _ _
    · apply ihTail after
      apply extension.weaken
      simp only [Scope.append, owners, SourceScheduledPhaseRestriction.owners_append]
      intro name member
      exact List.mem_cons_of_mem _ (List.mem_append_right _ member)
  · intro phases world rest outside owner tail ih after extension
    exact .spent (ih after extension)

theorem unwind_restrict
    (source : Unwind outward actions before world forest outside)
    (extension : AvailableOn (owners (forest.append outside)) before after) :
    Unwind outward actions after world forest outside := by
  induction forest generalizing outside with
  | nil => exact .nil
  | plain dependencies rest ih => cases source with | plain tail => exact .plain (ih tail extension)
  | handler effect table families rest ih => cases source with | handler tail => exact .handler (ih tail extension)
  | cell identity rest ih => cases source with | cell tail => exact .cell (ih tail extension)
  | cleanup needs dependencies rest ih => cases source with
    | cleanup callback tail => exact .cleanup (local_restrict callback extension) (ih tail extension)
  | running rest ih => cases source with | running tail => exact .running (ih tail extension)
  | live owner captured rest ihCaptured ihRest => cases source with
    | live saved tail =>
        apply Unwind.live
        · apply ihCaptured saved
          apply extension.weaken
          simp only [Scope.append, owners, SourceScheduledPhaseRestriction.owners_append]
          exact List.subset_cons_self _ _
        · apply ihRest tail
          apply extension.weaken
          simp only [Scope.append, owners, SourceScheduledPhaseRestriction.owners_append]
          intro name member
          exact List.mem_cons_of_mem _ (List.mem_append_right _ member)
  | spent owner rest ih => cases source with | spent tail => exact .spent (ih tail extension)
end Ash.OneShot.SourceDependencySchemes.Lexical
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.local_restrict
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.unwind_restrict

namespace Ash.OneShot.SourceConsumingCleanupAdmission
open SourceDependencyOwners (owners)
open SourceScheduledPhaseRestriction (AvailableOn)
/-- The existing scope realization and live-owner inclusion derive the phase
premise from the actual runtime stack. No caller-supplied availability fact is
needed for an owner retained by that same stack. -/
theorem realized_available
    (realized : SourceDependencyCapture.Realizes tables families scope stack) :
    AvailableOn (owners scope) phases (OwnerPhaseTransitions.available (ScopedExecution.ownedTickets stack)) := by
  intro name member _
  rw [SourceDependencyOwners.realized_owners realized] at member
  exact if_pos (ScopedExecution.recursive_live_tickets_owned stack member)

end Ash.OneShot.SourceConsumingCleanupAdmission
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.realized_available


namespace Ash.OneShot.SourceDependencySchemes.Lexical
open ScopedExpressions ScopedExecution
open SourceDependencyFrames

/-- Existing saved-capture origin and uniqueness identify every surviving
record with its prior source certificate. No successor layout is assumed. -/
theorem annotated_records_ordinary_step
    (step : RawStep before after created discharged)
    (ordinary : LexicalUnwind.ordinary before.expression)
    (noCapture : ∀ owner, Owner.ticket owner ∉ created)
    (source : UnwindRecords operations policy contracts tables world before.stack records)
    (annotated : ∀ key body, (key, body) ∈ records →
      UnwindAnnotated operations policy contracts tables families annotations world before.stack key body)
    (unique : (ownedTickets before.stack).Nodup) :
    ∃ retained, UnwindRecords operations policy contracts tables world after.stack retained ∧ retained ⊆ records ∧
      ∀ key body, (key, body) ∈ retained →
        UnwindAnnotated operations policy contracts tables families annotations world after.stack key body := by
  obtain ⟨retained, layout, included⟩ := source.ordinary_step step ordinary noCapture unique
  refine ⟨retained, layout, included, ?_⟩
  intro key body member
  have prior := annotated key body (included member)
  cases prior with
  | dispose located unprotected recorded original =>
      cases layout.certified member with
      | dispose current _ _ =>
          cases SourceTemplates.captured_in_unique unique located
            (SavedCaptureIdentity.raw_step_origin step (noCapture _) current)
          exact .dispose current unprotected recorded original
end Ash.OneShot.SourceDependencySchemes.Lexical
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.annotated_records_ordinary_step


namespace Ash.OneShot.SourceDependencySchemes.Lexical
open ScopedExpressions ScopedExecution
open SourceDependencyCapture (Scope)
open SourceDependencyChecks.Lexical (ModePending ModeFrame)
open SourceDependencyOwners (owners)
open SourceScheduledPhaseRestriction (AvailableOn)

/-- Reuse local capability restriction at every actually executed position.
Only owners retained by this same receiving scope need remain available. -/
theorem mode_pending_restrict
    (source : ModePending outward actions before world tables families stack scope outside initial finalMode)
    (extension : AvailableOn (owners (scope.append outside)) before after) :
    ModePending outward actions after world tables families stack scope outside initial finalMode := by
  induction source with
  | nil => exact .nil
  | push frame tail ih => cases frame with
      | plain code => exact .push (.plain (local_restrict code extension)) (ih extension)
      | skipped => exact .push .skipped (ih extension)
      | handler => exact .push .handler (ih extension)
      | cell => exact .push .cell (ih extension)
      | armed callback => exact .push (.armed (local_restrict callback extension)) (ih extension)
      | running => exact .push .running (ih extension)
      | unwinding => exact .push .unwinding (ih extension)
      | closing => exact .push .closing (ih extension)
      | retiring => exact .push .retiring (ih extension)
  | live saved tail ihSaved ihTail =>
      apply ModePending.live
      · apply ihSaved
        apply extension.weaken
        simp only [Scope.append, owners, SourceScheduledPhaseRestriction.owners_append]
        exact List.subset_cons_self _ _
      · apply ihTail
        apply extension.weaken
        simp only [Scope.append, owners, SourceScheduledPhaseRestriction.owners_append]
        intro name member
        exact List.mem_cons_of_mem _ (List.mem_append_right _ member)
  | opening saved tail ihSaved ihTail =>
      apply ModePending.opening
      · apply ihSaved
        apply extension.weaken
        simp only [Scope.append, owners, SourceScheduledPhaseRestriction.owners_append]
        exact List.subset_cons_self _ _
      · apply ihTail
        apply extension.weaken
        simp only [Scope.append, owners, SourceScheduledPhaseRestriction.owners_append]
        intro name member
        exact List.mem_cons_of_mem _ (List.mem_append_right _ member)
  | spent tail ih => exact .spent (ih extension)

/-- Fresh allocation transports checks at every executed mixed-mode position,
reusing local transport for code and callbacks. -/
theorem mode_pending_transport
    (source : ModePending outward actions before world tables families stack scope outside initial finalMode)
    (extension : PhaseExtension before after) (permissions : Syntax.UsageExtension actions nextActions)
    (larger : world ⊆ nextWorld) :
    ModePending outward nextActions after nextWorld tables families stack scope outside initial finalMode := by
  induction source with
  | nil => exact .nil
  | push frame tail ih => cases frame with
      | plain code => exact .push (.plain (local_transport code extension permissions larger)) ih
      | skipped => exact .push .skipped ih
      | handler => exact .push .handler ih
      | cell => exact .push .cell ih
      | armed callback => exact .push (.armed (local_transport callback extension permissions larger)) ih
      | running => exact .push .running ih
      | unwinding => exact .push .unwinding ih
      | closing => exact .push .closing ih
      | retiring => exact .push .retiring ih
  | live saved tail ihSaved ihTail => exact .live ihSaved ihTail
  | opening saved tail ihSaved ihTail => exact .opening ihSaved ihTail
  | spent tail ih => exact .spent ih

end Ash.OneShot.SourceDependencySchemes.Lexical
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.mode_pending_restrict
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.mode_pending_transport


namespace Ash.OneShot.SourceDependencySchemes.Lexical
open ScopedExpressions ScopedExecution
open SourceDependencyAnnotations SourceDependencyFrames
open SourceDependencyCapture (OwnerCut)
open RecursiveRequirements (Requirements Store Key)
open SourceDependencySchemes.Closing (Bound)

/-- A resume entry pairs its exact stored requirement body with the chosen
rich source and dependency annotation. Its boundary may resume unwinding. -/
inductive ResumeAnnotated (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Contracts) (tables : CallableProtectionFrames.Tables) (families : Families)
    (actions : Syntax.UsageTickets) (annotations : Nat → Option SourceDependencyCapture.Scope)
    (world : List Nat) (root : Stack) : Key → RecursiveRequirements.Template → Prop where
  | resume (located : SourceTemplates.CapturedIn owner captured root)
      (known : contracts owner = some contract)
      (recorded : annotations owner = some capturedScope)
      (source : ModeSource operations policy contracts tables families actions world captured
        (.value contract.input) boundary contract.resumeDemand requirements capturedScope)
      (answer : boundary = .value contract.answer ∨ boundary = .unwind) :
      ResumeAnnotated operations policy contracts tables families actions annotations world root
        ⟨owner, .resume⟩ ⟨contract.resumeDemand, requirements⟩

theorem ResumeAnnotated.transport
    (record : ResumeAnnotated operations policy contracts tables families actions annotations world root key body)
    (extension : contracts.Extends nextContracts) (permissions : Syntax.UsageExtension actions nextActions)
    (annotationExtension : ∀ owner captured, annotations owner = some captured → nextAnnotations owner = some captured)
    (larger : world ⊆ nextWorld)
    (locations : ∀ owner captured, SourceTemplates.CapturedIn owner captured root →
      SourceTemplates.CapturedIn owner captured nextRoot) :
    ResumeAnnotated operations policy nextContracts tables families nextActions nextAnnotations nextWorld nextRoot key body := by
  cases record with
  | resume located known recorded source answer =>
      exact .resume (locations _ _ located) (extension _ _ known) (annotationExtension _ _ recorded)
        (source.transport extension permissions larger) answer

/-- Lookup returns the exact stored source. Contract types and the actual
runtime return mode determine its boundary; no typing-annotation uniqueness
principle is used. -/
theorem selected_resume_source {contract : SourceDependencyAnnotations.Contract}
    {requirements : Requirements contract.resumeDemand}
    (records : ∀ key body, (key, body) ∈ (resumes : Store) →
      ResumeAnnotated operations policy contracts tables families actions annotations world root key body)
    (found : RecursiveRequirements.lookup ⟨owner, .resume⟩ resumes = some ⟨contract.resumeDemand, requirements⟩)
    (bound : Bound annotations receiving)
    (cut : OwnerCut owner receiving selected)
    (located : SourceTemplates.CapturedIn owner captured root)
    (unique : (ownedTickets root).Nodup)
    (known : contracts owner = some contract)
    (mode : LexicalUnwind.returnMode captured .ordinary = boundary.mode)
    (returns : boundary = .value contract.answer ∨ boundary = .unwind) :
    ModeSource operations policy contracts tables families actions world captured
      (.value contract.input) boundary contract.resumeDemand requirements selected.captured := by
  generalize bodySame : (⟨contract.resumeDemand, requirements⟩ : RecursiveRequirements.Template) = stored at found
  cases records _ _ (SourceTemplates.lookup_member found) with
  | resume actual actualKnown recorded source answer =>
      cases SourceTemplates.captured_in_unique unique actual located
      cases Option.some.inj (actualKnown.symm.trans known)
      cases bodySame
      cases Option.some.inj (recorded.symm.trans (bound.selected cut))
      have sameMode := source.return_mode.symm.trans mode
      rcases returns with rfl | rfl <;> rcases answer with rfl | rfl
      · exact source
      · cases sameMode
      · cases sameMode
      · exact source

/-- Fresh capture retains the exact resume body and its chosen annotation.
Older entries keep their source witnesses under the same registry extensions. -/
theorem capture_resume_records {contract : SourceDependencyAnnotations.Contract}
    {requirements : Requirements contract.resumeDemand}
    (cut : HandlerCut requested whole captured tail handler)
    (source : ModeSource operations policy contracts tables families actions world captured
      (.value contract.input) boundary contract.resumeDemand requirements capturedScope)
    (returns : boundary = .value contract.answer ∨ boundary = .unwind)
    (known : nextContracts owner = some contract)
    (scopeSame : receiving = capturedScope.append tailScope)
    (bound : Bound annotations receiving) (fresh : annotations owner = none)
    (records : ∀ key body, (key, body) ∈ (entries : Store) →
      ResumeAnnotated operations policy contracts tables families actions annotations world whole key body)
    (extension : contracts.Extends nextContracts) (permissions : Syntax.UsageExtension actions nextActions) :
    let nextAnnotations := fun other => if other = owner then some capturedScope else annotations other
    Bound nextAnnotations (.live owner capturedScope tailScope) ∧
    ∀ key body, (key, body) ∈ ((⟨owner, .resume⟩, ⟨contract.resumeDemand, requirements⟩) :: entries) →
      ResumeAnnotated operations policy nextContracts tables families nextActions nextAnnotations world
        (.live owner input answer captured caller tail) key body := by
  let nextAnnotations := fun other => if other = owner then some capturedScope else annotations other
  have annotationExtension : ∀ other scope, annotations other = some scope → nextAnnotations other = some scope := by
    intro other scope recorded
    by_cases same : other = owner
    · subst other; rw [fresh] at recorded; cases recorded
    · simpa only [nextAnnotations, if_neg same] using recorded
  obtain ⟨savedBound, tailBound⟩ := Bound.append_iff.mp (scopeSame ▸ bound)
  refine ⟨savedBound.capture tailBound fresh, ?_⟩
  intro key body member
  rcases List.mem_cons.mp member with same | previous
  · cases same
    exact .resume .here known (by simp) (source.transport extension permissions (List.Subset.refl _)) returns
  · exact (records key body previous).transport extension permissions annotationExtension (List.Subset.refl _) (by
      intro other saved located
      rw [handler_cut_reconstructs cut] at located
      rcases SavedCaptureIdentity.located_append.mp located with inside | outside
      · exact .saved inside
      · exact .tail outside)

/-- Administrative unwinding preserves each surviving exact resume body. -/
theorem resume_annotated_records_advance
    (step : LexicalUnwind.Advance before after discharged)
    (records : ∀ key body, (key, body) ∈ (entries : Store) →
      ResumeAnnotated operations policy contracts tables families actions annotations world before key body) :
    ∀ key body, (key, body) ∈ unwindStore before entries →
      ResumeAnnotated operations policy contracts tables families actions annotations world after key body := by
  intro key body member
  cases records key body (unwind_store_sublist.subset member) with
  | resume located known recorded source answer =>
      exact .resume (SourceDependencyOwners.Lexical.unwind_record_location step located member)
        known recorded source answer
end Ash.OneShot.SourceDependencySchemes.Lexical
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.ResumeAnnotated.transport
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.selected_resume_source
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.capture_resume_records
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.resume_annotated_records_advance



namespace Ash.OneShot.SourceDependencySchemes.Lexical
open ScopedExpressions ScopedExecution
open SourceDependencyAnnotations SourceDependencyFrames
open RecursiveRequirements (Store)
/-- Resumption removes the selected owner's records and preserves the exact
source witness for every surviving resume body. -/
theorem resume_annotated_records_resume {front captured tail : Stack}
    (records : ∀ key body, (key, body) ∈ (entries : Store) →
      ResumeAnnotated operations policy contracts tables families actions annotations world
        (front.append (.live owner input answer captured caller tail)) key body) :
    ∀ key body, (key, body) ∈ RecursiveTransport.removeOwner owner entries →
      ResumeAnnotated operations policy contracts tables families actions annotations world
        (captured.append (front.append (.spent owner answer caller tail))) key body := by
  intro key body member
  cases records key body (RecursiveTransport.remove_owner_sublist.subset member) with
  | resume located known recorded source answer =>
      exact .resume (SourceDependencyOwners.Lexical.resume_record_location located member)
        known recorded source answer
end Ash.OneShot.SourceDependencySchemes.Lexical
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.resume_annotated_records_resume



namespace Ash.OneShot.SourceDependencySchemes.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations SourceDependencyFrames
open RecursiveRequirements (Requirements Store Checked)
open OwnerPhaseTransitions (available spendAll)
open RecursiveDisposalCapture
open SourceDependencyOwners.Lexical

/-- Authenticate both record modes once, then reuse the mixed ownership
argument for a current expression or a saved stack. -/
theorem mode_record_ownership_balance
    (records : ∀ key body, (key, body) ∈ (resumes : Store) →
      ResumeAnnotated operations policy contracts tables families actions annotations world stack key body)
    (closing : ∀ key body, (key, body) ∈ (disposals : Store) →
      UnwindAnnotated operations policy contracts tables families annotations world stack key body)
    (unique : (ownedTickets stack).Nodup)
    (checked : RecursiveRequirements.Checked (resumes ++ disposals) receiving (available (ownedTickets stack))
      (requirements : Requirements demand) row)
    (retirements : ∀ owner capture, SourceTemplates.CapturedIn owner capture stack →
      owner ∈ directRetirements requirements → ∀ nested ∈ spineOwners capture,
        spendAll (available (ownedTickets stack)) demand nested = .consumed)
    (spine : ∀ owner ∈ spineOwners stack, spendAll (available (ownedTickets stack)) demand owner = .consumed) :
    demand.Perm (ownedTickets stack) := by
  refine mode_checked_ownership_balance (operations := operations) (policy := policy) (contracts := contracts)
    (tables := tables) (families := families) (actions := actions) (world := world) (entries := resumes ++ disposals)
    (root := stack) ?_ ?_ unique checked retirements spine
  · intro owner demand body found
    rcases List.mem_append.mp (SourceTemplates.lookup_member found) with resumed | disposed
    · cases records _ _ resumed with
      | resume located known recorded source returns => exact ⟨_, _, _, _, located, source⟩
    · cases closing _ _ disposed
  · intro owner demand body found
    rcases List.mem_append.mp (SourceTemplates.lookup_member found) with resumed | disposed
    · cases records _ _ resumed
    · cases closing _ _ disposed with
      | dispose located unprotected recorded source => exact ⟨_, located, source.template.ownership⟩

/-- A checked mixed stack accounts for every physical owner, including
captures opened by unwinding and owners awaiting retirement. -/
theorem mode_stack_ownership_balance
    (source : ModeSource operations policy contracts tables families actions world
      stack input output demand requirements scope)
    (records : ∀ key body, (key, body) ∈ (resumes : Store) →
      ResumeAnnotated operations policy contracts tables families actions annotations world stack key body)
    (closing : ∀ key body, (key, body) ∈ (disposals : Store) →
      UnwindAnnotated operations policy contracts tables families annotations world stack key body)
    (unique : (ownedTickets stack).Nodup)
    (checked : RecursiveRequirements.Checked (resumes ++ disposals) receiving (available (ownedTickets stack))
      requirements row) : demand.Perm (ownedTickets stack) :=
  mode_record_ownership_balance records closing unique checked
    (fun _ _ located retired => mode_segment_retirement_spines source unique checked located retired)
    (mode_segment_spine_consumed source checked)

/-- The whole current-source certificate and exact mixed-mode records account
for all physical continuation owners. No owner-balance premise is supplied. -/
theorem mode_source_ownership_balance
    (current : Expression operations policy contracts world allowed runtimeScope Environment.empty
      code input currentDemand currentRequirements dependencies)
    (pending : ModeSource operations policy contracts tables families actions world
      stack (.value input) output pendingDemand pendingRequirements scope)
    (records : ∀ key body, (key, body) ∈ (resumes : Store) →
      ResumeAnnotated operations policy contracts tables families actions annotations world stack key body)
    (closing : ∀ key body, (key, body) ∈ (disposals : Store) →
      UnwindAnnotated operations policy contracts tables families annotations world stack key body)
    (unique : (ownedTickets stack).Nodup)
    (checked : RecursiveRequirements.Checked (resumes ++ disposals) receiving (available (ownedTickets stack))
      (.sequence (currentRequirements.prepend (OwnerPhases.ofStack tables stack)) pendingRequirements) row) :
    (currentDemand ++ pendingDemand).Perm (ownedTickets stack) := by
  refine mode_record_ownership_balance records closing unique checked ?_ ?_
  · intro owner capture located retired
    have noRetirements := RecursiveDisposalCapture.expression_no_retirements
      (DeclaredSources.expression_erase (expression_erase current))
    simp only [directRetirements, retirements_prepend, noRetirements, List.nil_append] at retired
    obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
    simpa only [PhaseRechecking.spendAll_append] using
      mode_segment_retirement_spines pending unique pendingCheck located retired
  · obtain ⟨currentRow, pendingRow, currentCheck, pendingCheck, same⟩ := RecursiveRequirements.checked_sequence_parts checked
    simpa only [PhaseRechecking.spendAll_append] using mode_segment_spine_consumed pending pendingCheck
end Ash.OneShot.SourceDependencySchemes.Lexical
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.mode_source_ownership_balance
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.mode_record_ownership_balance
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.mode_stack_ownership_balance

namespace Ash.OneShot.SourceDependencySchemes.Lexical
open ScopedExpressions ScopedExecution
open SourceDependencyAnnotations SourceDependencyFrames
open SourceDependencyCapture (OwnerCut)
open SourceDependencySchemes.Closing (Bound)
open RecursiveRequirements (Requirements Store)

/-- Select the live source fragments from the predecessor, then replace its
saved witness by the EXACT body authenticated by resume-record lookup. The
captured input, answer mode and recorded lexical scope remain the same. -/
theorem extract_recorded_resume {contract : SourceDependencyAnnotations.Contract}
    {recordedRequirements : Requirements contract.resumeDemand}
    (source : ModeSource operations policy contracts tables families actions world
      (front.append (.live owner inputType answerType captured caller tail))
      (.value contract.answer) output demand requirements scope)
    (known : contracts owner = some contract)
    (checked : RecursiveRequirements.Checked entries receiving before
      (.sequence (.invoke ⟨owner, .resume⟩ contract.resumeDemand nearer) requirements) row)
    (records : ∀ key body, (key, body) ∈ (resumes : Store) →
      ResumeAnnotated operations policy contracts tables families actions annotations world
        (front.append (.live owner inputType answerType captured caller tail)) key body)
    (found : RecursiveRequirements.lookup ⟨owner, .resume⟩ resumes = some ⟨contract.resumeDemand, recordedRequirements⟩)
    (bound : Bound annotations scope)
    (unique : (ownedTickets (front.append (.live owner inputType answerType captured caller tail))).Nodup) :
    ∃ (boundary : ModeValue) (frontDemand tailDemand : List Nat),
    ∃ frontRequirements : Requirements frontDemand,
    ∃ tailRequirements : Requirements tailDemand,
    ∃ frontScope capturedScope tailScope,
      ModeSource operations policy contracts tables families actions world front
        (.value contract.answer) (.value contract.answer) frontDemand frontRequirements frontScope ∧
      ModeSource operations policy contracts tables families actions world captured
        (.value contract.input) boundary contract.resumeDemand recordedRequirements capturedScope ∧
      ModeSource operations policy contracts tables families actions world tail
        boundary output tailDemand tailRequirements tailScope ∧
      (boundary = .value contract.answer ∨ boundary = .unwind) ∧
      contract.input.erase.port = ScopedPorts.eraseType inputType ∧
      contract.answer.erase.port = ScopedPorts.eraseType answerType ∧
      ScopedPorts.EffectScopeKnown contracts.erase.ports caller ∧
      contract.held = ProtectionContexts.protectedMode captured.erase ∧
      scope = frontScope.append (.live owner capturedScope tailScope) ∧
      demand = frontDemand ++ tailDemand ∧
      Bound annotations (capturedScope.append (frontScope.append (.spent owner tailScope))) ∧
      ∀ store receiving phases,
        RecursiveRequirements.evaluate store receiving phases requirements =
          ProtectionResiduals.merge
            (RecursiveRequirements.evaluate store
              (OwnerPhases.ofStack tables (.live owner inputType answerType captured caller tail) ++ receiving)
              phases frontRequirements)
            (RecursiveRequirements.evaluate store receiving (OwnerPhaseTransitions.spendAll phases frontDemand)
              (.sequence (.spent owner) tailRequirements)) := by
  obtain ⟨boundary, frontDemand, tailDemand, frontRequirements, capturedRequirements,
    tailRequirements, frontScope, capturedScope, tailScope, frontSource, savedSource, tailSource,
    returns, inputAnnotation, answerAnnotation, callerScope, held, scopeSame, demandSame, evaluation⟩ :=
    source.extract_live known checked
  have prefixUnique : (ownedTickets front ++ owner :: (ownedTickets captured ++ ownedTickets tail)).Nodup := by
    simpa only [owned_tickets_append, ownedTickets] using unique
  have absent : owner ∉ ownedTickets front := fun member =>
    (List.nodup_append.mp prefixUnique).2.2 owner member owner List.mem_cons_self rfl
  have cut : OwnerCut owner scope ⟨frontScope, capturedScope, tailScope⟩ := by
    rw [scopeSame]
    exact SourceDependencySchemes.Closing.prefix_owner_cut frontSource.realizes absent
  have stored := selected_resume_source records found bound cut
    (RecursiveRecords.located_below front .here) unique known savedSource.return_mode returns
  exact ⟨boundary, frontDemand, tailDemand, frontRequirements, tailRequirements,
    frontScope, capturedScope, tailScope, frontSource, stored, tailSource, returns,
    inputAnnotation, answerAnnotation, callerScope, held, scopeSame, demandSame,
    (by simpa only [SourceDependencyCapture.OwnerSelection.resumed] using (bound.invocations cut).1), evaluation⟩
end Ash.OneShot.SourceDependencySchemes.Lexical
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.extract_recorded_resume

namespace Ash.OneShot.SourceDependencySchemes.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations SourceDependencyFrames
open SourceDependencySchemes.Closing (Bound)
open RecursiveRequirements (Requirements Store evaluate)
open OwnerPhaseTransitions (Phases spend spendAll)

variable {front captured tail : Stack} {before : Phases}

/-- Reuse the same row/store transport for an explicitly retained source
split. The equation is supplied by structural source decomposition. -/
theorem resume_fragment_rows {front captured tail : Stack} {contract : SourceDependencyAnnotations.Contract}
    {recordedRequirements : Requirements contract.resumeDemand}
    (storeAnnotation : StoreAnnotation (resumes ++ disposals) annotatedStore)
    (found : RecursiveRequirements.lookup ⟨owner, .resume⟩ resumes = some ⟨contract.resumeDemand, recordedRequirements⟩)
    (invocation : RecursiveRequirements.Checked annotatedStore
      (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType captured caller tail)))
      before (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) resumeRow)
    (pending : RecursiveRequirements.Checked annotatedStore [] (spendAll before (owner :: contract.resumeDemand))
      pendingRequirements pendingRow)
    {frontDemand tailDemand : List Nat}
    {frontRequirements : Requirements frontDemand} {tailRequirements : Requirements tailDemand}
    (evaluation : ∀ store receiving phases,
      evaluate store receiving phases pendingRequirements =
        merge (evaluate store (OwnerPhases.ofStack tables (.live owner inputType answerType captured caller tail) ++ receiving)
          phases frontRequirements)
          (evaluate store receiving (spendAll phases frontDemand) (.sequence (.spent owner) tailRequirements))) :
    ∃ frontRow tailRow savedRow, ∃ savedAnnotated : Requirements contract.resumeDemand,
      RowAnnotation recordedRequirements savedAnnotated ∧ savedRow ⊆ resumeRow ∧
      pendingRow = frontRow ++ tailRow ∧
      RecursiveRequirements.Checked (RecursiveTransport.removeOwner owner annotatedStore)
        (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail)))
        (spend before owner) recordedRequirements savedRow ∧
      RecursiveRequirements.Checked (RecursiveTransport.removeOwner owner annotatedStore)
        (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail)))
        (spend before owner) savedAnnotated resumeRow ∧
      RecursiveRequirements.Checked (RecursiveTransport.removeOwner owner annotatedStore)
        (OwnerPhases.ofStack tables (.spent owner answerType caller tail))
        (spendAll (spend before owner) contract.resumeDemand) frontRequirements frontRow ∧
      RecursiveRequirements.Checked (RecursiveTransport.removeOwner owner annotatedStore) []
        (spendAll (spendAll (spend before owner) contract.resumeDemand) frontDemand)
        tailRequirements tailRow := by
  obtain ⟨body, selectedContext, actual, ready, selection, bodyChecked⟩ :=
    RecursiveRequirements.checked_invocation invocation
  obtain ⟨savedAnnotated, actualFound, savedAnnotation⟩ := storeAnnotation.lookup_annotated
    (RecursiveRecords.lookup_append (second := disposals) found)
  have sameTemplate := Option.some.inj (actual.symm.trans actualFound)
  have sameBody := eq_of_heq (Sigma.mk.inj sameTemplate).2
  subst body
  have consumed : spend before owner owner = .consumed := OwnerPhaseTransitions.spend_self before owner
  have contexts : RecursiveTransport.normalize (spend before owner)
      (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType captured caller tail))) =
      RecursiveTransport.normalize (spend before owner)
        (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail))) := by
    simpa only [List.append_nil] using (RecursiveRecomposition.normalize_replaced
      (front := front) (capture := captured) (tail := tail) (input := inputType) (answer := answerType)
      (caller := caller) (tables := tables) (receiving := []) consumed)
  have savedAnnotatedCheck := RecursiveTransport.checked_transport bodyChecked
    (RecursiveTransport.remove_consumed_agrees consumed) (by simpa only [List.nil_append] using contexts)
  obtain ⟨savedRow, savedChecked, savedBound⟩ := savedAnnotation.checked savedAnnotatedCheck
  have evaluated := RecursiveRequirements.checked_complete pending
  rw [evaluation] at evaluated
  obtain ⟨frontRow, waitingRow, frontEvaluation, waitingEvaluation, rowSame⟩ := PhaseRechecking.merge_split evaluated
  obtain ⟨spentRow, tailRow, spentCheck, tailCheck, waitingSame⟩ :=
    RecursiveRequirements.checked_sequence_parts (RecursiveRequirements.evaluate_sound waitingEvaluation)
  have spentEmpty : spentRow = [] := by
    have checked := RecursiveRequirements.checked_complete spentCheck
    rw [RecursiveRecomposition.evaluate_spent] at checked
    split at checked
    · exact (Option.some.inj checked).symm
    · cases checked
  subst spentRow
  simp only [List.nil_append] at waitingSame
  subst waitingRow
  have consumedAfter : spendAll (spend before owner) contract.resumeDemand owner = .consumed :=
    RecursiveTransport.phases_spendAll_later owner consumed
  have frontContexts : RecursiveTransport.normalize (spendAll (spend before owner) contract.resumeDemand)
      (OwnerPhases.ofStack tables (.live owner inputType answerType captured caller tail) ++ []) =
      RecursiveTransport.normalize (spendAll (spend before owner) contract.resumeDemand)
        (OwnerPhases.ofStack tables (.spent owner answerType caller tail)) := by
    simpa only [Stack.append, List.append_nil] using (RecursiveRecomposition.normalize_replaced
      (front := .nil) (capture := captured) (tail := tail) (input := inputType) (answer := answerType)
      (caller := caller) (tables := tables) (receiving := []) consumedAfter)
  have frontChecked := RecursiveTransport.checked_transport (RecursiveRequirements.evaluate_sound frontEvaluation)
    (RecursiveTransport.remove_consumed_agrees consumedAfter) frontContexts
  have tailActual : RecursiveRequirements.Checked annotatedStore []
      (spendAll (spendAll (spend before owner) contract.resumeDemand) frontDemand) tailRequirements tailRow := by
    simpa only [spendAll] using tailCheck
  have tailChecked := RecursiveTransport.checked_remove_consumed tailActual
    (RecursiveTransport.phases_spendAll_later owner consumedAfter)
  refine ⟨frontRow, tailRow, savedRow, savedAnnotated,
    savedAnnotation, savedBound, rowSame, savedChecked, savedAnnotatedCheck, frontChecked, ?_⟩
  simpa only [spendAll] using tailChecked

/-- The predecessor invocation and pending-code checks supply the saved,
caller and tail checks after removing the selected owner's records. Source
extraction authenticates the exact normal body. Structural store annotation
also exposes its checked annotated body at the same real spent-owner suffix;
projection derives the normal body's bounded row. No reentered source is a
premise. -/
theorem resume_checked_fragments {contract : SourceDependencyAnnotations.Contract}
    {recordedRequirements : Requirements contract.resumeDemand}
    (source : ModeSource operations policy contracts tables families actions world
      (front.append (.live owner inputType answerType captured caller tail))
      (.value contract.answer) output pendingDemand pendingRequirements scope)
    (known : contracts owner = some contract)
    (storeAnnotation : StoreAnnotation (resumes ++ disposals) annotatedStore)
    (records : ∀ key body, (key, body) ∈ (resumes : Store) →
      ResumeAnnotated operations policy contracts tables families actions annotations world
        (front.append (.live owner inputType answerType captured caller tail)) key body)
    (found : RecursiveRequirements.lookup ⟨owner, .resume⟩ resumes = some ⟨contract.resumeDemand, recordedRequirements⟩)
    (bound : Bound annotations scope)
    (unique : (ownedTickets (front.append (.live owner inputType answerType captured caller tail))).Nodup)
    (invocation : RecursiveRequirements.Checked annotatedStore
      (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType captured caller tail)))
      before (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) resumeRow)
    (pending : RecursiveRequirements.Checked annotatedStore [] (spendAll before (owner :: contract.resumeDemand))
      pendingRequirements pendingRow) :
    ∃ (boundary : ModeValue) (frontDemand tailDemand : List Nat),
    ∃ frontRequirements : Requirements frontDemand, ∃ tailRequirements : Requirements tailDemand,
    ∃ frontScope capturedScope tailScope frontRow tailRow savedRow,
    ∃ savedAnnotated : Requirements contract.resumeDemand,
      RowAnnotation recordedRequirements savedAnnotated ∧ savedRow ⊆ resumeRow ∧
      ModeSource operations policy contracts tables families actions world front
        (.value contract.answer) (.value contract.answer) frontDemand frontRequirements frontScope ∧
      ModeSource operations policy contracts tables families actions world captured
        (.value contract.input) boundary contract.resumeDemand recordedRequirements capturedScope ∧
      ModeSource operations policy contracts tables families actions world tail
        boundary output tailDemand tailRequirements tailScope ∧
      (boundary = .value contract.answer ∨ boundary = .unwind) ∧
      contract.input.erase.port = ScopedPorts.eraseType inputType ∧
      contract.answer.erase.port = ScopedPorts.eraseType answerType ∧
      ScopedPorts.EffectScopeKnown contracts.erase.ports caller ∧
      contract.held = ProtectionContexts.protectedMode captured.erase ∧
      scope = frontScope.append (.live owner capturedScope tailScope) ∧
      pendingDemand = frontDemand ++ tailDemand ∧ pendingRow = frontRow ++ tailRow ∧
      Bound annotations (capturedScope.append (frontScope.append (.spent owner tailScope))) ∧
      RecursiveRequirements.Checked (RecursiveTransport.removeOwner owner annotatedStore)
        (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail)))
        (spend before owner) recordedRequirements savedRow ∧
      RecursiveRequirements.Checked (RecursiveTransport.removeOwner owner annotatedStore)
        (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail)))
        (spend before owner) savedAnnotated resumeRow ∧
      RecursiveRequirements.Checked (RecursiveTransport.removeOwner owner annotatedStore)
        (OwnerPhases.ofStack tables (.spent owner answerType caller tail))
        (spendAll (spend before owner) contract.resumeDemand) frontRequirements frontRow ∧
      RecursiveRequirements.Checked (RecursiveTransport.removeOwner owner annotatedStore) []
        (spendAll (spendAll (spend before owner) contract.resumeDemand) frontDemand)
        tailRequirements tailRow := by
  have invoked : RecursiveRequirements.Checked annotatedStore [] before
      (.invoke ⟨owner, .resume⟩ contract.resumeDemand
        (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType captured caller tail)))) resumeRow := by
    change RecursiveRequirements.Checked annotatedStore [] before
      ((Requirements.invoke ⟨owner, .resume⟩ contract.resumeDemand []).prepend
        (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType captured caller tail)))) resumeRow
    apply RecursiveRequirements.checked_prepend_iff.mpr
    simpa only [List.append_nil] using invocation
  obtain ⟨boundary, frontDemand, tailDemand, frontRequirements, tailRequirements,
    frontScope, capturedScope, tailScope, frontSource, savedSource, tailSource, returns,
    inputAnnotation, answerAnnotation, callerScope, held, scopeSame, demandSame, nextBound, evaluation⟩ :=
    extract_recorded_resume source known (RecursiveRequirements.Checked.sequence invoked pending) records found bound unique
  obtain ⟨frontRow, tailRow, savedRow, savedAnnotated,
    savedAnnotation, savedBound, rowSame, savedChecked, savedAnnotatedCheck, frontChecked, tailChecked⟩ :=
    resume_fragment_rows storeAnnotation found invocation pending evaluation
  exact ⟨boundary, frontDemand, tailDemand, frontRequirements, tailRequirements,
    frontScope, capturedScope, tailScope, frontRow, tailRow, savedRow, savedAnnotated,
    savedAnnotation, savedBound, frontSource, savedSource, tailSource,
    returns, inputAnnotation, answerAnnotation, callerScope, held, scopeSame, demandSame, rowSame,
    nextBound, savedChecked, savedAnnotatedCheck, frontChecked, tailChecked⟩

end Ash.OneShot.SourceDependencySchemes.Lexical
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.resume_checked_fragments

namespace Ash.OneShot.SourceDependencySchemes.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations SourceDependencyFrames
open RecursiveRequirements (Requirements Store)
open OwnerPhaseTransitions (available spendAll)
open RecursiveDisposalCapture SourceDependencyOwners.Lexical

/-- Source-local dependency bounds are reused through every recursively
referenced body. The region may be a caller prefix or preserved saved suffix. -/
theorem mode_region_demand_bound
    (records : ∀ key body, (key, body) ∈ (resumes : Store) →
      ResumeAnnotated operations policy contracts tables families actions annotations world root key body)
    (closing : ∀ key body, (key, body) ∈ (disposals : Store) →
      UnwindAnnotated operations policy contracts tables families annotations world root key body)
    (unique : (ownedTickets root).Nodup)
    (captures : ∀ owner capture, SourceTemplates.CapturedIn owner capture region →
      SourceTemplates.CapturedIn owner capture root)
    (retained : ScopedRetirement.scheduled region ⊆ ScopedRetirement.scheduled root)
    (internal : region.erase.pending ⊆ ownedTickets region)
    (checked : RecursiveRequirements.Checked (resumes ++ disposals) receiving before
      (requirements : Requirements demand) row)
    (calls : directCalls requirements ⊆ ownedTickets region)
    (retirements : directRetirements requirements ⊆ ownedTickets region) :
    demand ⊆ ownedTickets region := by
  refine checked_demand_bound ?_ ?_ checked calls retirements
  · intro owner demand body found member
    rcases List.mem_append.mp (SourceTemplates.lookup_member found) with resumed | disposed
    · cases records _ _ resumed with
      | resume located known recorded source returns =>
          have inside := captured_in_preserved_region unique captures retained located member
          exact ⟨fun _ present => internal (captured_pending_subset inside (mode_segment_call_pending source present)),
            (mode_segment_retirements_owned source).trans (captured_owned_subset inside)⟩
    · cases closing _ _ disposed
  · intro owner demand body found member
    rcases List.mem_append.mp (SourceTemplates.lookup_member found) with resumed | disposed
    · cases records _ _ resumed
    · cases closing _ _ disposed with
      | dispose located unprotected recorded source =>
          have inside := captured_in_preserved_region unique captures retained located member
          exact fun _ present => captured_owned_subset inside (source.template.ownership.mem_iff.mp present)

/-- The existing reentry dependency bounds isolate the caller's demanded
owners. Reuse balanced_middle_demands; no source/use demand permutation or
caller ownership equation is a premise. -/
theorem mode_reentry_unwind_balance
    (frontSource : ModeSource operations policy contracts tables families actions world
      front frontInput frontOutput frontDemand frontRequirements frontScope)
    (savedSource : ModeSource operations policy contracts tables families actions world
      captured savedInput savedOutput captureDemand captureRequirements capturedScope)
    (tailSource : ModeSource operations policy contracts tables families actions world
      tail tailInput tailOutput tailDemand tailRequirements tailScope)
    (records : ∀ key body, (key, body) ∈ (resumes : Store) →
      ResumeAnnotated operations policy contracts tables families actions annotations world
        (captured.append (front.append (.spent owner answer caller tail))) key body)
    (closing : ∀ key body, (key, body) ∈ (disposals : Store) →
      UnwindAnnotated operations policy contracts tables families annotations world
        (captured.append (front.append (.spent owner answer caller tail))) key body)
    (unique : (ownedTickets (captured.append (front.append (.spent owner answer caller tail)))).Nodup)
    (savedChecked : RecursiveRequirements.Checked (resumes ++ disposals) savedReceiving savedBefore captureRequirements savedRow)
    (frontChecked : RecursiveRequirements.Checked (resumes ++ disposals) frontReceiving frontBefore frontRequirements frontRow)
    (tailChecked : RecursiveRequirements.Checked (resumes ++ disposals) tailReceiving tailBefore tailRequirements tailRow)
    (bounds : LexicalUnwind.ReentryBounds front captured tail .unwind)
    (balance : (captureDemand ++ frontDemand ++ tailDemand).Perm
      (ownedTickets (captured.append (front.append (.spent owner answer caller tail))))) :
    frontDemand.Perm (ownedTickets front) := by
  cases bounds with
  | unwind scopes inside saved outside =>
    have frontInternal : front.erase.pending ⊆ ownedTickets front :=
      (internalUses_subset inside).trans (recursive_live_tickets_owned front)
    have tailInternal : tail.erase.pending ⊆ ownedTickets tail := internalUses_subset outside
    have savedInternal : (captured.append tail).erase.pending ⊆ ownedTickets (captured.append tail) := by
      rw [erase_append, (CaptureOwnerChecks.append_projections _ _).1, owned_tickets_append]
      exact List.append_subset.mpr ⟨internalUses_subset saved, tailInternal.trans (List.subset_append_right _ _)⟩
    have frontCaptures : ∀ key body, SourceTemplates.CapturedIn key body front →
        SourceTemplates.CapturedIn key body (captured.append (front.append (.spent owner answer caller tail))) := by
      intro key body located
      exact SavedCaptureIdentity.located_append.mpr (.inr (SavedCaptureIdentity.located_append.mpr (.inl located)))
    have tailCaptures : ∀ key body, SourceTemplates.CapturedIn key body tail →
        SourceTemplates.CapturedIn key body (captured.append (front.append (.spent owner answer caller tail))) := by
      intro key body located
      exact SavedCaptureIdentity.located_append.mpr (.inr (SavedCaptureIdentity.located_append.mpr (.inr (.spent located))))
    have savedCaptures : ∀ key body, SourceTemplates.CapturedIn key body (captured.append tail) →
        SourceTemplates.CapturedIn key body (captured.append (front.append (.spent owner answer caller tail))) := by
      intro key body located
      rcases SavedCaptureIdentity.located_append.mp located with first | last
      · exact SavedCaptureIdentity.located_append.mpr (.inl first)
      · exact tailCaptures _ _ last
    have frontRetained : ScopedRetirement.scheduled front ⊆
        ScopedRetirement.scheduled (captured.append (front.append (.spent owner answer caller tail))) := by
      simp only [ScopedRetirement.scheduled_append, ScopedRetirement.scheduled]
      exact (List.subset_append_left _ _).trans (List.subset_append_right _ _)
    have tailRetained : ScopedRetirement.scheduled tail ⊆
        ScopedRetirement.scheduled (captured.append (front.append (.spent owner answer caller tail))) := by
      simp only [ScopedRetirement.scheduled_append, ScopedRetirement.scheduled]
      exact (List.subset_append_right _ _).trans (List.subset_append_right _ _)
    have savedRetained : ScopedRetirement.scheduled (captured.append tail) ⊆
        ScopedRetirement.scheduled (captured.append (front.append (.spent owner answer caller tail))) := by
      rw [ScopedRetirement.scheduled_append]
      exact List.append_subset.mpr ⟨by
        rw [ScopedRetirement.scheduled_append]
        exact List.subset_append_left _ _, tailRetained⟩
    have frontBound := mode_region_demand_bound records closing unique frontCaptures frontRetained frontInternal frontChecked
      (fun _ member => frontInternal (mode_segment_call_pending frontSource member))
      (mode_segment_retirements_owned frontSource)
    have tailBound := mode_region_demand_bound records closing unique tailCaptures tailRetained tailInternal tailChecked
      (fun _ member => tailInternal (mode_segment_call_pending tailSource member))
      (mode_segment_retirements_owned tailSource)
    have savedBound := mode_region_demand_bound records closing unique savedCaptures savedRetained savedInternal savedChecked
      (by
        rw [owned_tickets_append]
        exact fun _ member => internalUses_subset saved (mode_segment_call_pending savedSource member))
      (by
        rw [owned_tickets_append]
        exact (mode_segment_retirements_owned savedSource).trans (List.subset_append_left _ _))
    apply Syntax.balanced_middle_demands
      (by simpa only [owned_tickets_append, ownedTickets, List.append_assoc] using balance)
      (by simpa only [owned_tickets_append, ownedTickets, List.append_assoc] using unique)
      (by simpa only [owned_tickets_append] using savedBound) frontBound tailBound
end Ash.OneShot.SourceDependencySchemes.Lexical

#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.mode_region_demand_bound
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.mode_reentry_unwind_balance


namespace Ash.OneShot.SourceDependencySchemes.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations SourceDependencyFrames
open SourceDependencySchemes.Closing (Bound)
open RecursiveRequirements (Requirements Store)
open OwnerPhaseTransitions (available spend spendAll Trace)
variable {front captured tail : Stack}

/-- Source inversion and value silence recover the actual invocation check
from the ready resume expression, without assuming its operand annotation. -/
private theorem resume_expression_check
    (current : Expression operations policy contracts world allowed runtimeScope Environment.empty
      (.resume binder value) result currentDemand currentRequirements dependencies)
    (known : contracts owner = some contract)
    (resolved : runtimeScope.resolve binder = some owner)
    (isValue : value.IsValue)
    (checked : RecursiveRequirements.Checked entries receiving before currentRequirements row) :
    currentDemand = owner :: contract.resumeDemand ∧
    RecursiveRequirements.Checked entries receiving before (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) row ∧
    ValueSummary operations policy contracts world Environment.empty [] value contract.input := by
  cases current with
  | resume actualKnown actualResolved permission operand admitted formed =>
      cases Option.some.inj (actualResolved.symm.trans resolved)
      cases Option.some.inj (actualKnown.symm.trans known)
      have empty := SourceTemplates.expression_value_demand
        (DeclaredSources.expression_erase (expression_erase operand)) isValue
      have evaluated := RecursiveRequirements.checked_complete checked
      rw [RecursiveRequirements.evaluate_sequence,
        RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase (expression_erase operand)) isValue] at evaluated
      simp only [empty, spendAll, RecursiveRecomposition.merge_empty_left] at evaluated
      exact ⟨by simp only [empty, List.nil_append], RecursiveRequirements.evaluate_sound evaluated,
        Values.change_allowed (Values.summary operand isValue) isValue []⟩

/-- The typed ready resume expression and its enclosing predecessor
certificate supply the invocation and pending requirement checks. The local
recursive return-mode judgment checks the whole current expression and supplies
recursive retained dependency checks for the same successor.
Existing structural use, access and resource-support proofs establish that
actual resume transition.
The checked fragments and reentry bounds derive caller cleanup and its owner
balance. Unwind return requires only a path to that cleanup branch in the same
certificate; ordinary return requires none. The successor certificate retains
the saved record's annotation, the pending annotation, and the selected cleanup
choice after the saved demand. Exact normal records justify source and owner
facts; their structurally related checking store retains annotated bodies.
Recomposition stays within the original certificate's effect bound. -/
theorem resume_mode_segments {contract : SourceDependencyAnnotations.Contract}
    {recordedRequirements : Requirements contract.resumeDemand}
    (current : Expression operations policy contracts world allowed runtimeScope Environment.empty
      (.resume binder value) contract.answer currentDemand currentRequirements dependencies)
    (resolved : runtimeScope.resolve binder = some owner)
    (isValue : value.IsValue)
    (usage : LexicalUnwind.MachineUse policy actions (.eval
      ⟨.resume binder value, runtimeScope, front.append (.live owner inputType answerType captured caller tail)⟩))
    (ticketAccess : LexicalUnwind.MachineTicketAccess policy actions (.eval
      ⟨.resume binder value, runtimeScope, front.append (.live owner inputType answerType captured caller tail)⟩))
    (resourceAccess : LexicalUnwind.MachineAccess ambient (.eval
      ⟨.resume binder value, runtimeScope, front.append (.live owner inputType answerType captured caller tail)⟩))
    (reentry : SourceDependencyOwners.ReentrySource operations policy contracts world front captured tail
      (LexicalUnwind.returnMode captured .ordinary))
    (source : ModeSource operations policy contracts tables families actions world
      (front.append (.live owner inputType answerType captured caller tail))
      (.value contract.answer) output pendingDemand pendingRequirements scope)
    {returnHints : SourceDependencyChecks.Lexical.ReturnHints scope}
    (currentLocal : SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local outward actions
      (available (ownedTickets (front.append (.live owner inputType answerType captured caller tail))))
      world dependencies returnHints)
    (hinted : SourceDependencyChecks.Lexical.ReturnHints.Matches tables families returnHints
      (front.append (.live owner inputType answerType captured caller tail)))
    (known : contracts owner = some contract)
    (records : ∀ key body, (key, body) ∈ (resumes : Store) →
      ResumeAnnotated operations policy contracts tables families actions annotations world
        (front.append (.live owner inputType answerType captured caller tail)) key body)
    (closing : ∀ key body, (key, body) ∈ (disposals : Store) →
      UnwindAnnotated operations policy contracts tables families annotations world
        (front.append (.live owner inputType answerType captured caller tail)) key body)
    (found : RecursiveRequirements.lookup ⟨owner, .resume⟩ resumes = some ⟨contract.resumeDemand, recordedRequirements⟩)
    (bound : Bound annotations scope)
    (unique : (ownedTickets (front.append (.live owner inputType answerType captured caller tail))).Nodup)
    (annotation : RowAnnotation
      (.sequence (currentRequirements.prepend
        (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType captured caller tail)))) pendingRequirements)
      annotatedRoot)
    (storeAnnotation : StoreAnnotation (resumes ++ disposals) annotatedStore)
    (certificate : RecursiveRequirements.Checked annotatedStore []
      (available (ownedTickets (front.append (.live owner inputType answerType captured caller tail))))
      annotatedRoot certificateRow) :
    let nextStack := captured.append (front.append (.spent owner answerType caller tail))
    let after := available (ownedTickets nextStack)
    LexicalUnwind.UseTransition (.eval
      ⟨.resume binder value, runtimeScope, front.append (.live owner inputType answerType captured caller tail)⟩)
      (.eval ⟨value, runtimeScope, nextStack⟩) [] [.ticket owner] ∧
    LexicalUnwind.MachineUse policy actions (.eval ⟨value, runtimeScope, nextStack⟩) ∧
    LexicalUnwind.MachineTicketAccess policy actions (.eval ⟨value, runtimeScope, nextStack⟩) ∧
    LexicalUnwind.MachineAccess ambient (.eval ⟨value, runtimeScope, nextStack⟩) ∧
    StoreAnnotation (RecursiveTransport.removeOwner owner (resumes ++ disposals))
      (RecursiveTransport.removeOwner owner annotatedStore) ∧
    ∃ (boundary : ModeValue) (frontDemand : List Nat), ∃ frontRequirements : Requirements frontDemand,
    ∃ (frontScope nextScope : DependencyScope) (frontRow tailRow : Footprint),
    ∃ closeDemand, ∃ closeRequirements : Requirements closeDemand, ∃ aligned : frontDemand.Perm closeDemand,
      ValueSummary operations policy contracts world Environment.empty [] value contract.input ∧
      ModeSource operations policy contracts tables families actions world front
        (.value contract.answer) (.value contract.answer) frontDemand frontRequirements frontScope ∧
      (boundary = .value contract.answer ∨ boundary = .unwind) ∧
      (boundary.mode = .unwind →
        UnwindSource operations policy contracts tables families world front closeDemand closeRequirements frontScope) ∧
      frontRow ++ tailRow ⊆ certificateRow ∧ Bound annotations nextScope ∧
      (∃ nextHints : SourceDependencyChecks.Lexical.ReturnHints nextScope,
        SourceDependencyChecks.Lexical.ReturnHints.Matches tables families nextHints nextStack ∧
        SourceDependencyChecks.Lexical.ReturnHints.Recursive.Pending outward actions after world
          nextHints .nil .ordinary output.mode) ∧
      ((boundary.mode = .unwind →
          RequirementPath
              (.choice
                (frontRequirements.prepend (OwnerPhases.ofStack tables (.live owner inputType answerType captured caller tail)))
                (closeRequirements.prepend (OwnerPhases.ofStack tables (.live owner inputType answerType captured caller tail))) aligned)
              annotatedRoot (owner :: contract.resumeDemand)) →
        ∃ demand, ∃ requirements annotatedNext : Requirements demand, ∃ row annotatedRow,
          ModeSource operations policy contracts tables families actions world nextStack
            (.value contract.input) output demand requirements nextScope ∧
          RecursiveRequirements.Checked (RecursiveTransport.removeOwner owner annotatedStore) []
            after requirements row ∧ row ⊆ certificateRow ∧
          RowAnnotation requirements annotatedNext ∧
          RecursiveRequirements.Checked (RecursiveTransport.removeOwner owner annotatedStore) []
            after annotatedNext annotatedRow ∧ annotatedRow ⊆ certificateRow ∧
          (∃ retained : Requirements pendingDemand,
            RowAnnotation pendingRequirements retained ∧
            RequirementPath retained annotatedRoot currentDemand ∧
            RequirementPath retained annotatedNext contract.resumeDemand) ∧
          (boundary.mode = .unwind →
            RequirementPath
              (.choice
                (frontRequirements.prepend (OwnerPhases.ofStack tables (.live owner inputType answerType captured caller tail)))
                (closeRequirements.prepend (OwnerPhases.ofStack tables (.live owner inputType answerType captured caller tail))) aligned)
              annotatedNext contract.resumeDemand) ∧
          (∃ savedAnnotated : Requirements contract.resumeDemand,
            RowAnnotation recordedRequirements savedAnnotated ∧
            RequirementPath
              (savedAnnotated.prepend (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail))))
              annotatedNext []) ∧
          demand.Perm (ownedTickets nextStack)) ∧
      Trace (available (ownedTickets (front.append (.live owner inputType answerType captured caller tail)))) [owner] after ∧
      (ownedTickets nextStack).Nodup ∧
      (∀ key body, (key, body) ∈ RecursiveTransport.removeOwner owner resumes →
        ResumeAnnotated operations policy contracts tables families actions annotations world nextStack key body) ∧
      (∀ key body, (key, body) ∈ RecursiveTransport.removeOwner owner disposals →
        UnwindAnnotated operations policy contracts tables families annotations world nextStack key body) := by
  dsimp only
  obtain ⟨rootRow, rootCheck, rootBound⟩ := annotation.checked certificate
  obtain ⟨_, normalStoreCheck, _⟩ := storeAnnotation.checked rootCheck
  have ownerBalance := mode_source_ownership_balance current source records closing unique normalStoreCheck
  obtain ⟨resumeRow, normalPendingRow, currentCheck, normalPending, rootSame⟩ :=
    RecursiveRequirements.checked_sequence_parts rootCheck
  obtain ⟨currentDemandSame, invocation, payload⟩ := resume_expression_check current known resolved isValue
    (RecursiveRequirements.checked_prepend_iff.mp currentCheck)
  have balanced : (owner :: (contract.resumeDemand ++ pendingDemand)).Perm
      (ownedTickets (front.append (.live owner inputType answerType captured caller tail))) := by
    simpa only [currentDemandSame, List.cons_append] using ownerBalance
  have closed := ScopedPorts.typed_value_closed
    ((DeclaredSourceValues.erase (value_erase payload)).ports .none) isValue
  have step := LexicalUnwind.UseTransition.resume binder owner runtimeScope caller inputType answerType
    front captured tail value closed resolved reentry.bounds
  have nextUsage := SourceDependencyOwners.source_resume_use usage resolved isValue unique reentry
  have nextTickets := step.ticket_access (policy := policy) (tickets := actions)
    (by intro other impossible; cases impossible) unique usage ticketAccess
  have nextResources : LexicalUnwind.MachineAccess ambient (.eval
      ⟨value, runtimeScope, captured.append (front.append (.spent owner answerType caller tail))⟩) := by
    cases resourceAccess with
    | eval supported =>
        exact .eval (raw_step_preserves_access
          (.resume binder owner runtimeScope caller inputType answerType front captured tail value closed resolved)
          supported ScopedPorts.resume_access_checks)
  refine ⟨step, nextUsage, nextTickets, nextResources, storeAnnotation.remove_owner owner, ?_⟩
  have invocationActual : RecursiveRequirements.Checked annotatedStore
      (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType captured caller tail)))
      (available (ownedTickets (front.append (.live owner inputType answerType captured caller tail))))
      (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) resumeRow := by
    simpa only [List.append_nil] using invocation
  rw [currentDemandSame] at normalPending
  have resumeBound : resumeRow ⊆ certificateRow :=
    (List.subset_append_left _ _).trans (rootSame ▸ rootBound)
  have normalBound : normalPendingRow ⊆ certificateRow :=
    (List.subset_append_right _ _).trans (rootSame ▸ rootBound)
  obtain ⟨boundary, frontDemand, tailDemand, frontRequirements, tailRequirements,
    frontScope, capturedScope, tailScope, frontRow, tailRow, savedRow, savedAnnotated,
    savedAnnotation, savedRowBound, frontSource, savedSource, tailSource,
    returns, inputAnnotation, answerAnnotation, callerScope, held, scopeSame, demandSame, rowSame,
    nextBound, savedChecked, savedAnnotatedCheck, frontChecked, tailChecked⟩ :=
    resume_checked_fragments source known storeAnnotation records found bound unique invocationActual normalPending
  have trace := OwnerPhaseTransitions.resume_phase_trace unique
  have phaseSame := OwnerPhaseTransitions.trace_result trace
  change available (ownedTickets (captured.append (front.append (.spent owner answerType caller tail)))) =
    spend (available (ownedTickets (front.append (.live owner inputType answerType captured caller tail)))) owner at phaseSame
  rw [← phaseSame] at savedChecked savedAnnotatedCheck frontChecked tailChecked
  have prefixUnique : (ownedTickets front ++ owner :: (ownedTickets captured ++ ownedTickets tail)).Nodup := by
    simpa only [owned_tickets_append, ownedTickets] using unique
  have absent : owner ∉ ownedTickets front := fun member =>
    (List.nodup_append.mp prefixUnique).2.2 owner member owner List.mem_cons_self rfl
  have localCut : SourceDependencyCapture.OwnerCut owner scope ⟨frontScope, capturedScope, tailScope⟩ := by
    rw [scopeSame]
    exact SourceDependencySchemes.Closing.prefix_owner_cut frontSource.realizes absent
  have invocationLocal := SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local.ready_resume current resolved currentLocal
  have localRetained := invocationLocal.resume_at_cut hinted localCut frontSource.realizes
  have returnModeSame : returnHints.returnMode .ordinary = output.mode :=
    (SourceDependencyChecks.Lexical.ReturnHints.Matches.return_mode hinted).trans source.return_mode
  rw [← phaseSame, returnModeSame] at localRetained
  have consumed : available (ownedTickets (captured.append (front.append (.spent owner answerType caller tail)))) owner = .consumed := by
    rw [phaseSame]
    exact OwnerPhaseTransitions.spend_self _ _
  have nextBalance : (contract.resumeDemand ++ pendingDemand).Perm
      (ownedTickets (captured.append (front.append (.spent owner answerType caller tail)))) :=
    (balanced.trans OwnerPhaseTransitions.resume_owned_permutation).cons_inv
  have nextUnique := (List.nodup_cons.mp (OwnerPhaseTransitions.resume_owned_permutation.nodup unique)).2
  have combinedBound : frontRow ++ tailRow ⊆ certificateRow := rowSame ▸ normalBound
  have frontBound : frontRow ⊆ certificateRow := (List.subset_append_left _ _).trans combinedBound
  have tailBound : tailRow ⊆ certificateRow := (List.subset_append_right _ _).trans combinedBound
  have returnMode := savedSource.return_mode
  have reentryBounds : LexicalUnwind.ReentryBounds front captured tail boundary.mode := by
    rw [← returnMode]
    exact reentry.bounds
  have survivingResumes := resume_annotated_records_resume records
  have survivingDisposals := annotated_records_resume closing (.refl _)
  have nextStoreAnnotation := storeAnnotation.remove_owner owner
  obtain ⟨_, normalSavedCheck, _⟩ := nextStoreAnnotation.checked savedChecked
  obtain ⟨_, normalFrontCheck, _⟩ := nextStoreAnnotation.checked frontChecked
  obtain ⟨_, normalTailCheck, _⟩ := nextStoreAnnotation.checked tailChecked
  obtain ⟨closeDemand, closeRequirements, aligned, cleanup⟩ :
      ∃ closeDemand, ∃ closeRequirements : Requirements closeDemand, ∃ aligned : frontDemand.Perm closeDemand,
        boundary.mode = .unwind →
          UnwindSource operations policy contracts tables families world front closeDemand closeRequirements frontScope := by
    cases boundary with
    | value answer => exact ⟨frontDemand, frontRequirements, .refl _, by intro impossible; cases impossible⟩
    | unwind =>
        have frontBalance := mode_reentry_unwind_balance frontSource savedSource tailSource
          survivingResumes survivingDisposals nextUnique
          (by simpa only [RecursiveConsumption.remove_owner_append] using normalSavedCheck)
          (by simpa only [RecursiveConsumption.remove_owner_append] using normalFrontCheck)
          (by simpa only [RecursiveConsumption.remove_owner_append] using normalTailCheck)
          reentryBounds (by simpa only [demandSame, List.append_assoc] using nextBalance)
        have scopes : LexicalUnwind.UnwindPrefix front := by cases reentryBounds with | unwind scopes _ _ _ => exact scopes
        obtain ⟨closeDemand, closeRequirements, cleanup, aligned⟩ := frontSource.unwind_reentry scopes frontBalance
        exact ⟨closeDemand, closeRequirements, aligned.symm, fun _ => cleanup⟩
  refine ⟨boundary, frontDemand, frontRequirements, frontScope, _, frontRow, tailRow,
    closeDemand, closeRequirements, aligned, payload, frontSource, returns, cleanup, combinedBound, nextBound, localRetained,
    ?_, trace, nextUnique, survivingResumes, survivingDisposals⟩
  intro coveredCaller
  have callerEffects : ReturnEffects operations policy contracts tables families world front frontDemand frontScope
      (OwnerPhases.ofStack tables (.spent owner answerType caller tail) ++ [])
      (spendAll (available (ownedTickets (captured.append (front.append (.spent owner answerType caller tail))))) contract.resumeDemand)
      certificateRow boundary.mode := by
    cases boundary with
    | value answer => exact .ordinary
    | unwind =>
        have path := coveredCaller rfl
        have closingSource := cleanup rfl
        obtain ⟨choiceRow, choiceCheck, choiceBound⟩ := path.checked certificate
        obtain ⟨normalRow, closeRow, normalCheck, closeCheck, choiceSame⟩ :=
          RecursiveExpressions.choice_parts choiceCheck
        have closingBound : closeRow ⊆ certificateRow :=
          (List.subset_append_right _ _).trans (choiceSame ▸ choiceBound)
        have closingAtCaller := RecursiveRequirements.checked_prepend_iff.mp closeCheck
        simp only [spendAll] at closingAtCaller
        rw [← phaseSame] at closingAtCaller
        have consumedAfter := RecursiveTransport.phases_spendAll_later (owners := contract.resumeDemand) owner consumed
        have contexts := RecursiveRecomposition.normalize_replaced
          (front := .nil) (capture := captured) (tail := tail) (input := inputType) (answer := answerType)
          (caller := caller) (tables := tables) (receiving := []) consumedAfter
        have closingChecked := RecursiveTransport.checked_transport closingAtCaller
          (RecursiveTransport.remove_consumed_agrees consumedAfter)
          (by simpa only [Stack.append] using contexts)
        exact .unwind closingSource aligned.symm (closingSource.template.effects_of_checked closingChecked closingBound)
  obtain ⟨demand, requirements, row, rebuilt, sameDemand, checked, covered⟩ :=
    ModeSource.resume_checked_recomposition known answerAnnotation callerScope savedSource frontSource tailSource
      returns consumed (by simpa only [List.append_nil] using savedChecked)
      (by simpa only [List.append_nil] using frontChecked) tailChecked frontBound callerEffects
  have normalCovered : row ⊆ certificateRow := covered.trans (List.append_subset.mpr
    ⟨List.append_subset.mpr ⟨savedRowBound.trans resumeBound, List.Subset.refl _⟩, tailBound⟩)
  obtain ⟨retained, retainedAnnotation, retainedPath⟩ := annotation.focus
    (show RequirementPath pendingRequirements
      (.sequence (currentRequirements.prepend
        (OwnerPhases.ofStack tables (front.append (.live owner inputType answerType captured caller tail)))) pendingRequirements)
      currentDemand from by simpa only [List.append_nil] using
        (RequirementPath.second (.here : RequirementPath pendingRequirements pendingRequirements [])))
  obtain ⟨retainedRow, retainedCheck, retainedBound⟩ := retainedPath.checked certificate
  rw [currentDemandSame] at retainedCheck
  simp only [spendAll] at retainedCheck
  rw [← phaseSame] at retainedCheck
  have retainedAfter := RecursiveTransport.checked_remove_consumed retainedCheck
    (RecursiveTransport.phases_spendAll_later (owners := contract.resumeDemand) owner consumed)
  obtain ⟨continuing, continuingRow, continuingCheck, continuingBound, retainedInContinuing, cleanupInContinuing⟩ :
      ∃ continuing : Requirements pendingDemand, ∃ continuingRow,
        RecursiveRequirements.Checked (RecursiveTransport.removeOwner owner annotatedStore) []
          (spendAll (available (ownedTickets (captured.append (front.append (.spent owner answerType caller tail))))) contract.resumeDemand)
          continuing continuingRow ∧ continuingRow ⊆ certificateRow ∧
        RequirementPath retained continuing [] ∧
        (boundary.mode = .unwind →
          RequirementPath
            (.choice
              (frontRequirements.prepend (OwnerPhases.ofStack tables (.live owner inputType answerType captured caller tail)))
              (closeRequirements.prepend (OwnerPhases.ofStack tables (.live owner inputType answerType captured caller tail))) aligned)
            continuing []) := by
    cases boundary with
    | value answer => exact ⟨retained, retainedRow, retainedAfter, retainedBound, .here,
        by intro impossible; cases impossible⟩
    | unwind =>
        obtain ⟨remainingDemand, remaining, sameRemaining, selected, checkedRemaining⟩ := (coveredCaller rfl).remainder
        have alignedRemaining : pendingDemand.Perm remainingDemand := by
          rw [← currentDemandSame] at sameRemaining
          exact (List.perm_append_left_iff _).mp sameRemaining
        obtain ⟨remainingRow, remainingCheck, remainingBound⟩ := checkedRemaining _ _ _ _ certificate
        simp only [spendAll] at remainingCheck
        rw [← phaseSame] at remainingCheck
        have remainingAfter := RecursiveTransport.checked_remove_consumed remainingCheck
          (RecursiveTransport.phases_spendAll_later (owners := contract.resumeDemand) owner consumed)
        exact ⟨.choice retained remaining alignedRemaining, retainedRow ++ remainingRow,
          .choice retainedAfter remainingAfter, List.append_subset.mpr ⟨retainedBound, remainingBound⟩,
          .yes .here, fun _ => .no selected⟩
  have savedAtRoot : RecursiveRequirements.Checked (RecursiveTransport.removeOwner owner annotatedStore) []
      (available (ownedTickets (captured.append (front.append (.spent owner answerType caller tail)))))
      (savedAnnotated.prepend (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail)))) resumeRow :=
    RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.append_nil] using savedAnnotatedCheck)
  have retainedSequence := RecursiveRequirements.Checked.sequence savedAtRoot continuingCheck
  have sameRetained : demand.Perm (contract.resumeDemand ++ pendingDemand) := by
    simpa only [demandSame, List.append_assoc] using sameDemand
  let annotatedNext := Requirements.choice requirements
    (.sequence (savedAnnotated.prepend (OwnerPhases.ofStack tables (front.append (.spent owner answerType caller tail)))) continuing)
    sameRetained
  have annotatedCheck : RecursiveRequirements.Checked (RecursiveTransport.removeOwner owner annotatedStore) []
      (available (ownedTickets (captured.append (front.append (.spent owner answerType caller tail)))))
      annotatedNext (row ++ (resumeRow ++ continuingRow)) := .choice checked retainedSequence
  refine ⟨demand, requirements, annotatedNext, row, _, rebuilt, checked, normalCovered,
    .alternatives .original sameRetained, annotatedCheck, ?_,
    ⟨retained, retainedAnnotation, retainedPath, ?_⟩, ?_,
    ⟨savedAnnotated, savedAnnotation, .no (.first .here)⟩, sameDemand.trans ?_⟩
  · exact List.append_subset.mpr ⟨normalCovered, List.append_subset.mpr ⟨resumeBound, continuingBound⟩⟩
  · exact .no (by simpa only [List.append_nil] using
      (RequirementPath.second retainedInContinuing))
  · intro unwinding
    exact .no (by simpa only [List.append_nil] using
      (RequirementPath.second (cleanupInContinuing unwinding)))
  · simpa only [demandSame, List.append_assoc] using nextBalance

end Ash.OneShot.SourceDependencySchemes.Lexical
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.resume_mode_segments



namespace Ash.OneShot.SourceDependencySchemes.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations SourceDependencyFrames
open RecursiveRequirements (Requirements Store)

/-- Clause admission sees the exact stored resume body, including an unwind
return, through the existing rich source and capture-location certificate. -/
theorem ResumeAnnotated.row_source
    (record : ResumeAnnotated operations policy contracts tables families actions annotations world root key body) :
    ClauseRowAdmission.StoreCertified operations.erase policy contracts.erase tables world root key body := by
  cases record with
  | resume located known recorded source returns =>
      refine .resume located (contract_erase_known known) source.row_source ?_
      rcases returns with rfl | rfl
      · exact .inl rfl
      · exact .inr rfl

/-- The source and record facets of the actual mixed machine establish the
existing clause admission interface. The exact record bodies remain separate
from any alternate source witness carried by the active stack. -/
theorem mode_row_store
    (source : ModeSource operations policy contracts tables families actions world
      stack input output demand requirements scope)
    (records : ∀ key body, (key, body) ∈ (resumes : Store) →
      ResumeAnnotated operations policy contracts tables families actions annotations world stack key body)
    (closing : UnwindRecords operations policy contracts tables world stack disposals)
    (known : contracts owner = some contract)
    (storeAnnotation : StoreAnnotation (resumes ++ disposals) annotatedStore) :
    ClauseRowAdmission.SourceStore operations.erase owner contract.erase annotatedStore :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, source.row_source,
    fun key body member => (records key body member).row_source, closing.row_source, contract_erase_known known, storeAnnotation⟩

/-- Instantiate a hereditary clause annotation against the actual mixed
capture store. Both its additional static checks and its original source check
survive substitution. No whole-clause successor check is assumed. -/
theorem instantiate_mode_clause
    (source : ModeSource operations policy contracts tables families actions world
      stack input output demand requirements scope)
    (records : ∀ key body, (key, body) ∈ (resumes : Store) →
      ResumeAnnotated operations policy contracts tables families actions annotations world stack key body)
    (closing : UnwindRecords operations policy contracts tables world stack disposals)
    (known : contracts owner = some contract)
    (storeAnnotation : StoreAnnotation (resumes ++ disposals) annotatedStore)
    (body : Body operations policy contracts world allowed (.ticket binder owner)
      (environment.extend parameter argument) code answer
      ⟨owner, contract.erase, disposes, advertised⟩ dependencies)
    (operand : ValueSummary operations policy contracts world environment allowed value argument)
    (closed : ClosedValue value)
    (interface : ClauseRowAdmission.Interface owner contract.erase disposes annotatedStore
      tail before requestRow)
    (exported : OwnerSource.exportAt tail before advertised = some requestRow) :
    ∃ clauseDemand, ∃ clauseRequirements annotated : Requirements clauseDemand,
    ∃ row annotatedRow,
      Expression operations policy contracts world allowed (.ticket binder owner) environment
        (code.subst parameter value) answer clauseDemand clauseRequirements dependencies ∧
      RowAnnotation clauseRequirements annotated ∧
      RecursiveRequirements.Checked annotatedStore (.live owner contract.held :: tail)
        before annotated annotatedRow ∧ EffectBounds.Covers (requestRow ++ contract.resumeRow) annotatedRow ∧
      RecursiveRequirements.Checked annotatedStore (.live owner contract.held :: tail)
        before clauseRequirements row ∧ EffectBounds.Covers (requestRow ++ contract.resumeRow) row := by
  obtain ⟨_, _, _, expression, annotation, rows⟩ := body.row_annotation
  obtain ⟨annotatedRow, checked, covered⟩ := rows.instantiate interface exported (mode_row_store source records closing known storeAnnotation)
  obtain ⟨row, normalCheck, within⟩ := annotation.checked checked
  exact ⟨_, _, _, row, annotatedRow, substitution expression operand closed, annotation,
    checked, covered, normalCheck, within.trans covered⟩

end Ash.OneShot.SourceDependencySchemes.Lexical
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.ResumeAnnotated.row_source
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.mode_row_store
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.instantiate_mode_clause


namespace Ash.OneShot.SourceDependencySchemes.Closing
open ScopedExpressions ScopedExecution SourceDependencyAnnotations
open SourceDependencyOwners
open SourceDependencyCapture (Realizes)

/-- The installation annotation identifies a stored source scope inside the
same lexical owner bound, including dormant captures. -/
theorem Bound.captured_pending {capture : Stack}
    (realized : Realizes tables families scope stack)
    (bound : Bound annotations scope)
    (pending : PendingWithin world owned scope)
    (located : SourceTemplates.CapturedIn owner capture stack)
    (recorded : annotations owner = some capturedScope) :
    PendingWithin world owned capturedScope := by
  induction realized with
  | nil => cases located
  | push frame rest ih =>
      cases located with | push located =>
        cases frame <;> cases bound <;> cases pending <;> exact ih ‹_› ‹_› located
  | live saved tail ihSaved ihTail =>
      cases bound with | live known inside outside =>
        cases pending with | live savedPending tailPending =>
          cases located with
          | here => cases Option.some.inj (known.symm.trans recorded); exact savedPending
          | saved located => exact ihSaved inside savedPending located
          | tail located => exact ihTail outside tailPending located
  | spent tail ih =>
      cases bound with | spent outside =>
        cases pending with | spent later =>
          cases located with | spent located => exact ih outside later located

end Ash.OneShot.SourceDependencySchemes.Closing
#print axioms Ash.OneShot.SourceDependencySchemes.Closing.Bound.captured_pending


namespace Ash.OneShot.SourceDependencySchemes.Lexical.Recursive
open ScopedExpressions
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceDependencyChecks.Lexical.ReturnHints.Recursive (Local Pending)

/-- Reuse phase, permission and world extension through the recursive source
judgments. Consumed-owner subchecks use the existing spend extension law. -/
theorem local_transport
    (source : Local outward actions before world dependencies hints)
    (extension : PhaseExtension before after) (permissions : Syntax.UsageExtension actions nextActions)
    (larger : world ⊆ nextWorld) : Local outward nextActions after nextWorld dependencies hints := by
  refine (Local.rec
    (motive_1 := fun before world dependencies scope hints _ => ∀ after nextActions nextWorld,
      PhaseExtension before after → Syntax.UsageExtension actions nextActions → world ⊆ nextWorld →
      Local outward nextActions after nextWorld dependencies hints)
    (motive_2 := fun before world scope outside hints outsideHints initial finalMode _ => ∀ after nextActions nextWorld,
      PhaseExtension before after → Syntax.UsageExtension actions nextActions → world ⊆ nextWorld →
      Pending outward nextActions after nextWorld hints outsideHints initial finalMode)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (t := source))
    after nextActions nextWorld extension permissions larger
  · intros; exact .pure
  · intros
    rename_i guard callbacks bound ihCallbacks after nextActions nextWorld extension permissions larger
    exact .request guard
      (fun captured tail contract modes same selected disposes =>
        ihCallbacks captured tail contract modes same selected disposes after nextActions nextWorld extension permissions larger)
      (fun captured tail contract modes selected disposes =>
        (bound captured tail contract modes selected disposes).world_weaken larger)
  · intros
    rename_i located known permission available restored ih after nextActions nextWorld extension permissions larger
    exact .resume located (permissions _ _ known) permission (extension _ available)
      (ih _ nextActions nextWorld extension.spend permissions larger)
  · intros
    rename_i located known permission available unprotected callbacks waiting ihCallbacks ihWaiting after nextActions nextWorld extension permissions larger
    exact .dispose located (permissions _ _ known) permission (extension _ available) unprotected
      (ihCallbacks _ nextActions nextWorld extension.spend permissions larger)
      (ihWaiting _ nextActions nextWorld extension.spend permissions larger)
  · intros
    rename_i first second ihFirst ihSecond after nextActions nextWorld extension permissions larger
    exact .sequence (ihFirst after nextActions nextWorld extension permissions larger)
      (ihSecond after nextActions nextWorld extension permissions larger)
  · intros
    rename_i first second ihFirst ihSecond after nextActions nextWorld extension permissions larger
    exact .choice (ihFirst after nextActions nextWorld extension permissions larger)
      (ihSecond after nextActions nextWorld extension permissions larger)
  · intros
    rename_i body ih after nextActions nextWorld extension permissions larger
    exact .handler (ih after nextActions nextWorld extension permissions larger)
  · intros
    rename_i body callback ihBody ihCallback after nextActions nextWorld extension permissions larger
    exact .cleanup (ihBody after nextActions nextWorld extension permissions larger)
      (ihCallback after nextActions nextWorld extension permissions larger)
  · intros
    rename_i body ih after nextActions nextWorld extension permissions larger
    exact .resource (fun identity fresh => ih identity (fun member => fresh (larger member))
      after nextActions (nextWorld ++ [identity]) extension permissions
      (ScopedExpressions.append_subset larger (List.Subset.refl _)))
  · intros; exact .nil
  · intros
    rename_i first second ihFirst ihSecond after nextActions nextWorld extension permissions larger
    exact .plain (ihFirst after nextActions nextWorld extension permissions larger)
      (ihSecond after nextActions nextWorld extension permissions larger)
  · intros
    rename_i tail ih after nextActions nextWorld extension permissions larger
    exact .skipped (ih after nextActions nextWorld extension permissions larger)
  · intros
    rename_i tail ih after nextActions nextWorld extension permissions larger
    exact .handler (ih after nextActions nextWorld extension permissions larger)
  · intros
    rename_i tail ih after nextActions nextWorld extension permissions larger
    exact .cell (ih after nextActions nextWorld extension permissions larger)
  · intros
    rename_i first second ihFirst ihSecond after nextActions nextWorld extension permissions larger
    exact .cleanup (ihFirst after nextActions nextWorld extension permissions larger)
      (ihSecond after nextActions nextWorld extension permissions larger)
  · intros
    rename_i tail ih after nextActions nextWorld extension permissions larger
    exact .normal (ih after nextActions nextWorld extension permissions larger)
  · intros
    rename_i tail ih after nextActions nextWorld extension permissions larger
    exact .unwinding (ih after nextActions nextWorld extension permissions larger)
  · intros
    rename_i tail ih after nextActions nextWorld extension permissions larger
    exact .closing (ih after nextActions nextWorld extension permissions larger)
  · intros
    rename_i tail ih after nextActions nextWorld extension permissions larger
    exact .retiring (ih after nextActions nextWorld extension permissions larger)
  · intros
    rename_i first second ihFirst ihSecond after nextActions nextWorld extension permissions larger
    exact .live (ihFirst after nextActions nextWorld extension permissions larger)
      (ihSecond after nextActions nextWorld extension permissions larger)
  · intros
    rename_i first second ihFirst ihSecond after nextActions nextWorld extension permissions larger
    exact .opening (ihFirst after nextActions nextWorld extension permissions larger)
      (ihSecond after nextActions nextWorld extension permissions larger)
  · intros
    rename_i tail ih after nextActions nextWorld extension permissions larger
    exact .spent (ih after nextActions nextWorld extension permissions larger)

/-- The same transport applies to the finite retained forest at either mode. -/
theorem pending_transport {hints : ReturnHints scope} {outside : ReturnHints outsideScope}
    (source : Pending outward actions before world hints outside initial finalMode)
    (extension : PhaseExtension before after) (permissions : Syntax.UsageExtension actions nextActions)
    (larger : world ⊆ nextWorld) : Pending outward nextActions after nextWorld hints outside initial finalMode := by
  induction hints generalizing outsideScope initial finalMode with
  | nil => cases source; exact .nil
  | plain rest ih => cases source with
    | plain code tail => exact .plain (local_transport code extension permissions larger) (ih tail)
    | skipped tail => exact .skipped (ih tail)
  | handler rest ih => cases source with | handler tail => exact .handler (ih tail)
  | cell rest ih => cases source with | cell tail => exact .cell (ih tail)
  | cleanup rest ih => cases source with | cleanup callback tail =>
      exact .cleanup (local_transport callback extension permissions larger) (ih tail)
  | running kind rest ih => cases source with
    | normal tail => exact .normal (ih tail)
    | unwinding tail => exact .unwinding (ih tail)
    | closing tail => exact .closing (ih tail)
    | retiring tail => exact .retiring (ih tail)
  | live saved rest ihSaved ihRest => cases source with
    | live inside tail => exact .live (ihSaved inside) (ihRest tail)
    | opening inside tail => exact .opening (ihSaved inside) (ihRest tail)
  | spent rest ih => cases source with | spent tail => exact .spent (ih tail)

end Ash.OneShot.SourceDependencySchemes.Lexical.Recursive
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.Recursive.local_transport
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.Recursive.pending_transport

namespace Ash.OneShot.SourceDependencySchemes.Lexical
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals
open SourceDependencyAnnotations SourceDependencyFrames
open RecursiveRequirements (Requirements Store evaluate)
open OwnerPhaseTransitions (available spend spendAll)
open SourceDependencySchemes.Closing (Bound)

open RecursiveDisposalCapture SourceDependencyOwners.Lexical

/-- A disposing capture's pending-owner bound and exact record sources give
its normal demand the same ownership as its physical mixed-mode segment. -/
theorem mode_capture_ownership_balance
    (cut : HandlerCut requested whole capture tail handler)
    (saved : ModeSource operations policy contracts tables families actions world
      capture input output demand requirements scope)
    (records : ∀ key body, (key, body) ∈ (resumes : Store) →
      ResumeAnnotated operations policy contracts tables families actions annotations world whole key body)
    (closing : ∀ key body, (key, body) ∈ (disposals : Store) →
      UnwindAnnotated operations policy contracts tables families annotations world whole key body)
    (unique : (ownedTickets whole).Nodup)
    (bound : Bound annotations scope)
    (pending : SourceDependencyOwners.PendingWithin world capture.erase.liveTickets scope)
    (checked : RecursiveRequirements.Checked (resumes ++ disposals) receiving (available (ownedTickets whole)) requirements row) :
    demand.Perm (ownedTickets capture) := by
  have captures : ∀ owner nested, SourceTemplates.CapturedIn owner nested capture →
      SourceTemplates.CapturedIn owner nested whole := by
    intro owner nested located
    rw [handler_cut_reconstructs cut]
    exact SavedCaptureIdentity.located_append.mpr (.inl located)
  have retained : ScopedRetirement.scheduled capture ⊆ ScopedRetirement.scheduled whole := by
    rw [handler_cut_reconstructs cut, ScopedRetirement.scheduled_append]
    exact List.subset_append_left _ _
  have owned : ownedTickets capture ⊆ ownedTickets whole := by
    rw [handler_cut_reconstructs cut, owned_tickets_append]
    exact List.subset_append_left _ _
  have captureUnique : (ownedTickets capture).Nodup := by
    rw [handler_cut_reconstructs cut, owned_tickets_append] at unique
    exact (List.nodup_append.mp unique).1
  have inside : demand ⊆ ownedTickets capture := by
    refine checked_demand_bound ?_ ?_ checked
      ((mode_source_calls_within saved pending).trans (recursive_live_tickets_owned capture))
      (mode_segment_retirements_owned saved)
    · intro owner demand body found member
      rcases List.mem_append.mp (SourceTemplates.lookup_member found) with resumed | disposed
      · cases records _ _ resumed with
        | resume located known recorded source returns =>
            have nested := captured_in_preserved_region unique captures retained located member
            have annotated := bound.captured_pending saved.realizes pending nested recorded
            exact ⟨(mode_source_calls_within source annotated).trans (recursive_live_tickets_owned capture),
              (mode_segment_retirements_owned source).trans (captured_owned_subset nested)⟩
      · cases closing _ _ disposed
    · intro owner demand body found member
      rcases List.mem_append.mp (SourceTemplates.lookup_member found) with resumed | disposed
      · cases records _ _ resumed
      · cases closing _ _ disposed with
        | dispose located unprotected recorded source =>
            have nested := captured_in_preserved_region unique captures retained located member
            exact fun _ present => captured_owned_subset nested (source.template.ownership.mem_iff.mp present)
  have resumesKnown : ∀ owner demand (body : Requirements demand),
      RecursiveRequirements.lookup ⟨owner, .resume⟩ (resumes ++ disposals) = some ⟨demand, body⟩ →
      ∃ nested input output scope, SourceTemplates.CapturedIn owner nested whole ∧
        ModeSource operations policy contracts tables families actions world nested input output demand body scope := by
    intro owner demand body found
    rcases List.mem_append.mp (SourceTemplates.lookup_member found) with resumed | disposed
    · cases records _ _ resumed with
      | resume located known recorded source returns => exact ⟨_, _, _, _, located, source⟩
    · cases closing _ _ disposed
  have disposalsKnown : ∀ owner demand (body : Requirements demand),
      RecursiveRequirements.lookup ⟨owner, .dispose⟩ (resumes ++ disposals) = some ⟨demand, body⟩ →
      ∃ nested, SourceTemplates.CapturedIn owner nested whole ∧ demand.Perm (ownedTickets nested) := by
    intro owner demand body found
    rcases List.mem_append.mp (SourceTemplates.lookup_member found) with resumed | disposed
    · cases records _ _ resumed
    · cases closing _ _ disposed with
      | dispose located unprotected recorded source => exact ⟨_, located, source.template.ownership⟩
  have transition := RecursiveRequirements.checked_trace checked
  have ready : ∀ owner ∈ ownedTickets capture, available (ownedTickets whole) owner = .available := by
    intro owner member
    exact if_pos (owned member)
  have complete := ownership_tree_consumed capture _ (mode_segment_spine_consumed saved checked) (by
    intro owner nested located consumed
    have demanded := (OwnerSource.trace_member_iff_changes transition (owner := owner)).mpr (by
      rw [ready owner (SourceTemplates.captured_in_owned located), consumed]
      decide)
    rcases mode_checked_capture_spines resumesKnown disposalsKnown unique checked owner nested
      (captures _ _ located) demanded with retired | complete
    · exact mode_segment_retirement_spines saved captureUnique checked located retired
    · exact complete)
  apply (List.perm_ext_iff_of_nodup (RecursiveRequirements.checked_once checked) captureUnique).mpr
  intro owner
  constructor
  · exact fun member => inside member
  · intro member
    apply (OwnerSource.trace_member_iff_changes transition).mpr
    rw [ready owner member, complete owner member]
    decide


/-- The checked request selects its actual handler offer and hereditary clause
body. Normalize the pending certificate around that handler cut, retaining the
original annotation and a normal split. A structural path supplies the relative
saved annotation and annotated tail used in allocation. The selected declaration
supplies the clause certificate, which is instantiated against the allocated
store and joined to the tail with the existing clause-consumption proof.
One-shot usage, ticket access and resource support hold for that same successor.
The operand's independent finite support bound must fit the selected source
handler's outer suffix. A disposing offer obtains its owner bound and protection from the structural
request check and requires an exact cleanup path in the saved certificate. Neither branch coverage nor
initial admission of support annotations is established here. -/
theorem capture_mode_segments_with_closing_store
    (cut : HandlerCut requested whole capture tail handler)
    (current : Expression operations policy contracts world allowed caller Environment.empty
      (.perform (Instantiation.freezeEffect requested) operation operand) input currentDemand currentRequirements currentDependencies)
    (source : ModeSource operations policy contracts tables families actions world
      whole (.value input) output demand requirements wholeScope)
    {returnHints : SourceDependencyChecks.Lexical.ReturnHints wholeScope}
    (hinted : SourceDependencyChecks.Lexical.ReturnHints.Matches tables families returnHints whole)
    (pendingLocal : SourceDependencyChecks.Lexical.ReturnHints.Recursive.Pending outward actions
      (available (ownedTickets whole)) world returnHints .nil .ordinary output.mode)
    (usage : LexicalUnwind.MachineUse policy actions (.eval
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩))
    (ticketAccess : LexicalUnwind.MachineTicketAccess policy actions (.eval
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩))
    (resourceAccess : LexicalUnwind.MachineAccess ambient (.eval
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩))
    (operandSupport : Syntax.resourceDependencies operand.dependencies ⊆ operandBound)
    (operandBoundary : match SourceDependencyCapture.select requested operation wholeScope with
      | some (.handler _ receiving _ _) => operandBound ⊆ receiving.visibleResources ++ ambient
      | _ => False)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (isValue : operand.IsValue)
    (fresh : contracts owner = none) (freshAction : actions owner = none)
    (absent : owner ∉ ownedTickets whole)
    (bound : Bound annotations wholeScope) (freshAnnotation : annotations owner = none)
    (recorded : ∀ key body, (key, body) ∈ (resumes : Store) →
      ResumeAnnotated operations policy contracts tables families actions annotations world whole key body)
    (closing : UnwindRecords operations policy contracts tables world whole disposals)
    (closingRecorded : ∀ key body, (key, body) ∈ disposals →
      UnwindAnnotated operations policy contracts tables families annotations world whole key body)
    (unique : (ownedTickets whole).Nodup)
    (storeAnnotation : StoreAnnotation (resumes ++ disposals) annotatedStore)
    (annotation : RowAnnotation requirements annotatedRoot)
    (certificate : RecursiveRequirements.Checked annotatedStore []
      (available (ownedTickets whole)) annotatedRoot certificateRow)
    (currentCheck : RecursiveRequirements.Checked annotatedStore (OwnerPhases.ofStack tables whole)
      (available (ownedTickets whole)) currentRequirements requestRow)
    (currentLocal : SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local outward actions
      (available (ownedTickets whole)) world currentDependencies returnHints)
    {answer : Value} {residual : List Instance} {boundary : ModeValue}
    {capDemand tailDemand : List Nat} {capReq : Requirements capDemand} {tailReq : Requirements tailDemand}
    {capScope tailScope : Receiving}
    (declaration : SourceDependencyFrames.Frame operations policy contracts tables families world
      (.handler handler) answer answer [] (.request [] [])
      (.handler handler.effectInst (tables handler) (families handler)) (handler.effectInst :: residual) residual)
    (returns : boundary = .value answer ∨ boundary = .unwind)
    (saved : ModeSource operations policy contracts tables families actions world
      capture (.value input) boundary capDemand capReq capScope)
    (waiting : ModeSource operations policy contracts tables families actions world
      tail boundary output tailDemand tailReq tailScope)
    (scopeSame : wholeScope = capScope.append tailScope)
    (demandSame : demand = capDemand ++ tailDemand)
    (evaluation : ∀ store receiving phases, evaluate store receiving phases requirements =
      merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) phases capReq)
        (evaluate store receiving (spendAll phases capDemand) tailReq))
    {declaredArgument declaredInput : Value}
    {resumeEffects closeEffects : List Instance} {family : Nat → Dependencies}
    {offered : ClauseContract} {advertised : Footprint}
    (chosenOffer : lookup operation (tables handler) = some offered)
    (chosenRow : offered.row capScope.held = some advertised)
    (declaredOperation : operations handler.effectInst operation = some (declaredArgument, declaredInput))
    (familyKnown : (SourceDependencyCapture.lookupDependencies operation (families handler)).bind
      (SourceDependencyCapture.modeDependencies capScope.held) = some family)
    (bodyFamily : ∀ owner (contract : Contract), contracts owner = none →
      contract.input = declaredInput → contract.answer = answer →
      contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
      contract.held = capScope.held → contract.closeDemand.Perm contract.resumeDemand →
      Body operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
        (Environment.empty.extend parameter declaredArgument) code answer
        ⟨owner, contract.erase, offered.dispose, advertised⟩ (family owner)) :
      wholeScope = capScope.append tailScope ∧ demand = capDemand ++ tailDemand ∧
      (boundary = .value answer ∨ boundary = .unwind) ∧
      SourceDependencyFrames.Frame operations policy contracts tables families world (.handler handler) answer answer [] (.request [] [])
        (.handler handler.effectInst (tables handler) (families handler)) (handler.effectInst :: residual) residual ∧
      lookup operation (tables handler) = some offered ∧
      offered.row capScope.held = some advertised ∧
      (SourceDependencyCapture.lookupDependencies operation (families handler)).bind
        (SourceDependencyCapture.modeDependencies capScope.held) = some family ∧
      residualize (CallableProtectionFrames.contextOf tables tail) advertised = some requestRow ∧
      (offered.dispose = true → ProtectionContexts.protectedMode capture.erase = false) ∧
      ∃ cutCertificate : Requirements (capDemand ++ tailDemand), ∃ cutRow,
      RowAnnotation (.sequence (capReq.prepend (OwnerPhases.ofStack tables tail)) tailReq) cutCertificate ∧
      RecursiveRequirements.Checked annotatedStore [] (available (ownedTickets whole)) cutCertificate cutRow ∧
      cutRow ⊆ certificateRow ∧
      RequirementPath annotatedRoot cutCertificate [] ∧
      RequirementPath (.sequence (capReq.prepend (OwnerPhases.ofStack tables tail)) tailReq) cutCertificate [] ∧
      ∀ (capAnnotated : Requirements capDemand) (tailAnnotated : Requirements tailDemand),
        RowAnnotation capReq capAnnotated → RowAnnotation tailReq tailAnnotated →
        (∃ selectedRow, RecursiveRequirements.Checked annotatedStore [] (available (ownedTickets whole))
          (.sequence (capAnnotated.prepend (OwnerPhases.ofStack tables tail)) tailAnnotated) selectedRow ∧
          selectedRow ⊆ certificateRow) →
      ∀ suppliedDemand (suppliedRequirements : Requirements suppliedDemand),
        (ProtectionContexts.protectedMode capture.erase = false →
          UnwindSource operations policy contracts tables families world capture suppliedDemand suppliedRequirements capScope) →
        (offered.dispose = true → RequirementPath suppliedRequirements capAnnotated []) →
      ∃ capRow tailRow, capRow ++ tailRow ⊆ certificateRow ∧
      ∃ closingDemand closingRow, closingDemand.Perm capDemand ∧
      (offered.dispose = false → closingRow = none) ∧
      let contract : Contract := ⟨input, answer, capScope.held, capDemand, capRow,
        closingDemand, closingRow, resumeEffects, closeEffects⟩
      let nextStack := Stack.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail
      let nextResumes : Store := (⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: resumes
      let nextAnnotations := fun other => if other = owner then some capScope else annotations other
      ∃ nextDisposals nextStore : Store,
        nextDisposals = (if ProtectionContexts.protectedMode capture.erase then disposals else
          (⟨owner, .dispose⟩, ⟨suppliedDemand, suppliedRequirements⟩) :: disposals) ∧
        nextStore = (⟨owner, .resume⟩, ⟨capDemand, capAnnotated⟩) ::
          (annotatedStore.take resumes.length ++
            ((if ProtectionContexts.protectedMode capture.erase then [] else
              [(⟨owner, .dispose⟩, ⟨suppliedDemand, suppliedRequirements⟩)]) ++ annotatedStore.drop resumes.length)) ∧
        (offered.dispose = true → RecursiveRequirements.lookup ⟨owner, .dispose⟩ nextStore =
          some ⟨suppliedDemand, suppliedRequirements⟩) ∧
        StoreAnnotation (nextResumes ++ nextDisposals) nextStore ∧
        RecursiveRequirements.lookup ⟨owner, .resume⟩ nextStore = some ⟨capDemand, capAnnotated⟩ ∧
        Bound nextAnnotations (.live owner capScope tailScope) ∧
        ClauseRowAdmission.SourceStore operations.erase owner contract.erase nextStore ∧
        (∀ key body, (key, body) ∈ nextResumes →
          ResumeAnnotated operations policy (contracts.insert owner contract) tables families
            (actions.insert owner code.requiredActions) nextAnnotations world nextStack key body) ∧
        (∀ key body, (key, body) ∈ nextDisposals →
          UnwindAnnotated operations policy (contracts.insert owner contract) tables families
            nextAnnotations world nextStack key body) ∧
        UnwindRecords operations policy (contracts.insert owner contract) tables world nextStack nextDisposals ∧
        ModeSource operations policy (contracts.insert owner contract) tables families
          (actions.insert owner code.requiredActions) world nextStack (.value answer) output tailDemand
          (.sequence (.spent owner) tailReq) (.live owner capScope tailScope) ∧
        (∃ nextHints : SourceDependencyChecks.Lexical.ReturnHints (.live owner capScope tailScope),
          SourceDependencyChecks.Lexical.ReturnHints.Matches tables families nextHints nextStack ∧
          SourceDependencyChecks.Lexical.ReturnHints.Recursive.Pending outward (actions.insert owner code.requiredActions)
            (available (ownedTickets nextStack)) world nextHints .nil .ordinary output.mode ∧
          (code.requiredActions.resume = true →
            SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local outward (actions.insert owner code.requiredActions)
              (available (ownedTickets nextStack)) world (.invoke ⟨owner, .resume⟩) nextHints) ∧
          (code.requiredActions.dispose = true →
            SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local outward (actions.insert owner code.requiredActions)
              (available (ownedTickets nextStack)) world (.invoke ⟨owner, .dispose⟩) nextHints)) ∧
        RowAnnotation (.sequence (.spent owner) tailReq) (.sequence (.spent owner) tailAnnotated) ∧
        LexicalUnwind.MachineUse policy (actions.insert owner code.requiredActions)
          (.eval ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩) ∧
        LexicalUnwind.MachineTicketAccess policy (actions.insert owner code.requiredActions)
          (.eval ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩) ∧
        LexicalUnwind.MachineAccess ambient
          (.eval ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩) ∧
        RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩
          ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩ [.ticket owner] [] ∧
        ownedTickets nextStack = owner :: ownedTickets whole ∧
        (ownedTickets nextStack).Nodup ∧
        ((owner :: capDemand) ++ tailDemand).Perm (ownedTickets nextStack) ∧
        spend (available (ownedTickets nextStack)) owner = available (ownedTickets whole) ∧
        RecursiveRequirements.Checked nextStore (OwnerPhases.ofStack tables tail)
          (available (ownedTickets whole)) capAnnotated capRow ∧
        RecursiveRequirements.Checked nextStore []
          (spendAll (available (ownedTickets whole)) capDemand) tailAnnotated tailRow ∧
        RecursiveRequirements.Checked nextStore (OwnerPhases.ofStack tables nextStack)
          (available (ownedTickets nextStack)) (.invoke ⟨owner, .resume⟩ capDemand []) capRow ∧
        ClauseRowAdmission.Interface owner contract.erase offered.dispose nextStore
          (OwnerPhases.ofStack tables tail) (available (ownedTickets nextStack)) requestRow ∧
          ∃ clauseDemand, ∃ clauseReq clauseAnnotated : Requirements clauseDemand, ∃ clauseRow,
            Expression operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
              Environment.empty (code.subst parameter operand) answer clauseDemand clauseReq (family owner) ∧
            RowAnnotation clauseReq clauseAnnotated ∧
            RecursiveRequirements.Checked nextStore (OwnerPhases.ofStack tables nextStack)
              (available (ownedTickets nextStack)) clauseAnnotated clauseRow ∧
            clauseRow ⊆ requestRow ++ capRow ∧
            clauseDemand.Perm (owner :: capDemand) ∧
            RowAnnotation
              (.sequence (clauseReq.prepend (OwnerPhases.ofStack tables nextStack)) (.sequence (.spent owner) tailReq))
              (.sequence (clauseAnnotated.prepend (OwnerPhases.ofStack tables nextStack)) (.sequence (.spent owner) tailAnnotated)) ∧
            RecursiveRequirements.Checked nextStore [] (available (ownedTickets nextStack))
              (.sequence (clauseAnnotated.prepend (OwnerPhases.ofStack tables nextStack)) (.sequence (.spent owner) tailAnnotated))
              (clauseRow ++ tailRow) ∧
            clauseRow ++ tailRow ⊆ requestRow ++ certificateRow ∧
            (clauseDemand ++ tailDemand).Perm (ownedTickets nextStack) := by
  obtain ⟨argument, operationKnown, payload⟩ : ∃ argument,
      operations requested operation = some (argument, input) ∧
      ValueSummary operations policy contracts world Environment.empty allowed operand argument := by
    generalize encoded : Instantiation.freezeEffect requested = actual at current
    cases current with
    | perform known admitted operandSource formed =>
        cases freeze_effect_injective encoded
        exact ⟨_, known, Values.summary operandSource isValue⟩
  have requestLocal := SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local.ready_request current currentLocal
  have closed : ClosedValue operand := ScopedPorts.typed_value_closed
    ((DeclaredSourceValues.erase (value_erase payload)).ports .none) isValue
  have resourceChecks : LexicalUnwind.AccessConditions
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩ ambient := by
    cases found : SourceDependencyCapture.select requested operation wholeScope with
    | none => simp only [found] at operandBoundary
    | some selection => cases selection with
      | builtin identity => simp only [found] at operandBoundary
      | handler saved receiving offered modes =>
          exact SourceDependencyCapture.source_request_access source.realizes found operandSupport
            (by simpa only [found] using operandBoundary)
  have erasedCurrent := DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase current)
  have requestExport := RecursiveRequirements.checked_complete currentCheck
  rw [RecursiveDispatch.request_evaluation erasedCurrent closed.1] at requestExport
  simp only [OwnerSource.exportAt, OwnerPhaseTransitions.project_actual] at requestExport
  obtain ⟨actualOffer, actualRow, offeredKnown, offeredMode, offeredRow, offeredExport⟩ :=
    RecursiveDispatch.cut_residual cut requestExport
  have sameOffer : actualOffer = offered := Option.some.inj (offeredKnown.symm.trans chosenOffer)
  subst actualOffer
  simp only [Bool.false_or] at offeredMode offeredRow
  have sameRow : actualRow = advertised := Option.some.inj
    ((by simpa only [saved.realizes.held] using offeredRow : offered.row capScope.held = some actualRow).symm.trans chosenRow)
  subst actualRow
  obtain ⟨pendingRow, pendingCheck, pendingBound⟩ := annotation.checked certificate
  obtain ⟨_, normalStoreCheck, _⟩ := storeAnnotation.checked pendingCheck
  have balanced := mode_stack_ownership_balance source recorded closingRecorded unique normalStoreCheck
  obtain ⟨annotatedResumes, annotatedDisposals, rfl, resumeAnnotation, disposalAnnotation⟩ := storeAnnotation.split
  have lengths : ∀ {original annotated : Store}, StoreAnnotation original annotated → annotated.length = original.length := by
    intro original annotated source
    induction source with
    | nil => rfl
    | cons head tail ih => exact congrArg Nat.succ ih
  have resumeLength := lengths resumeAnnotation
  obtain ⟨localCaptureScope, localTailScope, capHints, tailHints, localBoundary,
    localScope, localHints, capMatched, tailMatched, capturedLocal, tailLocal⟩ :=
    pendingLocal.handler_cut hinted cut
  have localScopes := saved.realizes.append_scopes_unique
    (SourceDependencyChecks.Lexical.ReturnHints.Matches.erases capMatched) (scopeSame.symm.trans localScope)
  obtain ⟨rfl, rfl⟩ := localScopes
  have localMode : localBoundary = boundary.mode := capturedLocal.return_mode.symm.trans
    ((SourceDependencyChecks.Lexical.ReturnHints.Matches.return_mode capMatched).trans saved.return_mode)
  rw [localMode] at capturedLocal tailLocal
  have declarations : Declarations operations policy contracts world Environment.empty residual
      handler.effectInst answer handler.clauses (tables handler) (families handler) := by
    cases declaration with | handler scope annotation clauses coverage unique declarations capabilities modes => exact declarations
  obtain ⟨actualCapture, actualTail, realizedCapture, realizedTail, actualScope, selection⟩ := source.realizes.cut cut
  have matched := saved.realizes.append_scopes_unique realizedCapture (scopeSame.symm.trans actualScope)
  rw [← matched.1, ← matched.2] at selection
  have guarded := SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local.request_guard requestLocal
  obtain ⟨modes, selectedScope⟩ : ∃ modes,
      SourceDependencyCapture.select requested operation wholeScope =
        some (.handler capScope tailScope offered modes) := by
    cases modesFound : SourceDependencyCapture.lookupDependencies operation (families handler) with
    | none =>
        have missing : SourceDependencyCapture.select requested operation wholeScope = none := by
          simpa only [SourceDependencyCapture.chosen, offeredKnown, modesFound] using selection operation
        cases guarded with
        | builtin actual => rw [missing] at actual; cases actual
        | handler actual permission row body => rw [missing] at actual; cases actual
    | some modes =>
        exact ⟨modes, by simpa only [SourceDependencyCapture.chosen, offeredKnown, modesFound] using selection operation⟩
  have rowAvailable : offered.row capScope.held = some advertised := by
    simpa only [saved.realizes.held] using offeredRow
  rw [ScopedTyping.handler_cut_instance cut] at declaredOperation
  obtain ⟨argumentSame, inputSame⟩ := Prod.mk.inj (Option.some.inj (declaredOperation.symm.trans operationKnown))
  subst declaredArgument
  subst declaredInput
  have evaluated := RecursiveRequirements.checked_complete pendingCheck
  rw [evaluation] at evaluated
  obtain ⟨normalCapRow, normalTailRow, inside, outside, rowSame⟩ := PhaseRechecking.merge_split evaluated
  have normalSavedCheck : RecursiveRequirements.Checked (annotatedResumes ++ annotatedDisposals) []
      (available (ownedTickets whole)) (capReq.prepend (OwnerPhases.ofStack tables tail)) normalCapRow :=
    RecursiveRequirements.checked_prepend_iff.mpr (RecursiveRequirements.evaluate_sound inside)
  have normalTailCheck := RecursiveRequirements.evaluate_sound outside
  have splitSame : (capDemand ++ tailDemand).Perm demand := by rw [demandSame]
  let cutCertificate := Requirements.choice
    (.sequence (capReq.prepend (OwnerPhases.ofStack tables tail)) tailReq) annotatedRoot splitSame
  have cutCheck : RecursiveRequirements.Checked (annotatedResumes ++ annotatedDisposals) []
      (available (ownedTickets whole)) cutCertificate ((normalCapRow ++ normalTailRow) ++ certificateRow) :=
    .choice (.sequence normalSavedCheck normalTailCheck) certificate
  have cutBound : (normalCapRow ++ normalTailRow) ++ certificateRow ⊆ certificateRow :=
    List.append_subset.mpr ⟨rowSame ▸ pendingBound, List.Subset.refl _⟩
  refine ⟨scopeSame, demandSame, returns, declaration, offeredKnown, rowAvailable,
    familyKnown, offeredExport,
    (fun permitted => saved.realizes.held.symm.trans (guarded.disposing_unprotected selectedScope permitted)), cutCertificate, _,
    .alternatives .original splitSame, cutCheck, cutBound, .no .here, .yes .here, ?_⟩
  intro capAnnotated tailAnnotated capAnnotation tailAnnotation selectedPath suppliedDemand suppliedRequirements suppliedSource cleanupPath
  obtain ⟨selectedRow, selectedCheck, selectedBound⟩ := selectedPath
  obtain ⟨capRow, tailRow, capCheck, tailCheck, rowSame⟩ := RecursiveRequirements.checked_sequence_parts selectedCheck
  have branchBound : capRow ++ tailRow ⊆ certificateRow := rowSame ▸ selectedBound
  have savedCheck : RecursiveRequirements.Checked (annotatedResumes ++ annotatedDisposals) (OwnerPhases.ofStack tables tail)
      (available (ownedTickets whole)) capAnnotated capRow := by
    simpa only [List.append_nil] using RecursiveRequirements.checked_prepend_iff.mp capCheck
  let nextStack := Stack.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail
  let nextAnnotations := fun other => if other = owner then some capScope else annotations other
  have annotationExtension : ∀ other captured, annotations other = some captured → nextAnnotations other = some captured := by
    intro other captured known
    by_cases same : other = owner
    · subst other; rw [freshAnnotation] at known; cases known
    · simpa only [nextAnnotations, if_neg same] using known
  have preserved : ∀ key body, (key, body) ∈ disposals →
      UnwindAnnotated operations policy contracts tables families nextAnnotations world nextStack key body := by
    intro key body member
    exact (closingRecorded key body member).transport (fun _ _ known => known) annotationExtension (List.Subset.refl _) (by
      intro other captured located
      rw [handler_cut_reconstructs cut] at located
      rcases SavedCaptureIdentity.located_append.mp located with inside | outside
      · exact .saved inside
      · exact .tail outside)
  obtain ⟨closingDemand, closingRow, added, closingBalance, noClosing, addedOrigin, chosen, keys, annotated, disposalData⟩ :
      ∃ closingDemand, ∃ closingRow : Option Footprint, ∃ added : Store,
      closingDemand.Perm capDemand ∧ (offered.dispose = false → closingRow = none) ∧
      added = (if ProtectionContexts.protectedMode capture.erase then [] else
        [(⟨owner, .dispose⟩, ⟨suppliedDemand, suppliedRequirements⟩)]) ∧
      UnwindRecords operations policy contracts tables world nextStack (added ++ disposals) ∧
      (∀ key body, (key, body) ∈ added → key.owner = owner ∧ key.mode = .dispose) ∧
      (∀ key body, (key, body) ∈ added ++ disposals →
        UnwindAnnotated operations policy contracts tables families nextAnnotations world nextStack key body) ∧
      (offered.dispose = true → ∃ closingRequirements : Requirements closingDemand,
        added = [(⟨owner, .dispose⟩, ⟨closingDemand, closingRequirements⟩)] ∧
        UnwindTemplate operations policy contracts tables world capture closingDemand closingRequirements ∧
        ∃ row, closingRow = some row ∧
          RecursiveRequirements.evaluate [] (OwnerPhases.ofStack tables tail)
            (available (ownedTickets whole)) closingRequirements = some row ∧ row ⊆ capRow) := by
    cases disposes : offered.dispose with
    | false =>
        cases held : ProtectionContexts.protectedMode capture.erase with
        | true =>
            exact ⟨capDemand, none, [], .refl _, fun _ => rfl, (by simp),
              closing.capture_protected cut held, (by intro key body member; cases member), preserved,
              (by intro impossible; cases impossible)⟩
        | false =>
            have summary := suppliedSource held
            let closeDemand := suppliedDemand
            let closeRequirements := suppliedRequirements
            refine ⟨capDemand, none, [(⟨owner, .dispose⟩, ⟨closeDemand, closeRequirements⟩)],
              .refl _, fun _ => rfl, (by simp [closeDemand, closeRequirements]), closing.capture_with_template cut held summary.template, ?_, ?_, ?_⟩
            · intro key body member
              cases List.mem_singleton.mp member
              exact ⟨rfl, rfl⟩
            · intro key body member
              rcases List.mem_cons.mp member with same | old
              · cases same
                exact .dispose .here held (by simp [nextAnnotations]) summary
              · exact preserved key body old
            · intro impossible; cases impossible
    | true =>
        have held : ProtectionContexts.protectedMode capture.erase = false :=
          saved.realizes.held.symm.trans (guarded.disposing_unprotected selectedScope disposes)
        have pending : SourceDependencyOwners.PendingWithin world capture.erase.liveTickets capScope := by
          cases requestLocal with
          | request guard callbacks owners =>
              simpa only [SourceDependencyOwners.realized_owners saved.realizes] using
                owners _ _ _ _ selectedScope disposes
        have capBound : Bound annotations capScope :=
          (Bound.append_iff.mp (scopeSame ▸ bound)).1
        have summary := suppliedSource held
        let closeDemand := suppliedDemand
        let closeRequirements := suppliedRequirements
        have path := cleanupPath disposes
        obtain ⟨closeRow, closeCheck, closeBound⟩ := path.checked savedCheck
        simp only [spendAll] at closeCheck
        have evaluation : RecursiveRequirements.evaluate [] (OwnerPhases.ofStack tables tail)
            (available (ownedTickets whole)) closeRequirements = some closeRow := by
          rw [summary.template.store (first := []) (second := annotatedResumes ++ annotatedDisposals)]
          exact RecursiveRequirements.checked_complete closeCheck
        obtain ⟨normalRow, normalCheck, normalBound⟩ := capAnnotation.checked savedCheck
        obtain ⟨sourceRow, sourceCheck, sourceBound⟩ := (resumeAnnotation.append disposalAnnotation).checked normalCheck
        have balance := mode_capture_ownership_balance cut saved recorded closingRecorded unique capBound pending sourceCheck
        refine ⟨closeDemand, some closeRow, [(⟨owner, .dispose⟩, ⟨closeDemand, closeRequirements⟩)],
          summary.template.ownership.trans balance.symm, ?_, (by simp [held, closeDemand, closeRequirements]),
          closing.capture_with_template cut held summary.template, ?_, ?_, ?_⟩
        · intro impossible; cases impossible
        · intro key body member
          cases List.mem_singleton.mp member
          exact ⟨rfl, rfl⟩
        · intro key body member
          rcases List.mem_cons.mp member with same | old
          · cases same
            exact .dispose .here held (by simp [nextAnnotations]) summary
          · exact preserved key body old
        · intro _
          exact ⟨closeRequirements, rfl, summary.template, closeRow, rfl, evaluation, closeBound⟩
  let contract : Contract := ⟨input, answer, capScope.held, capDemand, capRow,
    closingDemand, closingRow, resumeEffects, closeEffects⟩
  have extension := SourceDependencyAnnotations.insert_extends (contract := contract) contracts fresh
  have permissions := Syntax.fresh_usage_insert_extends (rights := code.requiredActions) freshAction
  have known : (contracts.insert owner contract) owner = some contract := by simp [Contracts.insert]
  have actionKnown : (actions.insert owner code.requiredActions) owner = some code.requiredActions := by
    simp [Syntax.UsageTickets.insert]
  have nextResume := capture_resume_records
    (input := ScopedPorts.embedPort input.erase.port) (answer := handler.answer) (caller := handler.scope)
    cut saved returns known scopeSame bound freshAnnotation recorded extension permissions
  have consumed : available (ownedTickets whole) owner = .consumed := by simp [available, absent]
  have laterConsumed := RecursiveTransport.phases_spendAll_later (owners := capDemand) owner consumed
  have savedAfter := RecursiveCapture.checked_insert_consumed
    (RecursiveAllocation.checked_add_closing savedCheck consumed keys) consumed
      (mode := .resume) (body := ⟨capDemand, capAnnotated⟩)
  have tailAfter := RecursiveCapture.checked_insert_consumed
    (RecursiveAllocation.checked_add_closing tailCheck laterConsumed keys) laterConsumed
      (mode := .resume) (body := ⟨capDemand, capAnnotated⟩)
  let nextStore : Store := (⟨owner, .resume⟩, ⟨capDemand, capAnnotated⟩) ::
    (annotatedResumes ++ (added ++ annotatedDisposals))
  have nextStoreAnnotation : StoreAnnotation
      (((⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: resumes) ++ (added ++ disposals)) nextStore :=
    .cons capAnnotation (resumeAnnotation.append ((StoreAnnotation.refl added).append disposalAnnotation))
  have phaseSame := RecursiveCapture.capture_phase_consumed (input := ScopedPorts.embedPort input.erase.port) cut absent
  have owned := RecursiveCapture.capture_owned (owner := owner) (input := ScopedPorts.embedPort input.erase.port) cut
  have afterUnique : (ownedTickets nextStack).Nodup := by
    rw [owned]
    exact List.nodup_cons.mpr ⟨absent, unique⟩
  have afterBalance : ((owner :: capDemand) ++ tailDemand).Perm (ownedTickets nextStack) := by
    rw [owned, List.cons_append, ← demandSame]
    exact balanced.cons owner
  have nextSource : ModeSource operations policy (contracts.insert owner contract) tables families
      (actions.insert owner code.requiredActions) world nextStack (.value answer) output tailDemand
      (.sequence (.spent owner) tailReq) (.live owner capScope tailScope) := by
    cases declaration with
    | handler scope annotation clauses coverage unique declarations capabilities modes =>
      have ports := CoherentSourceTypes.Owners.port_contracts_extension (erased_contract_extension extension)
      exact .live known actionKnown (ScopedPorts.erase_embed_port input.erase.port).symm annotation
        (ScopedPorts.effect_scope_known_extension scope ports) saved.realizes.held
        (saved.transport extension permissions (List.Subset.refl _)) returns
        (waiting.transport extension permissions (List.Subset.refl _))
  have phaseExtension : PhaseExtension (available (ownedTickets whole)) (available (ownedTickets nextStack)) := by
    rw [owned, ← OwnerPhaseTransitions.introduce_available]
    exact introduce_extends
  have nextPending : SourceDependencyChecks.Lexical.ReturnHints.Recursive.Pending outward (actions.insert owner code.requiredActions)
      (available (ownedTickets nextStack)) world
      (.live (owner := owner) capHints tailHints) .nil .ordinary output.mode :=
    .live (Recursive.pending_transport capturedLocal phaseExtension permissions (List.Subset.refl _))
      (Recursive.pending_transport tailLocal phaseExtension permissions (List.Subset.refl _))
  have nextReady : available (ownedTickets nextStack) owner = .available := by
    rw [owned]
    simp [available]
  have consumedPending : SourceDependencyChecks.Lexical.ReturnHints.Recursive.Pending outward
      (actions.insert owner code.requiredActions) (spend (available (ownedTickets nextStack)) owner) world
      (.live (owner := owner) capHints tailHints) .nil .ordinary output.mode := by
    rw [phaseSame]
    exact .live
      (Recursive.pending_transport capturedLocal (fun _ ready => ready) permissions (List.Subset.refl _))
      (Recursive.pending_transport tailLocal (fun _ ready => ready) permissions (List.Subset.refl _))
  have nextResumeLocal : code.requiredActions.resume = true →
      SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local outward (actions.insert owner code.requiredActions)
        (available (ownedTickets nextStack)) world (.invoke ⟨owner, .resume⟩) (.live (owner := owner) capHints tailHints) := by
    intro permission
    exact SourceDependencyNeutral.Lexical.Recursive.resume_clause_from_retained
      actionKnown permission nextReady consumedPending
  have nextDisposeLocal : code.requiredActions.dispose = true →
      SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local outward (actions.insert owner code.requiredActions)
        (available (ownedTickets nextStack)) world (.invoke ⟨owner, .dispose⟩) (.live (owner := owner) capHints tailHints) := by
    intro permission
    have disposes : offered.dispose = true := by
      cases declaration with
      | handler scope annotation clauses coverage unique declarations capabilities modes =>
        obtain ⟨actual, declared, permitted⟩ := SourceTemplates.selected_clause_mode selected modes
        cases Option.some.inj (offeredKnown.symm.trans declared)
        exact permitted permission
    apply SourceDependencyNeutral.Lexical.Recursive.dispose_clause_from_retained
      actionKnown permission nextReady (guarded.disposing_unprotected selectedScope disposes) consumedPending
    rw [phaseSame]
    cases requestLocal with
    | request guard callbacks owners =>
      exact Recursive.pending_transport
        (callbacks capHints tailHints _ _ localHints selectedScope disposes)
        (fun _ ready => ready) permissions (List.Subset.refl _)
  have nextMatching : SourceDependencyChecks.Lexical.ReturnHints.Matches tables families
      (.live (owner := owner) capHints tailHints) nextStack := .live capMatched tailMatched
  have ready : ClosedExcept parameter code := by
    have declared := declaration.erase.source
    cases declared with
    | handler typed annotation declarations capabilities modes => cases typed with
      | handler scope clauses coverage unique =>
          obtain ⟨inputPort, outputPort, knownPort, bodyTyped⟩ := ScopedPorts.selected_clause_typed selected clauses
          exact ScopedPorts.typed_suffix_ready bodyTyped
  have resumeCheck := RecursiveClauses.fresh_resume_check savedAfter phaseSame
  have closingAfter := chosen.transport extension (List.Subset.refl _)
  have capabilities : ClausesUse policy handler.clauses := by
    cases declaration with | handler scope annotation clauses coverage unique declarations capabilities modes => exact capabilities
  have nextUse : LexicalUnwind.MachineUse policy (actions.insert owner code.requiredActions)
      (.eval ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩) :=
    LexicalUnwind.capture_machine_use cut
      (scoped_least_enclosing_actions (selected_clause_usage selected capabilities)).1 usage isValue freshAction
  have nextTickets : LexicalUnwind.MachineTicketAccess policy (actions.insert owner code.requiredActions)
      (.eval ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩) := by
    obtain ⟨nextDemand, nextPending, nextCode, nextPendingUse, nextBalance⟩ := nextUse
    obtain ⟨oldDemand, oldCode, oldVisible, stackAccess⟩ := ticketAccess
    refine ⟨nextDemand, nextCode, ?_, LexicalUnwind.capture_ticket_access cut stackAccess⟩
    cases nextCode with
    | idle scope used => exact List.nil_subset _
    | consume known used => simp [nextStack, activeTickets]
  have raw : RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩
      ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩ [.ticket owner] [] :=
    RawStep.capture requested operation parameter binder owner operand code caller whole capture tail handler
      (ScopedPorts.embedPort input.erase.port) cut selected closed ready
  have nextResources : LexicalUnwind.MachineAccess ambient
      (.eval ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩) :=
    LexicalUnwind.transition_access (.evaluate raw trivial) resourceAccess resourceChecks
  have oldModes : ∀ key body, (key, body) ∈ resumes → key.mode = .resume := by
    intro key body member
    cases recorded key body member
    rfl
  have annotatedModes : ∀ key body, (key, body) ∈ annotatedResumes → key.mode = .resume := by
    have transport : ∀ {original annotated : Store}, StoreAnnotation original annotated →
        (∀ key body, (key, body) ∈ original → key.mode = .resume) →
        ∀ key body, (key, body) ∈ annotated → key.mode = .resume := by
      intro original annotated annotation
      induction annotation with
      | nil => intro modes key body member; cases member
      | cons bodyAnnotation rest ih =>
          intro modes key body member
          rcases List.mem_cons.mp member with same | later
          · cases same
            exact modes _ _ List.mem_cons_self
          · exact ih (fun key body member => modes key body (List.mem_cons_of_mem _ member)) key body later
    exact transport resumeAnnotation oldModes
  have closingLookup : offered.dispose = true →
      RecursiveRequirements.lookup ⟨owner, .dispose⟩ nextStore = some ⟨suppliedDemand, suppliedRequirements⟩ := by
    intro disposes
    have held : ProtectionContexts.protectedMode capture.erase = false :=
      saved.realizes.held.symm.trans (guarded.disposing_unprotected selectedScope disposes)
    change RecursiveRequirements.lookup ⟨owner, .dispose⟩
      (((⟨owner, .resume⟩, ⟨capDemand, capAnnotated⟩) :: annotatedResumes) ++ (added ++ annotatedDisposals)) = _
    rw [RecursiveDisposalCapture.lookup_after_resumes]
    · simp only [addedOrigin, held, Bool.false_eq_true, if_false, List.singleton_append,
        RecursiveRequirements.lookup, if_true]
    · intro key body member
      rcases List.mem_cons.mp member with same | old
      · cases same; rfl
      · exact annotatedModes key body old
  refine ⟨capRow, tailRow, branchBound, closingDemand, closingRow, closingBalance, noClosing,
    added ++ disposals, nextStore, (by rw [addedOrigin]; split <;> rfl),
    (by simp only [nextStore, ← resumeLength, List.take_append_length, List.drop_append_length, ← addedOrigin]), closingLookup,
    nextStoreAnnotation, (by simp [nextStore, RecursiveRequirements.lookup]), nextResume.1, mode_row_store nextSource nextResume.2 (chosen.transport extension (List.Subset.refl _)) known nextStoreAnnotation,
    nextResume.2, ?_, chosen.transport extension (List.Subset.refl _), nextSource,
    ⟨_, nextMatching, nextPending, nextResumeLocal, nextDisposeLocal⟩, .sequence .original tailAnnotation, nextUse, nextTickets, nextResources, raw,
    owned, afterUnique, afterBalance, phaseSame, savedAfter, tailAfter, resumeCheck, ?_⟩
  · intro key body member
    exact (annotated key body member).transport extension (fun _ _ known => known) (List.Subset.refl _) (fun _ _ located => located)
  · have selectedBody := bodyFamily owner contract fresh rfl rfl rfl rfl rfl closingBalance
    have callerReady : ∀ other ∈ activeTickets tail, available (ownedTickets nextStack) other = .available := by
      intro other member
      apply if_pos
      rw [owned]
      apply List.mem_cons_of_mem
      rw [handler_cut_reconstructs cut, owned_tickets_append]
      exact List.mem_append_right _ (active_tickets_owned tail member)
    have exported : OwnerSource.exportAt (OwnerPhases.ofStack tables tail)
        (available (ownedTickets nextStack)) advertised = some requestRow :=
      (RecursivePlanAdmission.caller_export callerReady).trans offeredExport
    have payloadAfter := Values.extension (Values.change_allowed payload closed.1 residual) extension
    have interface : ClauseRowAdmission.Interface owner contract.erase offered.dispose nextStore
        (OwnerPhases.ofStack tables tail) (available (ownedTickets nextStack)) requestRow := by
      have resumed : RecursiveRequirements.Checked nextStore (.live owner contract.held :: OwnerPhases.ofStack tables tail)
          (available (ownedTickets nextStack)) (.invoke ⟨owner, .resume⟩ capDemand []) capRow := by
        simpa only [nextStack, OwnerPhases.ofStack, contract, Contract.erase, saved.realizes.held] using resumeCheck
      cases disposes : offered.dispose with
      | false => exact .of_resume resumed rfl (OwnerPhaseTransitions.capture_tail_fresh cut absent)
      | true =>
          obtain ⟨closeReq, addedSame, summary, closeRow, chosenRow, evaluated, closeBound⟩ := disposalData disposes
          have closingChecked : ∀ row, closingRow = some row →
              RecursiveRequirements.Checked nextStore (OwnerPhases.ofStack tables nextStack)
                (available (ownedTickets nextStack)) (.invoke ⟨owner, .dispose⟩ closingDemand []) row := by
            intro row same
            apply closing_invocation_from_record summary ?_ afterUnique ?_
            · change RecursiveRequirements.lookup ⟨owner, .dispose⟩
                (((⟨owner, .resume⟩, ⟨capDemand, capAnnotated⟩) :: annotatedResumes) ++ (added ++ annotatedDisposals)) = _
              rw [RecursiveDisposalCapture.lookup_after_resumes]
              · simp [addedSame, RecursiveRequirements.lookup]
              · intro key body member
                rcases List.mem_cons.mp member with same | old
                · cases same; rfl
                · exact annotatedModes key body old
            · rw [phaseSame]
              exact evaluated.trans (chosenRow.symm.trans same)
          refine ⟨resumed, ?_, fun _ => ⟨closeRow, chosenRow⟩, ?_, OwnerPhaseTransitions.capture_tail_fresh cut absent⟩
          · intro _ row same
            simpa only [nextStack, OwnerPhases.ofStack, contract, Contract.erase, saved.realizes.held] using closingChecked row same
          · intro _ row same
            have equal : closeRow = row := Option.some.inj (chosenRow.symm.trans same)
            exact equal ▸ closeBound.trans (List.subset_append_right _ _)
    refine ⟨interface, ?_⟩
    obtain ⟨clauseDemand, clauseReq, clauseAnnotated, normalRow, clauseRow,
      expression, clauseAnnotation, checked, covered, normalCheck, normalBound⟩ :=
      instantiate_mode_clause nextSource nextResume.2 closingAfter known nextStoreAnnotation
        selectedBody payloadAfter closed interface exported
    have actualChecked : RecursiveRequirements.Checked nextStore (OwnerPhases.ofStack tables nextStack)
        (available (ownedTickets nextStack)) clauseAnnotated clauseRow := by
      simpa only [nextStack, OwnerPhases.ofStack, contract, Contract.erase, saved.realizes.held] using checked
    have actualNormal : RecursiveRequirements.Checked nextStore (OwnerPhases.ofStack tables nextStack)
        (available (ownedTickets nextStack)) clauseReq normalRow := by
      simpa only [nextStack, OwnerPhases.ofStack, contract, Contract.erase, saved.realizes.held] using normalCheck
    obtain ⟨clauseBalance, _⟩ := complete_allocated_clause known selected capabilities payloadAfter closed
      expression actualNormal (by simp [available, nextStack, ownedTickets]) phaseSame closingBalance tailAfter
    have spentNext : spend (available (ownedTickets nextStack)) owner = available (ownedTickets whole) := phaseSame
    have spentOwner : spendAll (available (ownedTickets whole)) capDemand owner = .consumed :=
      RecursiveTransport.phases_spendAll_later owner consumed
    have pendingCheck : RecursiveRequirements.Checked nextStore []
        (spendAll (available (ownedTickets nextStack)) clauseDemand)
        (.sequence (.spent owner) tailAnnotated) tailRow := by
      rw [PhaseRechecking.spendAll_permutation clauseBalance]
      simpa only [spendAll, spentNext, List.nil_append, contract] using
        (RecursiveRequirements.Checked.sequence
          (RecursiveRequirements.Checked.spent (store := nextStore) (receiving := []) spentOwner) tailAfter)
    have combined : RecursiveRequirements.Checked nextStore [] (available (ownedTickets nextStack))
        (.sequence (clauseAnnotated.prepend (OwnerPhases.ofStack tables nextStack))
          (.sequence (.spent owner) tailAnnotated)) (clauseRow ++ tailRow) :=
      .sequence (RecursiveRequirements.checked_prepend_iff.mpr
        (by simpa only [List.append_nil] using actualChecked)) pendingCheck
    refine ⟨clauseDemand, clauseReq, clauseAnnotated, clauseRow, expression, clauseAnnotation,
      actualChecked, covered, clauseBalance,
      .sequence (clauseAnnotation.prepend _) (.sequence .original tailAnnotation), combined, ?_,
      (clauseBalance.append_right tailDemand).trans afterBalance⟩
    intro request member
    rcases List.mem_append.mp member with clauseMember | tailMember
    · rcases List.mem_append.mp (covered clauseMember) with advertisedMember | savedMember
      · exact List.mem_append_left _ advertisedMember
      · exact List.mem_append_right _ (branchBound (List.mem_append_left _ savedMember))
    · exact List.mem_append_right _ (branchBound (List.mem_append_right _ tailMember))

/-- Preserve the prior public statement by projecting the stronger allocation result. -/
theorem capture_mode_segments_with_closing_lookup
    (cut : HandlerCut requested whole capture tail handler)
    (current : Expression operations policy contracts world allowed caller Environment.empty
      (.perform (Instantiation.freezeEffect requested) operation operand) input currentDemand currentRequirements currentDependencies)
    (source : ModeSource operations policy contracts tables families actions world
      whole (.value input) output demand requirements wholeScope)
    {returnHints : SourceDependencyChecks.Lexical.ReturnHints wholeScope}
    (hinted : SourceDependencyChecks.Lexical.ReturnHints.Matches tables families returnHints whole)
    (pendingLocal : SourceDependencyChecks.Lexical.ReturnHints.Recursive.Pending outward actions
      (available (ownedTickets whole)) world returnHints .nil .ordinary output.mode)
    (usage : LexicalUnwind.MachineUse policy actions (.eval
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩))
    (ticketAccess : LexicalUnwind.MachineTicketAccess policy actions (.eval
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩))
    (resourceAccess : LexicalUnwind.MachineAccess ambient (.eval
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩))
    (operandSupport : Syntax.resourceDependencies operand.dependencies ⊆ operandBound)
    (operandBoundary : match SourceDependencyCapture.select requested operation wholeScope with
      | some (.handler _ receiving _ _) => operandBound ⊆ receiving.visibleResources ++ ambient
      | _ => False)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (isValue : operand.IsValue)
    (fresh : contracts owner = none) (freshAction : actions owner = none)
    (absent : owner ∉ ownedTickets whole)
    (bound : Bound annotations wholeScope) (freshAnnotation : annotations owner = none)
    (recorded : ∀ key body, (key, body) ∈ (resumes : Store) →
      ResumeAnnotated operations policy contracts tables families actions annotations world whole key body)
    (closing : UnwindRecords operations policy contracts tables world whole disposals)
    (closingRecorded : ∀ key body, (key, body) ∈ disposals →
      UnwindAnnotated operations policy contracts tables families annotations world whole key body)
    (unique : (ownedTickets whole).Nodup)
    (storeAnnotation : StoreAnnotation (resumes ++ disposals) annotatedStore)
    (annotation : RowAnnotation requirements annotatedRoot)
    (certificate : RecursiveRequirements.Checked annotatedStore []
      (available (ownedTickets whole)) annotatedRoot certificateRow)
    (currentCheck : RecursiveRequirements.Checked annotatedStore (OwnerPhases.ofStack tables whole)
      (available (ownedTickets whole)) currentRequirements requestRow)
    (currentLocal : SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local outward actions
      (available (ownedTickets whole)) world currentDependencies returnHints)
    {answer : Value} {residual : List Instance} {boundary : ModeValue}
    {capDemand tailDemand : List Nat} {capReq : Requirements capDemand} {tailReq : Requirements tailDemand}
    {capScope tailScope : Receiving}
    (declaration : SourceDependencyFrames.Frame operations policy contracts tables families world
      (.handler handler) answer answer [] (.request [] [])
      (.handler handler.effectInst (tables handler) (families handler)) (handler.effectInst :: residual) residual)
    (returns : boundary = .value answer ∨ boundary = .unwind)
    (saved : ModeSource operations policy contracts tables families actions world
      capture (.value input) boundary capDemand capReq capScope)
    (waiting : ModeSource operations policy contracts tables families actions world
      tail boundary output tailDemand tailReq tailScope)
    (scopeSame : wholeScope = capScope.append tailScope)
    (demandSame : demand = capDemand ++ tailDemand)
    (evaluation : ∀ store receiving phases, evaluate store receiving phases requirements =
      merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) phases capReq)
        (evaluate store receiving (spendAll phases capDemand) tailReq))
    {declaredArgument declaredInput : Value}
    {resumeEffects closeEffects : List Instance} {family : Nat → Dependencies}
    {offered : ClauseContract} {advertised : Footprint}
    (chosenOffer : lookup operation (tables handler) = some offered)
    (chosenRow : offered.row capScope.held = some advertised)
    (declaredOperation : operations handler.effectInst operation = some (declaredArgument, declaredInput))
    (familyKnown : (SourceDependencyCapture.lookupDependencies operation (families handler)).bind
      (SourceDependencyCapture.modeDependencies capScope.held) = some family)
    (bodyFamily : ∀ owner (contract : Contract), contracts owner = none →
      contract.input = declaredInput → contract.answer = answer →
      contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
      contract.held = capScope.held → contract.closeDemand.Perm contract.resumeDemand →
      Body operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
        (Environment.empty.extend parameter declaredArgument) code answer
        ⟨owner, contract.erase, offered.dispose, advertised⟩ (family owner)) :
      wholeScope = capScope.append tailScope ∧ demand = capDemand ++ tailDemand ∧
      (boundary = .value answer ∨ boundary = .unwind) ∧
      SourceDependencyFrames.Frame operations policy contracts tables families world (.handler handler) answer answer [] (.request [] [])
        (.handler handler.effectInst (tables handler) (families handler)) (handler.effectInst :: residual) residual ∧
      lookup operation (tables handler) = some offered ∧
      offered.row capScope.held = some advertised ∧
      (SourceDependencyCapture.lookupDependencies operation (families handler)).bind
        (SourceDependencyCapture.modeDependencies capScope.held) = some family ∧
      residualize (CallableProtectionFrames.contextOf tables tail) advertised = some requestRow ∧
      ∃ cutCertificate : Requirements (capDemand ++ tailDemand), ∃ cutRow,
      RowAnnotation (.sequence (capReq.prepend (OwnerPhases.ofStack tables tail)) tailReq) cutCertificate ∧
      RecursiveRequirements.Checked annotatedStore [] (available (ownedTickets whole)) cutCertificate cutRow ∧
      cutRow ⊆ certificateRow ∧
      RequirementPath annotatedRoot cutCertificate [] ∧
      RequirementPath (.sequence (capReq.prepend (OwnerPhases.ofStack tables tail)) tailReq) cutCertificate [] ∧
      ∀ (capAnnotated : Requirements capDemand) (tailAnnotated : Requirements tailDemand),
        RowAnnotation capReq capAnnotated → RowAnnotation tailReq tailAnnotated →
        RequirementPath (.sequence (capAnnotated.prepend (OwnerPhases.ofStack tables tail)) tailAnnotated) cutCertificate [] →
      ∀ suppliedDemand (suppliedRequirements : Requirements suppliedDemand),
        (ProtectionContexts.protectedMode capture.erase = false →
          UnwindSource operations policy contracts tables families world capture suppliedDemand suppliedRequirements capScope) →
        (offered.dispose = true → RequirementPath suppliedRequirements capAnnotated []) →
      ∃ capRow tailRow, capRow ++ tailRow ⊆ certificateRow ∧
      ∃ closingDemand closingRow, closingDemand.Perm capDemand ∧
      (offered.dispose = false → closingRow = none) ∧
      let contract : Contract := ⟨input, answer, capScope.held, capDemand, capRow,
        closingDemand, closingRow, resumeEffects, closeEffects⟩
      let nextStack := Stack.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail
      let nextResumes : Store := (⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: resumes
      let nextAnnotations := fun other => if other = owner then some capScope else annotations other
      ∃ nextDisposals nextStore : Store,
        nextDisposals = (if ProtectionContexts.protectedMode capture.erase then disposals else
          (⟨owner, .dispose⟩, ⟨suppliedDemand, suppliedRequirements⟩) :: disposals) ∧
        (offered.dispose = true → RecursiveRequirements.lookup ⟨owner, .dispose⟩ nextStore =
          some ⟨suppliedDemand, suppliedRequirements⟩) ∧
        StoreAnnotation (nextResumes ++ nextDisposals) nextStore ∧
        RecursiveRequirements.lookup ⟨owner, .resume⟩ nextStore = some ⟨capDemand, capAnnotated⟩ ∧
        Bound nextAnnotations (.live owner capScope tailScope) ∧
        ClauseRowAdmission.SourceStore operations.erase owner contract.erase nextStore ∧
        (∀ key body, (key, body) ∈ nextResumes →
          ResumeAnnotated operations policy (contracts.insert owner contract) tables families
            (actions.insert owner code.requiredActions) nextAnnotations world nextStack key body) ∧
        (∀ key body, (key, body) ∈ nextDisposals →
          UnwindAnnotated operations policy (contracts.insert owner contract) tables families
            nextAnnotations world nextStack key body) ∧
        UnwindRecords operations policy (contracts.insert owner contract) tables world nextStack nextDisposals ∧
        ModeSource operations policy (contracts.insert owner contract) tables families
          (actions.insert owner code.requiredActions) world nextStack (.value answer) output tailDemand
          (.sequence (.spent owner) tailReq) (.live owner capScope tailScope) ∧
        (∃ nextHints : SourceDependencyChecks.Lexical.ReturnHints (.live owner capScope tailScope),
          SourceDependencyChecks.Lexical.ReturnHints.Matches tables families nextHints nextStack ∧
          SourceDependencyChecks.Lexical.ReturnHints.Recursive.Pending outward (actions.insert owner code.requiredActions)
            (available (ownedTickets nextStack)) world nextHints .nil .ordinary output.mode ∧
          (code.requiredActions.resume = true →
            SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local outward (actions.insert owner code.requiredActions)
              (available (ownedTickets nextStack)) world (.invoke ⟨owner, .resume⟩) nextHints) ∧
          (code.requiredActions.dispose = true →
            SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local outward (actions.insert owner code.requiredActions)
              (available (ownedTickets nextStack)) world (.invoke ⟨owner, .dispose⟩) nextHints)) ∧
        RowAnnotation (.sequence (.spent owner) tailReq) (.sequence (.spent owner) tailAnnotated) ∧
        LexicalUnwind.MachineUse policy (actions.insert owner code.requiredActions)
          (.eval ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩) ∧
        LexicalUnwind.MachineTicketAccess policy (actions.insert owner code.requiredActions)
          (.eval ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩) ∧
        LexicalUnwind.MachineAccess ambient
          (.eval ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩) ∧
        RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩
          ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩ [.ticket owner] [] ∧
        ownedTickets nextStack = owner :: ownedTickets whole ∧
        (ownedTickets nextStack).Nodup ∧
        ((owner :: capDemand) ++ tailDemand).Perm (ownedTickets nextStack) ∧
        spend (available (ownedTickets nextStack)) owner = available (ownedTickets whole) ∧
        RecursiveRequirements.Checked nextStore (OwnerPhases.ofStack tables tail)
          (available (ownedTickets whole)) capAnnotated capRow ∧
        RecursiveRequirements.Checked nextStore []
          (spendAll (available (ownedTickets whole)) capDemand) tailAnnotated tailRow ∧
        RecursiveRequirements.Checked nextStore (OwnerPhases.ofStack tables nextStack)
          (available (ownedTickets nextStack)) (.invoke ⟨owner, .resume⟩ capDemand []) capRow ∧
        ClauseRowAdmission.Interface owner contract.erase offered.dispose nextStore
          (OwnerPhases.ofStack tables tail) (available (ownedTickets nextStack)) requestRow ∧
          ∃ clauseDemand, ∃ clauseReq clauseAnnotated : Requirements clauseDemand, ∃ clauseRow,
            Expression operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
              Environment.empty (code.subst parameter operand) answer clauseDemand clauseReq (family owner) ∧
            RowAnnotation clauseReq clauseAnnotated ∧
            RecursiveRequirements.Checked nextStore (OwnerPhases.ofStack tables nextStack)
              (available (ownedTickets nextStack)) clauseAnnotated clauseRow ∧
            clauseRow ⊆ requestRow ++ capRow ∧
            clauseDemand.Perm (owner :: capDemand) ∧
            RowAnnotation
              (.sequence (clauseReq.prepend (OwnerPhases.ofStack tables nextStack)) (.sequence (.spent owner) tailReq))
              (.sequence (clauseAnnotated.prepend (OwnerPhases.ofStack tables nextStack)) (.sequence (.spent owner) tailAnnotated)) ∧
            RecursiveRequirements.Checked nextStore [] (available (ownedTickets nextStack))
              (.sequence (clauseAnnotated.prepend (OwnerPhases.ofStack tables nextStack)) (.sequence (.spent owner) tailAnnotated))
              (clauseRow ++ tailRow) ∧
            clauseRow ++ tailRow ⊆ requestRow ++ certificateRow ∧
            (clauseDemand ++ tailDemand).Perm (ownedTickets nextStack) := by
  obtain ⟨sameScope, sameDemand, sameBoundary, sameDeclaration, sameOffer, sameRow,
    sameFamily, exportedRow, unprotected, cutCertificate, cutRow, cutAnnotation, cutCheck, cutBound,
    originalPath, splitPath, finish⟩ :=
    capture_mode_segments_with_closing_store cut current source hinted pendingLocal usage ticketAccess resourceAccess
      operandSupport operandBoundary selected isValue fresh freshAction absent bound freshAnnotation
      recorded closing closingRecorded unique storeAnnotation annotation certificate currentCheck currentLocal
      declaration returns saved waiting scopeSame demandSame evaluation chosenOffer chosenRow
      declaredOperation familyKnown bodyFamily
  refine ⟨sameScope, sameDemand, sameBoundary, sameDeclaration, sameOffer, sameRow,
    sameFamily, exportedRow, cutCertificate, cutRow, cutAnnotation, cutCheck, cutBound,
    originalPath, splitPath, ?_⟩
  intro capAnnotated tailAnnotated capAnnotation tailAnnotation splitCovered suppliedDemand suppliedRequirements suppliedSource suppliedPath
  obtain ⟨selectedRow, selectedCheck, selectedBound⟩ := splitCovered.checked cutCheck
  have splitCheck : ∃ selectedRow, RecursiveRequirements.Checked annotatedStore [] (available (ownedTickets whole))
      (.sequence (capAnnotated.prepend (OwnerPhases.ofStack tables tail)) tailAnnotated) selectedRow ∧ selectedRow ⊆ certificateRow :=
    ⟨selectedRow, by simpa only [spendAll] using selectedCheck, selectedBound.trans cutBound⟩
  obtain ⟨capRow, tailRow, within, closingDemand, closingRow, balanced, noClosing,
    nextDisposals, nextStore, origin, allocatedStore, result⟩ :=
    finish capAnnotated tailAnnotated capAnnotation tailAnnotation splitCheck
      suppliedDemand suppliedRequirements suppliedSource suppliedPath
  exact ⟨capRow, tailRow, within, closingDemand, closingRow, balanced, noClosing,
    nextDisposals, nextStore, origin, result⟩

/-- Preserve the original allocator interface by forgetting the additional
exact disposal lookup. -/
theorem capture_mode_segments_with_closing
    (cut : HandlerCut requested whole capture tail handler)
    (current : Expression operations policy contracts world allowed caller Environment.empty
      (.perform (Instantiation.freezeEffect requested) operation operand) input currentDemand currentRequirements currentDependencies)
    (source : ModeSource operations policy contracts tables families actions world
      whole (.value input) output demand requirements wholeScope)
    {returnHints : SourceDependencyChecks.Lexical.ReturnHints wholeScope}
    (hinted : SourceDependencyChecks.Lexical.ReturnHints.Matches tables families returnHints whole)
    (pendingLocal : SourceDependencyChecks.Lexical.ReturnHints.Recursive.Pending outward actions
      (available (ownedTickets whole)) world returnHints .nil .ordinary output.mode)
    (usage : LexicalUnwind.MachineUse policy actions (.eval
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩))
    (ticketAccess : LexicalUnwind.MachineTicketAccess policy actions (.eval
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩))
    (resourceAccess : LexicalUnwind.MachineAccess ambient (.eval
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩))
    (operandSupport : Syntax.resourceDependencies operand.dependencies ⊆ operandBound)
    (operandBoundary : match SourceDependencyCapture.select requested operation wholeScope with
      | some (.handler _ receiving _ _) => operandBound ⊆ receiving.visibleResources ++ ambient
      | _ => False)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (isValue : operand.IsValue)
    (fresh : contracts owner = none) (freshAction : actions owner = none)
    (absent : owner ∉ ownedTickets whole)
    (bound : Bound annotations wholeScope) (freshAnnotation : annotations owner = none)
    (recorded : ∀ key body, (key, body) ∈ (resumes : Store) →
      ResumeAnnotated operations policy contracts tables families actions annotations world whole key body)
    (closing : UnwindRecords operations policy contracts tables world whole disposals)
    (closingRecorded : ∀ key body, (key, body) ∈ disposals →
      UnwindAnnotated operations policy contracts tables families annotations world whole key body)
    (unique : (ownedTickets whole).Nodup)
    (storeAnnotation : StoreAnnotation (resumes ++ disposals) annotatedStore)
    (annotation : RowAnnotation requirements annotatedRoot)
    (certificate : RecursiveRequirements.Checked annotatedStore []
      (available (ownedTickets whole)) annotatedRoot certificateRow)
    (currentCheck : RecursiveRequirements.Checked annotatedStore (OwnerPhases.ofStack tables whole)
      (available (ownedTickets whole)) currentRequirements requestRow)
    (currentLocal : SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local outward actions
      (available (ownedTickets whole)) world currentDependencies returnHints)
    {answer : Value} {residual : List Instance} {boundary : ModeValue}
    {capDemand tailDemand : List Nat} {capReq : Requirements capDemand} {tailReq : Requirements tailDemand}
    {capScope tailScope : Receiving}
    (declaration : SourceDependencyFrames.Frame operations policy contracts tables families world
      (.handler handler) answer answer [] (.request [] [])
      (.handler handler.effectInst (tables handler) (families handler)) (handler.effectInst :: residual) residual)
    (returns : boundary = .value answer ∨ boundary = .unwind)
    (saved : ModeSource operations policy contracts tables families actions world
      capture (.value input) boundary capDemand capReq capScope)
    (waiting : ModeSource operations policy contracts tables families actions world
      tail boundary output tailDemand tailReq tailScope)
    (scopeSame : wholeScope = capScope.append tailScope)
    (demandSame : demand = capDemand ++ tailDemand)
    (evaluation : ∀ store receiving phases, evaluate store receiving phases requirements =
      merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) phases capReq)
        (evaluate store receiving (spendAll phases capDemand) tailReq))
    {declaredArgument declaredInput : Value}
    {resumeEffects closeEffects : List Instance} {family : Nat → Dependencies}
    {offered : ClauseContract} {advertised : Footprint}
    (chosenOffer : lookup operation (tables handler) = some offered)
    (chosenRow : offered.row capScope.held = some advertised)
    (declaredOperation : operations handler.effectInst operation = some (declaredArgument, declaredInput))
    (familyKnown : (SourceDependencyCapture.lookupDependencies operation (families handler)).bind
      (SourceDependencyCapture.modeDependencies capScope.held) = some family)
    (bodyFamily : ∀ owner (contract : Contract), contracts owner = none →
      contract.input = declaredInput → contract.answer = answer →
      contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
      contract.held = capScope.held → contract.closeDemand.Perm contract.resumeDemand →
      Body operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
        (Environment.empty.extend parameter declaredArgument) code answer
        ⟨owner, contract.erase, offered.dispose, advertised⟩ (family owner)) :
      wholeScope = capScope.append tailScope ∧ demand = capDemand ++ tailDemand ∧
      (boundary = .value answer ∨ boundary = .unwind) ∧
      SourceDependencyFrames.Frame operations policy contracts tables families world (.handler handler) answer answer [] (.request [] [])
        (.handler handler.effectInst (tables handler) (families handler)) (handler.effectInst :: residual) residual ∧
      lookup operation (tables handler) = some offered ∧
      offered.row capScope.held = some advertised ∧
      (SourceDependencyCapture.lookupDependencies operation (families handler)).bind
        (SourceDependencyCapture.modeDependencies capScope.held) = some family ∧
      residualize (CallableProtectionFrames.contextOf tables tail) advertised = some requestRow ∧
      ∃ cutCertificate : Requirements (capDemand ++ tailDemand), ∃ cutRow,
      RowAnnotation (.sequence (capReq.prepend (OwnerPhases.ofStack tables tail)) tailReq) cutCertificate ∧
      RecursiveRequirements.Checked annotatedStore [] (available (ownedTickets whole)) cutCertificate cutRow ∧
      cutRow ⊆ certificateRow ∧
      RequirementPath annotatedRoot cutCertificate [] ∧
      RequirementPath (.sequence (capReq.prepend (OwnerPhases.ofStack tables tail)) tailReq) cutCertificate [] ∧
      ∀ (capAnnotated : Requirements capDemand) (tailAnnotated : Requirements tailDemand),
        RowAnnotation capReq capAnnotated → RowAnnotation tailReq tailAnnotated →
        RequirementPath (.sequence (capAnnotated.prepend (OwnerPhases.ofStack tables tail)) tailAnnotated) cutCertificate [] →
      ∀ suppliedDemand (suppliedRequirements : Requirements suppliedDemand),
        (ProtectionContexts.protectedMode capture.erase = false →
          UnwindSource operations policy contracts tables families world capture suppliedDemand suppliedRequirements capScope) →
        (offered.dispose = true → RequirementPath suppliedRequirements capAnnotated []) →
      ∃ capRow tailRow, capRow ++ tailRow ⊆ certificateRow ∧
      ∃ closingDemand closingRow, closingDemand.Perm capDemand ∧
      (offered.dispose = false → closingRow = none) ∧
      let contract : Contract := ⟨input, answer, capScope.held, capDemand, capRow,
        closingDemand, closingRow, resumeEffects, closeEffects⟩
      let nextStack := Stack.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail
      let nextResumes : Store := (⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: resumes
      let nextAnnotations := fun other => if other = owner then some capScope else annotations other
      ∃ nextDisposals nextStore : Store,
        nextDisposals = (if ProtectionContexts.protectedMode capture.erase then disposals else
          (⟨owner, .dispose⟩, ⟨suppliedDemand, suppliedRequirements⟩) :: disposals) ∧
        StoreAnnotation (nextResumes ++ nextDisposals) nextStore ∧
        RecursiveRequirements.lookup ⟨owner, .resume⟩ nextStore = some ⟨capDemand, capAnnotated⟩ ∧
        Bound nextAnnotations (.live owner capScope tailScope) ∧
        ClauseRowAdmission.SourceStore operations.erase owner contract.erase nextStore ∧
        (∀ key body, (key, body) ∈ nextResumes →
          ResumeAnnotated operations policy (contracts.insert owner contract) tables families
            (actions.insert owner code.requiredActions) nextAnnotations world nextStack key body) ∧
        (∀ key body, (key, body) ∈ nextDisposals →
          UnwindAnnotated operations policy (contracts.insert owner contract) tables families
            nextAnnotations world nextStack key body) ∧
        UnwindRecords operations policy (contracts.insert owner contract) tables world nextStack nextDisposals ∧
        ModeSource operations policy (contracts.insert owner contract) tables families
          (actions.insert owner code.requiredActions) world nextStack (.value answer) output tailDemand
          (.sequence (.spent owner) tailReq) (.live owner capScope tailScope) ∧
        (∃ nextHints : SourceDependencyChecks.Lexical.ReturnHints (.live owner capScope tailScope),
          SourceDependencyChecks.Lexical.ReturnHints.Matches tables families nextHints nextStack ∧
          SourceDependencyChecks.Lexical.ReturnHints.Recursive.Pending outward (actions.insert owner code.requiredActions)
            (available (ownedTickets nextStack)) world nextHints .nil .ordinary output.mode ∧
          (code.requiredActions.resume = true →
            SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local outward (actions.insert owner code.requiredActions)
              (available (ownedTickets nextStack)) world (.invoke ⟨owner, .resume⟩) nextHints) ∧
          (code.requiredActions.dispose = true →
            SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local outward (actions.insert owner code.requiredActions)
              (available (ownedTickets nextStack)) world (.invoke ⟨owner, .dispose⟩) nextHints)) ∧
        RowAnnotation (.sequence (.spent owner) tailReq) (.sequence (.spent owner) tailAnnotated) ∧
        LexicalUnwind.MachineUse policy (actions.insert owner code.requiredActions)
          (.eval ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩) ∧
        LexicalUnwind.MachineTicketAccess policy (actions.insert owner code.requiredActions)
          (.eval ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩) ∧
        LexicalUnwind.MachineAccess ambient
          (.eval ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩) ∧
        RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩
          ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩ [.ticket owner] [] ∧
        ownedTickets nextStack = owner :: ownedTickets whole ∧
        (ownedTickets nextStack).Nodup ∧
        ((owner :: capDemand) ++ tailDemand).Perm (ownedTickets nextStack) ∧
        spend (available (ownedTickets nextStack)) owner = available (ownedTickets whole) ∧
        RecursiveRequirements.Checked nextStore (OwnerPhases.ofStack tables tail)
          (available (ownedTickets whole)) capAnnotated capRow ∧
        RecursiveRequirements.Checked nextStore []
          (spendAll (available (ownedTickets whole)) capDemand) tailAnnotated tailRow ∧
        RecursiveRequirements.Checked nextStore (OwnerPhases.ofStack tables nextStack)
          (available (ownedTickets nextStack)) (.invoke ⟨owner, .resume⟩ capDemand []) capRow ∧
        ClauseRowAdmission.Interface owner contract.erase offered.dispose nextStore
          (OwnerPhases.ofStack tables tail) (available (ownedTickets nextStack)) requestRow ∧
          ∃ clauseDemand, ∃ clauseReq clauseAnnotated : Requirements clauseDemand, ∃ clauseRow,
            Expression operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
              Environment.empty (code.subst parameter operand) answer clauseDemand clauseReq (family owner) ∧
            RowAnnotation clauseReq clauseAnnotated ∧
            RecursiveRequirements.Checked nextStore (OwnerPhases.ofStack tables nextStack)
              (available (ownedTickets nextStack)) clauseAnnotated clauseRow ∧
            clauseRow ⊆ requestRow ++ capRow ∧
            clauseDemand.Perm (owner :: capDemand) ∧
            RowAnnotation
              (.sequence (clauseReq.prepend (OwnerPhases.ofStack tables nextStack)) (.sequence (.spent owner) tailReq))
              (.sequence (clauseAnnotated.prepend (OwnerPhases.ofStack tables nextStack)) (.sequence (.spent owner) tailAnnotated)) ∧
            RecursiveRequirements.Checked nextStore [] (available (ownedTickets nextStack))
              (.sequence (clauseAnnotated.prepend (OwnerPhases.ofStack tables nextStack)) (.sequence (.spent owner) tailAnnotated))
              (clauseRow ++ tailRow) ∧
            clauseRow ++ tailRow ⊆ requestRow ++ certificateRow ∧
            (clauseDemand ++ tailDemand).Perm (ownedTickets nextStack) := by
  obtain ⟨sameScope, sameDemand, sameBoundary, sameDeclaration, sameOffer, sameRow,
    sameFamily, exportedRow, cutCertificate, cutRow, cutAnnotation, cutCheck, cutBound,
    originalPath, splitPath, finish⟩ :=
    capture_mode_segments_with_closing_lookup cut current source hinted pendingLocal usage ticketAccess resourceAccess
      operandSupport operandBoundary selected isValue fresh freshAction absent bound freshAnnotation
      recorded closing closingRecorded unique storeAnnotation annotation certificate currentCheck currentLocal
      declaration returns saved waiting scopeSame demandSame evaluation chosenOffer chosenRow
      declaredOperation familyKnown bodyFamily
  refine ⟨sameScope, sameDemand, sameBoundary, sameDeclaration, sameOffer, sameRow,
    sameFamily, exportedRow, cutCertificate, cutRow, cutAnnotation, cutCheck, cutBound,
    originalPath, splitPath, ?_⟩
  intro capAnnotated tailAnnotated capAnnotation tailAnnotation splitCovered suppliedDemand suppliedRequirements suppliedSource suppliedPath
  obtain ⟨capRow, tailRow, within, closingDemand, closingRow, balanced, noClosing,
    nextDisposals, nextStore, origin, exactLookup, result⟩ :=
    finish capAnnotated tailAnnotated capAnnotation tailAnnotation splitCovered
      suppliedDemand suppliedRequirements suppliedSource suppliedPath
  exact ⟨capRow, tailRow, within, closingDemand, closingRow, balanced, noClosing,
    nextDisposals, nextStore, origin, result⟩

/-- Preserve the previous existential cleanup interface while delegating to
the allocator that records its exact supplied cleanup body. -/
theorem capture_mode_segments_at_body
    (cut : HandlerCut requested whole capture tail handler)
    (current : Expression operations policy contracts world allowed caller Environment.empty
      (.perform (Instantiation.freezeEffect requested) operation operand) input currentDemand currentRequirements currentDependencies)
    (source : ModeSource operations policy contracts tables families actions world
      whole (.value input) output demand requirements wholeScope)
    {returnHints : SourceDependencyChecks.Lexical.ReturnHints wholeScope}
    (hinted : SourceDependencyChecks.Lexical.ReturnHints.Matches tables families returnHints whole)
    (pendingLocal : SourceDependencyChecks.Lexical.ReturnHints.Recursive.Pending outward actions
      (available (ownedTickets whole)) world returnHints .nil .ordinary output.mode)
    (usage : LexicalUnwind.MachineUse policy actions (.eval
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩))
    (ticketAccess : LexicalUnwind.MachineTicketAccess policy actions (.eval
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩))
    (resourceAccess : LexicalUnwind.MachineAccess ambient (.eval
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩))
    (operandSupport : Syntax.resourceDependencies operand.dependencies ⊆ operandBound)
    (operandBoundary : match SourceDependencyCapture.select requested operation wholeScope with
      | some (.handler _ receiving _ _) => operandBound ⊆ receiving.visibleResources ++ ambient
      | _ => False)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (isValue : operand.IsValue)
    (fresh : contracts owner = none) (freshAction : actions owner = none)
    (absent : owner ∉ ownedTickets whole)
    (bound : Bound annotations wholeScope) (freshAnnotation : annotations owner = none)
    (recorded : ∀ key body, (key, body) ∈ (resumes : Store) →
      ResumeAnnotated operations policy contracts tables families actions annotations world whole key body)
    (closing : UnwindRecords operations policy contracts tables world whole disposals)
    (closingRecorded : ∀ key body, (key, body) ∈ disposals →
      UnwindAnnotated operations policy contracts tables families annotations world whole key body)
    (unique : (ownedTickets whole).Nodup)
    (storeAnnotation : StoreAnnotation (resumes ++ disposals) annotatedStore)
    (annotation : RowAnnotation requirements annotatedRoot)
    (certificate : RecursiveRequirements.Checked annotatedStore []
      (available (ownedTickets whole)) annotatedRoot certificateRow)
    (currentCheck : RecursiveRequirements.Checked annotatedStore (OwnerPhases.ofStack tables whole)
      (available (ownedTickets whole)) currentRequirements requestRow)
    (currentLocal : SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local outward actions
      (available (ownedTickets whole)) world currentDependencies returnHints)
    {answer : Value} {residual : List Instance} {boundary : ModeValue}
    {capDemand tailDemand : List Nat} {capReq : Requirements capDemand} {tailReq : Requirements tailDemand}
    {capScope tailScope : Receiving}
    (declaration : SourceDependencyFrames.Frame operations policy contracts tables families world
      (.handler handler) answer answer [] (.request [] [])
      (.handler handler.effectInst (tables handler) (families handler)) (handler.effectInst :: residual) residual)
    (returns : boundary = .value answer ∨ boundary = .unwind)
    (saved : ModeSource operations policy contracts tables families actions world
      capture (.value input) boundary capDemand capReq capScope)
    (waiting : ModeSource operations policy contracts tables families actions world
      tail boundary output tailDemand tailReq tailScope)
    (scopeSame : wholeScope = capScope.append tailScope)
    (demandSame : demand = capDemand ++ tailDemand)
    (evaluation : ∀ store receiving phases, evaluate store receiving phases requirements =
      merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) phases capReq)
        (evaluate store receiving (spendAll phases capDemand) tailReq))
    {declaredArgument declaredInput : Value}
    {resumeEffects closeEffects : List Instance} {family : Nat → Dependencies}
    {offered : ClauseContract} {advertised : Footprint}
    (chosenOffer : lookup operation (tables handler) = some offered)
    (chosenRow : offered.row capScope.held = some advertised)
    (declaredOperation : operations handler.effectInst operation = some (declaredArgument, declaredInput))
    (familyKnown : (SourceDependencyCapture.lookupDependencies operation (families handler)).bind
      (SourceDependencyCapture.modeDependencies capScope.held) = some family)
    (bodyFamily : ∀ owner (contract : Contract), contracts owner = none →
      contract.input = declaredInput → contract.answer = answer →
      contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
      contract.held = capScope.held → contract.closeDemand.Perm contract.resumeDemand →
      Body operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
        (Environment.empty.extend parameter declaredArgument) code answer
        ⟨owner, contract.erase, offered.dispose, advertised⟩ (family owner)) :
      wholeScope = capScope.append tailScope ∧ demand = capDemand ++ tailDemand ∧
      (boundary = .value answer ∨ boundary = .unwind) ∧
      SourceDependencyFrames.Frame operations policy contracts tables families world (.handler handler) answer answer [] (.request [] [])
        (.handler handler.effectInst (tables handler) (families handler)) (handler.effectInst :: residual) residual ∧
      lookup operation (tables handler) = some offered ∧
      offered.row capScope.held = some advertised ∧
      (SourceDependencyCapture.lookupDependencies operation (families handler)).bind
        (SourceDependencyCapture.modeDependencies capScope.held) = some family ∧
      residualize (CallableProtectionFrames.contextOf tables tail) advertised = some requestRow ∧
      ∃ cutCertificate : Requirements (capDemand ++ tailDemand), ∃ cutRow,
      RowAnnotation (.sequence (capReq.prepend (OwnerPhases.ofStack tables tail)) tailReq) cutCertificate ∧
      RecursiveRequirements.Checked annotatedStore [] (available (ownedTickets whole)) cutCertificate cutRow ∧
      cutRow ⊆ certificateRow ∧
      RequirementPath annotatedRoot cutCertificate [] ∧
      RequirementPath (.sequence (capReq.prepend (OwnerPhases.ofStack tables tail)) tailReq) cutCertificate [] ∧
      ∀ (capAnnotated : Requirements capDemand) (tailAnnotated : Requirements tailDemand),
        RowAnnotation capReq capAnnotated → RowAnnotation tailReq tailAnnotated →
        RequirementPath (.sequence (capAnnotated.prepend (OwnerPhases.ofStack tables tail)) tailAnnotated) cutCertificate [] →
        (offered.dispose = true → ∃ closingDemand, ∃ closingRequirements : Requirements closingDemand,
          UnwindSource operations policy contracts tables families world capture closingDemand closingRequirements capScope ∧
          RequirementPath closingRequirements capAnnotated []) →
      ∃ capRow tailRow, capRow ++ tailRow ⊆ certificateRow ∧
      ∃ closingDemand closingRow, closingDemand.Perm capDemand ∧
      (offered.dispose = false → closingRow = none) ∧
      let contract : Contract := ⟨input, answer, capScope.held, capDemand, capRow,
        closingDemand, closingRow, resumeEffects, closeEffects⟩
      let nextStack := Stack.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail
      let nextResumes : Store := (⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: resumes
      let nextAnnotations := fun other => if other = owner then some capScope else annotations other
      ∃ nextDisposals nextStore : Store,
        StoreAnnotation (nextResumes ++ nextDisposals) nextStore ∧
        RecursiveRequirements.lookup ⟨owner, .resume⟩ nextStore = some ⟨capDemand, capAnnotated⟩ ∧
        Bound nextAnnotations (.live owner capScope tailScope) ∧
        ClauseRowAdmission.SourceStore operations.erase owner contract.erase nextStore ∧
        (∀ key body, (key, body) ∈ nextResumes →
          ResumeAnnotated operations policy (contracts.insert owner contract) tables families
            (actions.insert owner code.requiredActions) nextAnnotations world nextStack key body) ∧
        (∀ key body, (key, body) ∈ nextDisposals →
          UnwindAnnotated operations policy (contracts.insert owner contract) tables families
            nextAnnotations world nextStack key body) ∧
        UnwindRecords operations policy (contracts.insert owner contract) tables world nextStack nextDisposals ∧
        ModeSource operations policy (contracts.insert owner contract) tables families
          (actions.insert owner code.requiredActions) world nextStack (.value answer) output tailDemand
          (.sequence (.spent owner) tailReq) (.live owner capScope tailScope) ∧
        (∃ nextHints : SourceDependencyChecks.Lexical.ReturnHints (.live owner capScope tailScope),
          SourceDependencyChecks.Lexical.ReturnHints.Matches tables families nextHints nextStack ∧
          SourceDependencyChecks.Lexical.ReturnHints.Recursive.Pending outward (actions.insert owner code.requiredActions)
            (available (ownedTickets nextStack)) world nextHints .nil .ordinary output.mode ∧
          (code.requiredActions.resume = true →
            SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local outward (actions.insert owner code.requiredActions)
              (available (ownedTickets nextStack)) world (.invoke ⟨owner, .resume⟩) nextHints) ∧
          (code.requiredActions.dispose = true →
            SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local outward (actions.insert owner code.requiredActions)
              (available (ownedTickets nextStack)) world (.invoke ⟨owner, .dispose⟩) nextHints)) ∧
        RowAnnotation (.sequence (.spent owner) tailReq) (.sequence (.spent owner) tailAnnotated) ∧
        LexicalUnwind.MachineUse policy (actions.insert owner code.requiredActions)
          (.eval ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩) ∧
        LexicalUnwind.MachineTicketAccess policy (actions.insert owner code.requiredActions)
          (.eval ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩) ∧
        LexicalUnwind.MachineAccess ambient
          (.eval ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩) ∧
        RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩
          ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩ [.ticket owner] [] ∧
        ownedTickets nextStack = owner :: ownedTickets whole ∧
        (ownedTickets nextStack).Nodup ∧
        ((owner :: capDemand) ++ tailDemand).Perm (ownedTickets nextStack) ∧
        spend (available (ownedTickets nextStack)) owner = available (ownedTickets whole) ∧
        RecursiveRequirements.Checked nextStore (OwnerPhases.ofStack tables tail)
          (available (ownedTickets whole)) capAnnotated capRow ∧
        RecursiveRequirements.Checked nextStore []
          (spendAll (available (ownedTickets whole)) capDemand) tailAnnotated tailRow ∧
        RecursiveRequirements.Checked nextStore (OwnerPhases.ofStack tables nextStack)
          (available (ownedTickets nextStack)) (.invoke ⟨owner, .resume⟩ capDemand []) capRow ∧
        ClauseRowAdmission.Interface owner contract.erase offered.dispose nextStore
          (OwnerPhases.ofStack tables tail) (available (ownedTickets nextStack)) requestRow ∧
          ∃ clauseDemand, ∃ clauseReq clauseAnnotated : Requirements clauseDemand, ∃ clauseRow,
            Expression operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
              Environment.empty (code.subst parameter operand) answer clauseDemand clauseReq (family owner) ∧
            RowAnnotation clauseReq clauseAnnotated ∧
            RecursiveRequirements.Checked nextStore (OwnerPhases.ofStack tables nextStack)
              (available (ownedTickets nextStack)) clauseAnnotated clauseRow ∧
            clauseRow ⊆ requestRow ++ capRow ∧
            clauseDemand.Perm (owner :: capDemand) ∧
            RowAnnotation
              (.sequence (clauseReq.prepend (OwnerPhases.ofStack tables nextStack)) (.sequence (.spent owner) tailReq))
              (.sequence (clauseAnnotated.prepend (OwnerPhases.ofStack tables nextStack)) (.sequence (.spent owner) tailAnnotated)) ∧
            RecursiveRequirements.Checked nextStore [] (available (ownedTickets nextStack))
              (.sequence (clauseAnnotated.prepend (OwnerPhases.ofStack tables nextStack)) (.sequence (.spent owner) tailAnnotated))
              (clauseRow ++ tailRow) ∧
            clauseRow ++ tailRow ⊆ requestRow ++ certificateRow ∧
            (clauseDemand ++ tailDemand).Perm (ownedTickets nextStack) := by
  obtain ⟨sameScope, sameDemand, sameBoundary, sameDeclaration, sameOffer, sameRow,
    sameFamily, exportedRow, cutCertificate, cutRow, cutAnnotation, cutCheck, cutBound,
    originalPath, splitPath, finish⟩ :=
    capture_mode_segments_with_closing cut current source hinted pendingLocal usage ticketAccess resourceAccess
      operandSupport operandBoundary selected isValue fresh freshAction absent bound freshAnnotation
      recorded closing closingRecorded unique storeAnnotation annotation certificate currentCheck currentLocal
      declaration returns saved waiting scopeSame demandSame evaluation chosenOffer chosenRow
      declaredOperation familyKnown bodyFamily
  refine ⟨sameScope, sameDemand, sameBoundary, sameDeclaration, sameOffer, sameRow,
    sameFamily, exportedRow, cutCertificate, cutRow, cutAnnotation, cutCheck, cutBound,
    originalPath, splitPath, ?_⟩
  intro capAnnotated tailAnnotated capAnnotation tailAnnotation splitCovered cleanupCovered
  obtain ⟨suppliedDemand, suppliedRequirements, suppliedSource, suppliedPath⟩ :
      ∃ suppliedDemand, ∃ suppliedRequirements : Requirements suppliedDemand,
        (ProtectionContexts.protectedMode capture.erase = false →
          UnwindSource operations policy contracts tables families world capture suppliedDemand suppliedRequirements capScope) ∧
        (offered.dispose = true → RequirementPath suppliedRequirements capAnnotated []) := by
    cases disposes : offered.dispose with
    | true =>
      obtain ⟨closeDemand, closeRequirements, closeSource, closePath⟩ := cleanupCovered disposes
      exact ⟨closeDemand, closeRequirements, fun _ => closeSource, fun _ => closePath⟩
    | false =>
      cases held : ProtectionContexts.protectedMode capture.erase with
      | false =>
        obtain ⟨closeDemand, closeRequirements, closeSource⟩ :=
          saved.unwind_source (LexicalUnwind.unprotected_unwind_prefix held)
        exact ⟨closeDemand, closeRequirements, fun _ => closeSource, by intro impossible; cases impossible⟩
      | true => exact ⟨[], .request [] [], (by intro impossible; cases impossible), (by intro impossible; cases impossible)⟩
  obtain ⟨capRow, tailRow, within, closingDemand, closingRow, balanced, noClosing,
    nextDisposals, nextStore, origin, result⟩ :=
    finish capAnnotated tailAnnotated capAnnotation tailAnnotation splitCovered
      suppliedDemand suppliedRequirements suppliedSource suppliedPath
  exact ⟨capRow, tailRow, within, closingDemand, closingRow, balanced, noClosing,
    nextDisposals, nextStore, result⟩

theorem capture_mode_segments_at_cut
    (cut : HandlerCut requested whole capture tail handler)
    (current : Expression operations policy contracts world allowed caller Environment.empty
      (.perform (Instantiation.freezeEffect requested) operation operand) input currentDemand currentRequirements currentDependencies)
    (source : ModeSource operations policy contracts tables families actions world
      whole (.value input) output demand requirements wholeScope)
    {returnHints : SourceDependencyChecks.Lexical.ReturnHints wholeScope}
    (hinted : SourceDependencyChecks.Lexical.ReturnHints.Matches tables families returnHints whole)
    (pendingLocal : SourceDependencyChecks.Lexical.ReturnHints.Recursive.Pending outward actions
      (available (ownedTickets whole)) world returnHints .nil .ordinary output.mode)
    (usage : LexicalUnwind.MachineUse policy actions (.eval
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩))
    (ticketAccess : LexicalUnwind.MachineTicketAccess policy actions (.eval
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩))
    (resourceAccess : LexicalUnwind.MachineAccess ambient (.eval
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩))
    (operandSupport : Syntax.resourceDependencies operand.dependencies ⊆ operandBound)
    (operandBoundary : match SourceDependencyCapture.select requested operation wholeScope with
      | some (.handler _ receiving _ _) => operandBound ⊆ receiving.visibleResources ++ ambient
      | _ => False)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (isValue : operand.IsValue)
    (fresh : contracts owner = none) (freshAction : actions owner = none)
    (absent : owner ∉ ownedTickets whole)
    (bound : Bound annotations wholeScope) (freshAnnotation : annotations owner = none)
    (recorded : ∀ key body, (key, body) ∈ (resumes : Store) →
      ResumeAnnotated operations policy contracts tables families actions annotations world whole key body)
    (closing : UnwindRecords operations policy contracts tables world whole disposals)
    (closingRecorded : ∀ key body, (key, body) ∈ disposals →
      UnwindAnnotated operations policy contracts tables families annotations world whole key body)
    (unique : (ownedTickets whole).Nodup)
    (storeAnnotation : StoreAnnotation (resumes ++ disposals) annotatedStore)
    (annotation : RowAnnotation requirements annotatedRoot)
    (certificate : RecursiveRequirements.Checked annotatedStore []
      (available (ownedTickets whole)) annotatedRoot certificateRow)
    (currentCheck : RecursiveRequirements.Checked annotatedStore (OwnerPhases.ofStack tables whole)
      (available (ownedTickets whole)) currentRequirements requestRow)
    (currentLocal : SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local outward actions
      (available (ownedTickets whole)) world currentDependencies returnHints)
    {answer : Value} {residual : List Instance} {boundary : ModeValue}
    {capDemand tailDemand : List Nat} {capReq : Requirements capDemand} {tailReq : Requirements tailDemand}
    {capScope tailScope : Receiving}
    (declaration : SourceDependencyFrames.Frame operations policy contracts tables families world
      (.handler handler) answer answer [] (.request [] [])
      (.handler handler.effectInst (tables handler) (families handler)) (handler.effectInst :: residual) residual)
    (returns : boundary = .value answer ∨ boundary = .unwind)
    (saved : ModeSource operations policy contracts tables families actions world
      capture (.value input) boundary capDemand capReq capScope)
    (waiting : ModeSource operations policy contracts tables families actions world
      tail boundary output tailDemand tailReq tailScope)
    (scopeSame : wholeScope = capScope.append tailScope)
    (demandSame : demand = capDemand ++ tailDemand)
    (evaluation : ∀ store receiving phases, evaluate store receiving phases requirements =
      merge (evaluate store (OwnerPhases.ofStack tables tail ++ receiving) phases capReq)
        (evaluate store receiving (spendAll phases capDemand) tailReq)) :
    ∃ (resumeEffects closeEffects : List Instance)
      (family : Nat → Dependencies) (offered : ClauseContract) (advertised : Footprint),
      wholeScope = capScope.append tailScope ∧ demand = capDemand ++ tailDemand ∧
      (boundary = .value answer ∨ boundary = .unwind) ∧
      SourceDependencyFrames.Frame operations policy contracts tables families world (.handler handler) answer answer [] (.request [] [])
        (.handler handler.effectInst (tables handler) (families handler)) (handler.effectInst :: residual) residual ∧
      lookup operation (tables handler) = some offered ∧
      offered.row capScope.held = some advertised ∧
      (SourceDependencyCapture.lookupDependencies operation (families handler)).bind
        (SourceDependencyCapture.modeDependencies capScope.held) = some family ∧
      residualize (CallableProtectionFrames.contextOf tables tail) advertised = some requestRow ∧
      ∃ cutCertificate : Requirements (capDemand ++ tailDemand), ∃ cutRow,
      RowAnnotation (.sequence (capReq.prepend (OwnerPhases.ofStack tables tail)) tailReq) cutCertificate ∧
      RecursiveRequirements.Checked annotatedStore [] (available (ownedTickets whole)) cutCertificate cutRow ∧
      cutRow ⊆ certificateRow ∧
      RequirementPath annotatedRoot cutCertificate [] ∧
      RequirementPath (.sequence (capReq.prepend (OwnerPhases.ofStack tables tail)) tailReq) cutCertificate [] ∧
      ∀ (capAnnotated : Requirements capDemand) (tailAnnotated : Requirements tailDemand),
        RowAnnotation capReq capAnnotated → RowAnnotation tailReq tailAnnotated →
        RequirementPath (.sequence (capAnnotated.prepend (OwnerPhases.ofStack tables tail)) tailAnnotated) cutCertificate [] →
        (offered.dispose = true → ∃ closingDemand, ∃ closingRequirements : Requirements closingDemand,
          UnwindSource operations policy contracts tables families world capture closingDemand closingRequirements capScope ∧
          RequirementPath closingRequirements capAnnotated []) →
      ∃ capRow tailRow, capRow ++ tailRow ⊆ certificateRow ∧
      ∃ closingDemand closingRow, closingDemand.Perm capDemand ∧
      (offered.dispose = false → closingRow = none) ∧
      let contract : Contract := ⟨input, answer, capScope.held, capDemand, capRow,
        closingDemand, closingRow, resumeEffects, closeEffects⟩
      let nextStack := Stack.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail
      let nextResumes : Store := (⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: resumes
      let nextAnnotations := fun other => if other = owner then some capScope else annotations other
      ∃ nextDisposals nextStore : Store,
        StoreAnnotation (nextResumes ++ nextDisposals) nextStore ∧
        RecursiveRequirements.lookup ⟨owner, .resume⟩ nextStore = some ⟨capDemand, capAnnotated⟩ ∧
        Bound nextAnnotations (.live owner capScope tailScope) ∧
        ClauseRowAdmission.SourceStore operations.erase owner contract.erase nextStore ∧
        (∀ key body, (key, body) ∈ nextResumes →
          ResumeAnnotated operations policy (contracts.insert owner contract) tables families
            (actions.insert owner code.requiredActions) nextAnnotations world nextStack key body) ∧
        (∀ key body, (key, body) ∈ nextDisposals →
          UnwindAnnotated operations policy (contracts.insert owner contract) tables families
            nextAnnotations world nextStack key body) ∧
        UnwindRecords operations policy (contracts.insert owner contract) tables world nextStack nextDisposals ∧
        ModeSource operations policy (contracts.insert owner contract) tables families
          (actions.insert owner code.requiredActions) world nextStack (.value answer) output tailDemand
          (.sequence (.spent owner) tailReq) (.live owner capScope tailScope) ∧
        (∃ nextHints : SourceDependencyChecks.Lexical.ReturnHints (.live owner capScope tailScope),
          SourceDependencyChecks.Lexical.ReturnHints.Matches tables families nextHints nextStack ∧
          SourceDependencyChecks.Lexical.ReturnHints.Recursive.Pending outward (actions.insert owner code.requiredActions)
            (available (ownedTickets nextStack)) world nextHints .nil .ordinary output.mode ∧
          (code.requiredActions.resume = true →
            SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local outward (actions.insert owner code.requiredActions)
              (available (ownedTickets nextStack)) world (.invoke ⟨owner, .resume⟩) nextHints) ∧
          (code.requiredActions.dispose = true →
            SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local outward (actions.insert owner code.requiredActions)
              (available (ownedTickets nextStack)) world (.invoke ⟨owner, .dispose⟩) nextHints)) ∧
        RowAnnotation (.sequence (.spent owner) tailReq) (.sequence (.spent owner) tailAnnotated) ∧
        LexicalUnwind.MachineUse policy (actions.insert owner code.requiredActions)
          (.eval ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩) ∧
        LexicalUnwind.MachineTicketAccess policy (actions.insert owner code.requiredActions)
          (.eval ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩) ∧
        LexicalUnwind.MachineAccess ambient
          (.eval ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩) ∧
        RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩
          ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩ [.ticket owner] [] ∧
        ownedTickets nextStack = owner :: ownedTickets whole ∧
        (ownedTickets nextStack).Nodup ∧
        ((owner :: capDemand) ++ tailDemand).Perm (ownedTickets nextStack) ∧
        spend (available (ownedTickets nextStack)) owner = available (ownedTickets whole) ∧
        RecursiveRequirements.Checked nextStore (OwnerPhases.ofStack tables tail)
          (available (ownedTickets whole)) capAnnotated capRow ∧
        RecursiveRequirements.Checked nextStore []
          (spendAll (available (ownedTickets whole)) capDemand) tailAnnotated tailRow ∧
        RecursiveRequirements.Checked nextStore (OwnerPhases.ofStack tables nextStack)
          (available (ownedTickets nextStack)) (.invoke ⟨owner, .resume⟩ capDemand []) capRow ∧
        ClauseRowAdmission.Interface owner contract.erase offered.dispose nextStore
          (OwnerPhases.ofStack tables tail) (available (ownedTickets nextStack)) requestRow ∧
          ∃ clauseDemand, ∃ clauseReq clauseAnnotated : Requirements clauseDemand, ∃ clauseRow,
            Expression operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
              Environment.empty (code.subst parameter operand) answer clauseDemand clauseReq (family owner) ∧
            RowAnnotation clauseReq clauseAnnotated ∧
            RecursiveRequirements.Checked nextStore (OwnerPhases.ofStack tables nextStack)
              (available (ownedTickets nextStack)) clauseAnnotated clauseRow ∧
            clauseRow ⊆ requestRow ++ capRow ∧
            clauseDemand.Perm (owner :: capDemand) ∧
            RowAnnotation
              (.sequence (clauseReq.prepend (OwnerPhases.ofStack tables nextStack)) (.sequence (.spent owner) tailReq))
              (.sequence (clauseAnnotated.prepend (OwnerPhases.ofStack tables nextStack)) (.sequence (.spent owner) tailAnnotated)) ∧
            RecursiveRequirements.Checked nextStore [] (available (ownedTickets nextStack))
              (.sequence (clauseAnnotated.prepend (OwnerPhases.ofStack tables nextStack)) (.sequence (.spent owner) tailAnnotated))
              (clauseRow ++ tailRow) ∧
            clauseRow ++ tailRow ⊆ requestRow ++ certificateRow ∧
            (clauseDemand ++ tailDemand).Perm (ownedTickets nextStack) := by
  have erasedCurrent := DeclaredSources.expression_erase (SourceDependencyAnnotations.expression_erase current)
  obtain ⟨argument, operationKnown, payload⟩ : ∃ argument,
      operations requested operation = some (argument, input) ∧
      ValueSummary operations policy contracts world Environment.empty allowed operand argument := by
    generalize encoded : Instantiation.freezeEffect requested = actual at current
    cases current with
    | perform known admitted operandSource formed =>
        cases freeze_effect_injective encoded
        exact ⟨_, known, Values.summary operandSource isValue⟩
  have closed : ClosedValue operand := ScopedPorts.typed_value_closed
    ((DeclaredSourceValues.erase (value_erase payload)).ports .none) isValue
  have requestExport := RecursiveRequirements.checked_complete currentCheck
  rw [RecursiveDispatch.request_evaluation erasedCurrent closed.1] at requestExport
  simp only [OwnerSource.exportAt, OwnerPhaseTransitions.project_actual] at requestExport
  obtain ⟨offered, advertised, offeredKnown, offeredMode, offeredRow, offeredExport⟩ :=
    RecursiveDispatch.cut_residual cut requestExport
  simp only [Bool.false_or] at offeredMode offeredRow
  have rowAvailable : offered.row capScope.held = some advertised := by
    simpa only [saved.realizes.held] using offeredRow
  have declarations : Declarations operations policy contracts world Environment.empty residual
      handler.effectInst answer handler.clauses (tables handler) (families handler) := by
    cases declaration with | handler scope annotation clauses coverage unique declarations capabilities modes => exact declarations
  obtain ⟨declaredArgument, declaredInput, resumeEffects, closeEffects, family,
    declaredOperation, resumeInterface, closeInterface, familyKnown, bodyFamily⟩ :=
    SourceDependencyCapture.selected_body declarations selected offeredKnown rowAvailable
  exact ⟨resumeEffects, closeEffects, family, offered, advertised,
    capture_mode_segments_at_body cut current source hinted pendingLocal usage ticketAccess resourceAccess
      operandSupport operandBoundary selected isValue fresh freshAction absent bound freshAnnotation
      recorded closing closingRecorded unique storeAnnotation annotation certificate currentCheck currentLocal
      declaration returns saved waiting scopeSame demandSame evaluation offeredKnown rowAvailable
      declaredOperation familyKnown bodyFamily⟩

theorem capture_mode_segments
    (cut : HandlerCut requested whole capture tail handler)
    (current : Expression operations policy contracts world allowed caller Environment.empty
      (.perform (Instantiation.freezeEffect requested) operation operand) input currentDemand currentRequirements currentDependencies)
    (source : ModeSource operations policy contracts tables families actions world
      whole (.value input) output demand requirements wholeScope)
    {returnHints : SourceDependencyChecks.Lexical.ReturnHints wholeScope}
    (hinted : SourceDependencyChecks.Lexical.ReturnHints.Matches tables families returnHints whole)
    (pendingLocal : SourceDependencyChecks.Lexical.ReturnHints.Recursive.Pending outward actions
      (available (ownedTickets whole)) world returnHints .nil .ordinary output.mode)
    (usage : LexicalUnwind.MachineUse policy actions (.eval
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩))
    (ticketAccess : LexicalUnwind.MachineTicketAccess policy actions (.eval
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩))
    (resourceAccess : LexicalUnwind.MachineAccess ambient (.eval
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩))
    (operandSupport : Syntax.resourceDependencies operand.dependencies ⊆ operandBound)
    (operandBoundary : match SourceDependencyCapture.select requested operation wholeScope with
      | some (.handler _ receiving _ _) => operandBound ⊆ receiving.visibleResources ++ ambient
      | _ => False)
    (selected : ClauseAt operation handler.clauses parameter binder code)
    (isValue : operand.IsValue)
    (fresh : contracts owner = none) (freshAction : actions owner = none)
    (absent : owner ∉ ownedTickets whole)
    (bound : Bound annotations wholeScope) (freshAnnotation : annotations owner = none)
    (recorded : ∀ key body, (key, body) ∈ (resumes : Store) →
      ResumeAnnotated operations policy contracts tables families actions annotations world whole key body)
    (closing : UnwindRecords operations policy contracts tables world whole disposals)
    (closingRecorded : ∀ key body, (key, body) ∈ disposals →
      UnwindAnnotated operations policy contracts tables families annotations world whole key body)
    (unique : (ownedTickets whole).Nodup)
    (storeAnnotation : StoreAnnotation (resumes ++ disposals) annotatedStore)
    (annotation : RowAnnotation requirements annotatedRoot)
    (certificate : RecursiveRequirements.Checked annotatedStore []
      (available (ownedTickets whole)) annotatedRoot certificateRow)
    (currentCheck : RecursiveRequirements.Checked annotatedStore (OwnerPhases.ofStack tables whole)
      (available (ownedTickets whole)) currentRequirements requestRow)
    (currentLocal : SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local outward actions
      (available (ownedTickets whole)) world currentDependencies returnHints) :
    ∃ (answer : Value) (residual : List Instance) (boundary : ModeValue)
      (capDemand tailDemand : List Nat) (capReq : Requirements capDemand) (tailReq : Requirements tailDemand)
      (capScope tailScope : Receiving) (resumeEffects closeEffects : List Instance)
      (family : Nat → Dependencies) (offered : ClauseContract) (advertised : Footprint),
      wholeScope = capScope.append tailScope ∧ demand = capDemand ++ tailDemand ∧
      (boundary = .value answer ∨ boundary = .unwind) ∧
      SourceDependencyFrames.Frame operations policy contracts tables families world (.handler handler) answer answer [] (.request [] [])
        (.handler handler.effectInst (tables handler) (families handler)) (handler.effectInst :: residual) residual ∧
      lookup operation (tables handler) = some offered ∧
      offered.row capScope.held = some advertised ∧
      (SourceDependencyCapture.lookupDependencies operation (families handler)).bind
        (SourceDependencyCapture.modeDependencies capScope.held) = some family ∧
      residualize (CallableProtectionFrames.contextOf tables tail) advertised = some requestRow ∧
      ∃ cutCertificate : Requirements (capDemand ++ tailDemand), ∃ cutRow,
      RowAnnotation (.sequence (capReq.prepend (OwnerPhases.ofStack tables tail)) tailReq) cutCertificate ∧
      RecursiveRequirements.Checked annotatedStore [] (available (ownedTickets whole)) cutCertificate cutRow ∧
      cutRow ⊆ certificateRow ∧
      RequirementPath annotatedRoot cutCertificate [] ∧
      RequirementPath (.sequence (capReq.prepend (OwnerPhases.ofStack tables tail)) tailReq) cutCertificate [] ∧
      ∀ (capAnnotated : Requirements capDemand) (tailAnnotated : Requirements tailDemand),
        RowAnnotation capReq capAnnotated → RowAnnotation tailReq tailAnnotated →
        RequirementPath (.sequence (capAnnotated.prepend (OwnerPhases.ofStack tables tail)) tailAnnotated) cutCertificate [] →
        (offered.dispose = true → ∃ closingDemand, ∃ closingRequirements : Requirements closingDemand,
          UnwindSource operations policy contracts tables families world capture closingDemand closingRequirements capScope ∧
          RequirementPath closingRequirements capAnnotated []) →
      ∃ capRow tailRow, capRow ++ tailRow ⊆ certificateRow ∧
      ∃ closingDemand closingRow, closingDemand.Perm capDemand ∧
      (offered.dispose = false → closingRow = none) ∧
      let contract : Contract := ⟨input, answer, capScope.held, capDemand, capRow,
        closingDemand, closingRow, resumeEffects, closeEffects⟩
      let nextStack := Stack.live owner (ScopedPorts.embedPort input.erase.port) handler.answer capture handler.scope tail
      let nextResumes : Store := (⟨owner, .resume⟩, ⟨capDemand, capReq⟩) :: resumes
      let nextAnnotations := fun other => if other = owner then some capScope else annotations other
      ∃ nextDisposals nextStore : Store,
        StoreAnnotation (nextResumes ++ nextDisposals) nextStore ∧
        RecursiveRequirements.lookup ⟨owner, .resume⟩ nextStore = some ⟨capDemand, capAnnotated⟩ ∧
        Bound nextAnnotations (.live owner capScope tailScope) ∧
        ClauseRowAdmission.SourceStore operations.erase owner contract.erase nextStore ∧
        (∀ key body, (key, body) ∈ nextResumes →
          ResumeAnnotated operations policy (contracts.insert owner contract) tables families
            (actions.insert owner code.requiredActions) nextAnnotations world nextStack key body) ∧
        (∀ key body, (key, body) ∈ nextDisposals →
          UnwindAnnotated operations policy (contracts.insert owner contract) tables families
            nextAnnotations world nextStack key body) ∧
        UnwindRecords operations policy (contracts.insert owner contract) tables world nextStack nextDisposals ∧
        ModeSource operations policy (contracts.insert owner contract) tables families
          (actions.insert owner code.requiredActions) world nextStack (.value answer) output tailDemand
          (.sequence (.spent owner) tailReq) (.live owner capScope tailScope) ∧
        (∃ nextHints : SourceDependencyChecks.Lexical.ReturnHints (.live owner capScope tailScope),
          SourceDependencyChecks.Lexical.ReturnHints.Matches tables families nextHints nextStack ∧
          SourceDependencyChecks.Lexical.ReturnHints.Recursive.Pending outward (actions.insert owner code.requiredActions)
            (available (ownedTickets nextStack)) world nextHints .nil .ordinary output.mode ∧
          (code.requiredActions.resume = true →
            SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local outward (actions.insert owner code.requiredActions)
              (available (ownedTickets nextStack)) world (.invoke ⟨owner, .resume⟩) nextHints) ∧
          (code.requiredActions.dispose = true →
            SourceDependencyChecks.Lexical.ReturnHints.Recursive.Local outward (actions.insert owner code.requiredActions)
              (available (ownedTickets nextStack)) world (.invoke ⟨owner, .dispose⟩) nextHints)) ∧
        RowAnnotation (.sequence (.spent owner) tailReq) (.sequence (.spent owner) tailAnnotated) ∧
        LexicalUnwind.MachineUse policy (actions.insert owner code.requiredActions)
          (.eval ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩) ∧
        LexicalUnwind.MachineTicketAccess policy (actions.insert owner code.requiredActions)
          (.eval ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩) ∧
        LexicalUnwind.MachineAccess ambient
          (.eval ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩) ∧
        RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, caller, whole⟩
          ⟨code.subst parameter operand, .ticket binder owner, nextStack⟩ [.ticket owner] [] ∧
        ownedTickets nextStack = owner :: ownedTickets whole ∧
        (ownedTickets nextStack).Nodup ∧
        ((owner :: capDemand) ++ tailDemand).Perm (ownedTickets nextStack) ∧
        spend (available (ownedTickets nextStack)) owner = available (ownedTickets whole) ∧
        RecursiveRequirements.Checked nextStore (OwnerPhases.ofStack tables tail)
          (available (ownedTickets whole)) capAnnotated capRow ∧
        RecursiveRequirements.Checked nextStore []
          (spendAll (available (ownedTickets whole)) capDemand) tailAnnotated tailRow ∧
        RecursiveRequirements.Checked nextStore (OwnerPhases.ofStack tables nextStack)
          (available (ownedTickets nextStack)) (.invoke ⟨owner, .resume⟩ capDemand []) capRow ∧
        ClauseRowAdmission.Interface owner contract.erase offered.dispose nextStore
          (OwnerPhases.ofStack tables tail) (available (ownedTickets nextStack)) requestRow ∧
          ∃ clauseDemand, ∃ clauseReq clauseAnnotated : Requirements clauseDemand, ∃ clauseRow,
            Expression operations policy (contracts.insert owner contract) world residual (.ticket binder owner)
              Environment.empty (code.subst parameter operand) answer clauseDemand clauseReq (family owner) ∧
            RowAnnotation clauseReq clauseAnnotated ∧
            RecursiveRequirements.Checked nextStore (OwnerPhases.ofStack tables nextStack)
              (available (ownedTickets nextStack)) clauseAnnotated clauseRow ∧
            clauseRow ⊆ requestRow ++ capRow ∧
            clauseDemand.Perm (owner :: capDemand) ∧
            RowAnnotation
              (.sequence (clauseReq.prepend (OwnerPhases.ofStack tables nextStack)) (.sequence (.spent owner) tailReq))
              (.sequence (clauseAnnotated.prepend (OwnerPhases.ofStack tables nextStack)) (.sequence (.spent owner) tailAnnotated)) ∧
            RecursiveRequirements.Checked nextStore [] (available (ownedTickets nextStack))
              (.sequence (clauseAnnotated.prepend (OwnerPhases.ofStack tables nextStack)) (.sequence (.spent owner) tailAnnotated))
              (clauseRow ++ tailRow) ∧
            clauseRow ++ tailRow ⊆ requestRow ++ certificateRow ∧
            (clauseDemand ++ tailDemand).Perm (ownedTickets nextStack) := by
  obtain ⟨answer, residual, boundary, capDemand, tailDemand, capReq, tailReq, capScope, tailScope,
    declaration, returns, saved, waiting, scopeSame, demandSame, evaluation⟩ := source.handler_cut cut
  obtain ⟨resumeEffects, closeEffects, family, offered, advertised, facts⟩ :=
    capture_mode_segments_at_cut cut current source hinted pendingLocal usage ticketAccess resourceAccess
      operandSupport operandBoundary selected isValue fresh freshAction absent bound freshAnnotation
      recorded closing closingRecorded unique storeAnnotation annotation certificate currentCheck currentLocal
      declaration returns saved waiting scopeSame demandSame evaluation
  exact ⟨answer, residual, boundary, capDemand, tailDemand, capReq, tailReq, capScope, tailScope,
    resumeEffects, closeEffects, family, offered, advertised, facts⟩

end Ash.OneShot.SourceDependencySchemes.Lexical
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.mode_capture_ownership_balance
#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.capture_mode_segments


#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.capture_mode_segments_at_cut

#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.capture_mode_segments_at_body

#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.resume_fragment_rows

#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.capture_mode_segments_with_closing

#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.capture_mode_segments_with_closing_lookup

#print axioms Ash.OneShot.SourceDependencySchemes.Lexical.capture_mode_segments_with_closing_store
