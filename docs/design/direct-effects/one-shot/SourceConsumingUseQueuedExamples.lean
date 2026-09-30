import SourceAnnotatedStoredUseQueued
import SourceConsumingUseAdmissionExamples
import SourceConsumingUseTransport
import SourceAnnotatedStoredUseHandlers

/-! A queued body inhabits an intermediate masking caller while retaining the
original richer captured source. Focus and return reconstruct its source without
assuming a Context whose dormant saved code is valid at that masking caller. -/
namespace Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceConsumingClauseAnnotations (Body Declarations Bounded)
open SourceScheduledCapabilityAnnotations (Code recipeLaws)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledNeutral (OwnerCut)
open SourcePlanBounds (Annotation)
open SourceBoundSnapshots (Snapshot Returned)
open SourceDependencyCapture.Examples (effectE)
open UseAdmissionExamples (actions phases context saved waiting whole)
open LeafAdmissionExamples (inner innerBody maskedBody)

private def scopeOf {scope} {hints : Hints scope} (_ : Forest hints) := scope

def installed := Forest.handler (effect := effectE) (table := []) (families := []) (required := []) whole
def callerForest := Forest.handler (effect := effectE) (table := []) (families := []) (required := []) Forest.nil
def caller : Interfaces [] callerForest := .handler .nil .nil
theorem cut : OwnerCut 19 installed callerForest saved waiting := .handler .hit

def declarations : Declarations [] SourceScheduledInvocationInterfaceExamples.declarations :=
  .cons (.available (fun _ => .sequence [] .pure .pure .resume))
    (.available (fun _ => .sequence [] .pure .pure .resume)) .nil

theorem bounded : Bounded HandlerInterfaceExamples.bounds declarations [] :=
  .cons (.available (.available (fun _ => .sequence (.resume rfl))) (fun _ => .sequence .resume))
    (.available (.available (fun _ => .sequence (.resume rfl))) (fun _ => .sequence .resume)) .nil

theorem nested : (innerBody (world := [])).Nested := .handler declarations bounded .resume

theorem inner_source : AtUse [] actions phases context innerBody callerForest := by
  have source := UseAdmissionExamples.at_use
  cases source with | handler inner => exact inner

/-- The record's original and current receivers are deliberately different. -/
def queued : UseQueuedBody [(effectE, 0)] [] context cut caller (innerBody (world := [])).boundAnnotation where
  body := innerBody
  origin := rfl
  source := inner_source
  nested := nested
  checked := by
    have parent := (LeafAdmissionExamples.admitted (world := [])).at_capture
      (actions := actions) (phases := phases) (captured := scopeOf saved) (waiting := scopeOf waiting) rfl rfl rfl
    exact parent.2

/-- The original E request is masked here, even though the queued body will
supply it before consumption. This is not an eager intermediate Context. -/
theorem intermediate_mask : SourceContextualHints.checkRequirements
    ((scopeOf callerForest).append (.spent 19 (scopeOf waiting))) [(effectE, 0)] = false := rfl

theorem queued_generated : ∃ annotation : Code [] inner installed,
    annotation.Valid [] actions phases ∧ SourcePlanBounds.ofCode annotation = innerBody.boundAnnotation := by
  obtain ⟨annotation, ready, kept, _⟩ := queued.generate (recipeLaws []) (fun evidence => evidence)
  exact ⟨annotation, ready, kept⟩

def parentBody : Body [] 19 (Plan.sequence Plan.pure inner) := .sequence [] .pure .pure innerBody
def parent : UseQueuedBody [(effectE, 0)] [] context cut caller parentBody.boundAnnotation :=
  ⟨parentBody, rfl, .sequence inner_source, .sequence nested, ⟨rfl, queued.checked⟩⟩

theorem focused : UseFocusedSource [(effectE, 0)] [] context cut caller
    (Annotation.absent (plan := Plan.pure)) innerBody.boundAnnotation := parent.focused (.sequence _)

theorem current_focus : UseFocusedSource [(effectE, 0)] [] context cut caller
    innerBody.boundAnnotation (Annotation.absent (plan := Plan.pure)) := parent.focused (.pairRight _)

theorem current_child_valid : ∃ annotation : Code [] inner (.plain Plan.pure installed),
    annotation.Valid [] actions phases ∧ SourcePlanBounds.ofCode annotation = innerBody.boundAnnotation :=
  current_focus.child_valid (recipeLaws []) (fun evidence => evidence)

def position : SourceAnnotatedCode.Context := .bind .unit 3 (.unit .unit)

/-- Return uses the actual queued record to reconstruct the plugged body. -/
theorem returned_source (pending : SourceBoundSnapshots.Retained [] installed)
    {next : Snapshot []}
    (step : Returned position
      ⟨_, Plan.pure, .absent, _, _, .plain inner installed, .plain innerBody.boundAnnotation pending⟩ next) :
    ∃ nextQueued : UseQueuedBody [(effectE, 0)] [] context cut caller (innerBody.boundAnnotation.plug position).2.2,
      next = ⟨_, _, nextQueued.body.boundAnnotation, _, _, installed, pending⟩ :=
  queued.returned position .absent pending step

def canonical : SourceBoundSnapshots.CanonicalPayload
    (fun bounds => UseQueuedBody [(effectE, 0)] [] context cut caller bounds)
    (innerBody (world := [])).boundAnnotation.normalize := ⟨_, queued, rfl⟩

theorem canonical_generated : ∃ annotation : Code [] inner installed,
    annotation.Valid [] actions phases ∧
    SourcePlanBounds.ofCode annotation = innerBody.boundAnnotation.normalize ∧
    annotation.Expanded ∧ (innerBody (world := [])).boundAnnotation.normalize.Admitted :=
  canonical.generate_use_queued (recipeLaws []) (fun evidence => evidence)

theorem canonical_return (pending : SourceBoundSnapshots.Retained [] installed)
    {next : Snapshot []}
    (step : Returned position
      ⟨_, Plan.pure, .absent, _, _, .plain inner installed, .plain innerBody.boundAnnotation.normalize pending⟩ next) :
    ∃ annotation : Code [] next.plan next.forest,
      annotation.Valid [] actions phases ∧ SourcePlanBounds.ofCode annotation = next.current ∧
      annotation.Expanded ∧ next.current.Admitted :=
  canonical.returned_use_queued (recipeLaws []) (fun evidence => evidence) position .absent pending step

namespace Records
open SourceBoundSnapshots

/-- Only the designated queued computation carries this payload. Other source
positions are deliberately untracked; this is not a whole-state coverage claim. -/
abbrev Payload : RecordFamily [] := fun bounds => Option
  (UseQueuedBody [(effectE, 0)] [] context cut caller bounds)

def inside : Retained [] (.plain inner .nil) := .plain innerBody.boundAnnotation .nil
def tail : Retained [] installed := Retained.absent installed
def insideRecords : inside.Records Payload := .plain (some queued) .nil
def tailRecords : tail.Records Payload :=
  .handler (.live (.plain none .nil) (.live .nil (.handler .nil)))

def before : Snapshot [] := ⟨_, Plan.pure, .absent, _, _, _, inside.append tail⟩
def captured : Snapshot [] := ⟨_, Plan.pure, .absent, _, _, _, .live (owner := 73) inside tail⟩
def restored : Snapshot [] := Snapshot.value (inside.append (.spent (owner := 73) tail))
def beforeRecords : before.pending.Records Payload := insideRecords.append tailRecords
def capturedRecords : captured.pending.Records Payload := .live insideRecords tailRecords
def restoredRecords : restored.pending.Records Payload := insideRecords.append (.spent tailRecords)

theorem capture : RecordCapture 73 Payload beforeRecords capturedRecords := .cut _ _ _ _
theorem resume_records : RecordResumption 73 Payload capturedRecords restoredRecords := .cut _ .nil _ _
theorem captured_source_values : capturedRecords.entries = beforeRecords.entries := capture.entries
theorem restored_source_values : capturedRecords.entries.Perm restoredRecords.entries := resume_records.entries

def recoveredPayload : Payload innerBody.boundAnnotation :=
  match restoredRecords with
  | .plain payload _ => payload

def recovered : UseQueuedBody [(effectE, 0)] [] context cut caller innerBody.boundAnnotation :=
  recoveredPayload.get (by rfl)

theorem recovered_exact : recovered = queued := rfl

def restoredSource : UseReceiverBody [(effectE, 0)] [] context cut caller
    (.spent (owner := 73) installed) innerBody.boundAnnotation :=
  recovered.at_receiver.expand (.history .refl)

/-- After record restoration, retain the neutral receiver path alongside the
source. It remains usable by focus/return without assuming a new AtUse. -/
theorem restored_generation : ∃ annotation : Code [] inner (.spent (owner := 73) installed),
    annotation.Valid [] actions phases ∧ SourcePlanBounds.ofCode annotation = innerBody.boundAnnotation :=
  restoredSource.generate (recipeLaws []) (fun evidence => evidence)

theorem restored_return (pending : Retained [] (.spent (owner := 73) installed))
    {next : Snapshot []}
    (step : Returned position
      ⟨_, Plan.pure, .absent, _, _, .plain inner (.spent (owner := 73) installed),
        .plain innerBody.boundAnnotation pending⟩ next) :
    ∃ source : UseReceiverBody [(effectE, 0)] [] context cut caller
        (.spent (owner := 73) installed) (innerBody.boundAnnotation.plug position).2.2,
      next = ⟨_, _, source.source.body.boundAnnotation, _, _, .spent (owner := 73) installed, pending⟩ :=
  restoredSource.returned position .absent pending step

/-- Repeated neutral insertions compose, so a record does not get stuck after
the first restored spent marker or pure completion frame. -/
theorem restored_twice : ∃ annotation : Code [] inner
    (.cleanup (needs := []) Plan.pure (.spent (owner := 73) installed)),
    annotation.Valid [] actions phases ∧ SourcePlanBounds.ofCode annotation = innerBody.boundAnnotation :=
  (restoredSource.expand (.completion .refl)).generate (recipeLaws []) (fun evidence => evidence)

theorem restored_current_focus : Nonempty
    (UseReceiverBody [(effectE, 0)] [] context cut caller
      (.plain Plan.pure (.spent (owner := 73) installed)) innerBody.boundAnnotation) :=
  ((parent.at_receiver.expand (.history (owner := 73) .refl)).focused (.pairRight _)).current_body

end Records

namespace Transport

def nextActions := actions.insert 88 ⟨true, true⟩
def nextPhases := OwnerPhaseTransitions.spend (OwnerPhaseTransitions.available [19, 37, 88]) 88

theorem permissions : Syntax.UsageExtension actions nextActions :=
  Syntax.fresh_usage_insert_extends rfl

/-- The original source still needs both its selected owner and the outside
owner invoked by its saved code. Only unrelated owner88 is retired here. -/
theorem availability : SourceScheduledPhaseRestriction.AvailableOn
    (SourceDependencyOwners.owners (scopeOf whole)) phases nextPhases := by
  intro owner member _
  change owner ∈ [19, 37] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

def transported := queued.transport permissions availability (show [] ⊆ [7] from by simp)
def bounds := (innerBody (world := [])).boundAnnotation.world_weaken (show [] ⊆ [7] from by simp)

/-- Registry growth, unrelated retirement and world growth compose while the
caller still masks E. Original richer saved code is retained by the compiler. -/
theorem generated : ∃ annotation : Code [7] inner installed,
    annotation.Valid [] nextActions nextPhases ∧ SourcePlanBounds.ofCode annotation = bounds := by
  obtain ⟨annotation, ready, kept, _⟩ := transported.generate (recipeLaws []) (fun evidence => evidence)
  exact ⟨annotation, ready, kept⟩

/-- The transported record is consumed by the existing return/recomposition
API, rather than replaced by a newly assumed source-admission witness. -/
theorem returned : ∃ annotation : Code [7] (bounds.plug position).2.1 installed,
    annotation.Valid [] nextActions nextPhases ∧
    SourcePlanBounds.ofCode annotation = (bounds.plug position).2.2 := by
  obtain ⟨annotation, ready, kept, _⟩ := (transported.plug position).generate
    (recipeLaws []) (fun evidence => evidence)
  exact ⟨annotation, ready, kept⟩

/-- Keeping owner19 available is insufficient: the captured source also
observes owner37, so the phase-transport premise rejects its retirement. -/
theorem outside_retirement_rejected : ¬ SourceScheduledPhaseRestriction.AvailableOn
    (SourceDependencyOwners.owners (scopeOf whole)) phases (OwnerPhaseTransitions.spend phases 37) := by
  intro extension
  have impossible := extension 37 (by decide) (by rfl)
  contradiction

end Transport

namespace HandlerEntry

/-- One parent source record supplies both successive handler entries. -/
def root : UseQueuedBody [(effectE, 0)] [] context OwnerCut.hit Interfaces.nil
    (maskedBody (world := [])).boundAnnotation where
  body := maskedBody
  origin := rfl
  source := UseAdmissionExamples.at_use
  nested := .handler .nil .nil UseQueuedExamples.nested
  checked := (LeafAdmissionExamples.admitted (world := [])).at_capture
    (actions := actions) (phases := phases) (captured := scopeOf saved) (waiting := scopeOf waiting) rfl rfl rfl

def outer := root.at_receiver.handler_body
def inner := outer.handler_body

/-- The first entry produces the queued record used in the masking example,
rather than assuming its child source separately. -/
theorem outer_body : outer.source.body = (innerBody (world := [])) := rfl

theorem outer_generated : ∃ annotation : Code [] LeafAdmissionExamples.inner installed,
    annotation.Valid [] actions phases ∧ SourcePlanBounds.ofCode annotation = innerBody.boundAnnotation :=
  outer.generate (recipeLaws []) (fun evidence => evidence)

/-- The second entry installs the supplying handler. The same rich saved
source is now compiled at consumption, including its outside-owner invocation. -/
theorem inner_generated : ∃ annotation : Code [] (.invoke (key := ⟨19, .resume⟩))
    (.handler (effect := effectE) (table := SourceDependencyCapture.Examples.resumeTable)
      (families := SourceDependencyCapture.Examples.resumeDependencies) (required := []) installed),
    annotation.Valid [] actions phases ∧ SourcePlanBounds.ofCode annotation = Annotation.absent :=
  inner.generate (recipeLaws []) (fun evidence => evidence)

def initialSnapshot (pending : SourceBoundSnapshots.Retained [] whole) : Snapshot [] :=
  ⟨_, LeafAdmissionExamples.masked, maskedBody.boundAnnotation, _, _, whole, pending⟩

def outerSnapshot (pending : SourceBoundSnapshots.Retained [] whole) : Snapshot [] :=
  ⟨_, LeafAdmissionExamples.inner, innerBody.boundAnnotation, _, _, installed, .handler pending⟩

theorem outer_entry (pending : SourceBoundSnapshots.Retained [] whole) :
    SourceBoundSnapshots.EnteredHandler effectE [] [] SourceDeclarationPlans.ClausePlans.nil
      (initialSnapshot pending) (outerSnapshot pending) := .step _ _ rfl

/-- The exact bound-snapshot event reconstructs the child record, with no new
saved-source or successor-admission premise. -/
theorem outer_entry_source (pending : SourceBoundSnapshots.Retained [] whole) :
    ∃ child : UseReceiverBody [(effectE, 0)] [] context cut caller installed (outerSnapshot pending).current,
      outerSnapshot pending = ⟨_, (outerSnapshot pending).plan, child.source.body.boundAnnotation,
        _, _, installed, .handler pending⟩ :=
  root.at_receiver.handler_entered pending (outer_entry pending)

/-- Handler descent composes with a prior neutral restoration path. Both
handler entries still derive their child records from the one parent. -/
theorem after_restoration : ∃ annotation : Code [] (.invoke (key := ⟨19, .resume⟩))
    (.handler (effect := effectE) (table := SourceDependencyCapture.Examples.resumeTable)
      (families := SourceDependencyCapture.Examples.resumeDependencies) (required := [])
      (.handler (effect := effectE) (table := []) (families := []) (required := [])
        (.spent (owner := 73) whole))),
    annotation.Valid [] actions phases ∧ SourcePlanBounds.ofCode annotation = Annotation.absent :=
  ((root.at_receiver.expand (.history (owner := 73) .refl)).handler_body.handler_body).generate
    (recipeLaws []) (fun evidence => evidence)

end HandlerEntry

end Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.bounded
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.nested
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.inner_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.intermediate_mask
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.queued_generated
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.focused
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.current_focus
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.current_child_valid
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.returned_source

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.cut

#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.canonical_generated
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.canonical_return
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.Records.capture
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.Records.resume_records
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.Records.captured_source_values
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.Records.restored_source_values
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.Records.recovered_exact
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.Records.restored_generation
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.Records.restored_return
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.Records.restored_twice
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.Records.restored_current_focus
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.Transport.permissions
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.Transport.availability
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.Transport.generated
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.Transport.returned
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.Transport.outside_retirement_rejected
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.HandlerEntry.outer_body
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.HandlerEntry.outer_generated
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.HandlerEntry.inner_generated
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.HandlerEntry.outer_entry
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.HandlerEntry.outer_entry_source
#print axioms Ash.OneShot.SourceConsumingCleanupAdmission.UseQueuedExamples.HandlerEntry.after_restoration
