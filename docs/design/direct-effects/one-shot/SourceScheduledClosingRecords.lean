import SourceScheduledClosingData
import SourceScheduledSavedPlans
import SourcePlannedClosingRecords

/-! Disposal records store the template at its exact saved-plan annotation.
Structural agreement with the current forest connects record lookup to the
active continuation. Existing raw capture-origin proofs transport locations. -/
namespace Ash.OneShot.SourceScheduledClosingRecords
open ScopedExpressions ScopedExecution
open SourcePlannedTyping (Operations Contracts)
open SourceScheduledClosingData (Certificate)
open SourceScheduledSavedPlans (Saved Annotations Matches)
open SourceRetainedPlans (Forest)
open SourceContextualHints (Hints)
open RecursiveRequirements (Store Key Template)
open OwnerClosingSource (retirements)
abbrev Receiving := SourceDependencyCapture.Scope

inductive Certified (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (annotations : Annotations) (world : List Nat) (root : Stack) :
    Key → Template → Prop where
  | dispose (saved : Saved) (located : SourceTemplates.CapturedIn owner capture root)
      (built : makePlan capture = some plan) (recorded : annotations owner = some saved)
      (certificate : Certificate operations policy contracts tables world plan saved.forest raw requirements) :
      Certified operations policy contracts tables annotations world root ⟨owner, .dispose⟩ ⟨retirements plan, requirements⟩

inductive Records (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (annotations : Annotations) (world : List Nat) (root : Stack) : Store → Prop where
  | nil : Records operations policy contracts tables annotations world root []
  | cons : Certified operations policy contracts tables annotations world root key body →
      Records operations policy contracts tables annotations world root rest →
      Records operations policy contracts tables annotations world root ((key, body) :: rest)

theorem Records.member
    (records : Records operations policy contracts tables annotations world root entries)
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

theorem Records.erase
    (records : Records operations policy contracts tables annotations world root entries) :
    SourcePlannedClosingRecords.Records operations policy contracts tables annotations.scopes world root entries := by
  induction records with
  | nil => exact .nil
  | cons head tail ih => cases head with
    | dispose saved located built recorded certificate =>
        exact .cons (.dispose located built (by simp [Annotations.scopes, recorded]) certificate.erase) ih

theorem Records.transport
    (records : Records operations policy contracts tables annotations world root entries)
    (extension : contracts.Extends nextContracts)
    (annotationExtension : ∀ owner captured, annotations owner = some captured → nextAnnotations owner = some captured)
    (locations : ∀ owner capture, SourceTemplates.CapturedIn owner capture root → SourceTemplates.CapturedIn owner capture nextRoot) :
    Records operations policy nextContracts tables nextAnnotations world nextRoot entries := by
  induction records with
  | nil => exact .nil
  | cons head tail ih => cases head with
    | dispose saved located built recorded certificate =>
        exact .cons (.dispose saved (locations _ _ located) built (annotationExtension _ _ recorded)
          (certificate.transport extension)) ih

/-- Capture moves prior certificates into the saved and waiting branches.
This does not require or create a disposal certificate for the new owner. -/
theorem Records.capture_existing {capture : Stack} {savedHints : Hints captured} {saved : Forest savedHints}
    (records : Records operations policy contracts tables annotations world whole entries)
    (cut : HandlerCut requested whole capture tail handler)
    (fresh : annotations owner = none)
    (extension : contracts.Extends nextContracts) :
    Records operations policy nextContracts tables (annotations.insert owner ⟨captured, savedHints, saved⟩) world
      (.live owner inputType answerType capture caller tail) entries := by
  have locations : ∀ other saved, SourceTemplates.CapturedIn other saved whole →
      SourceTemplates.CapturedIn other saved (.live owner inputType answerType capture caller tail) := by
    intro other saved located
    rw [handler_cut_reconstructs cut] at located
    rcases SavedCaptureIdentity.located_append.mp located with inside | outside
    · exact .saved inside
    · exact .tail outside
  exact records.transport extension (SourceScheduledSavedPlans.insert_extends fresh) locations

theorem Records.capture {capture : Stack} {savedHints : Hints captured} {saved : Forest savedHints}
    (records : Records operations policy contracts tables annotations world whole entries)
    (cut : HandlerCut requested whole capture tail handler)
    (built : makePlan capture = some plan) (fresh : annotations owner = none)
    (certificate : Certificate operations policy contracts tables world plan saved raw requirements)
    (extension : contracts.Extends nextContracts) :
    Records operations policy nextContracts tables (annotations.insert owner ⟨captured, savedHints, saved⟩) world
      (.live owner inputType answerType capture caller tail)
      ((⟨owner, .dispose⟩, ⟨retirements plan, requirements⟩) :: entries) := by
  exact .cons (.dispose ⟨captured, savedHints, saved⟩ .here built (by simp [Annotations.insert]) (certificate.transport extension))
    (records.capture_existing cut fresh extension)

/-- Reuse the established post-step layout and origin/uniqueness facts to
retain each exact stronger template. No fresh ticket is allocated by this step. -/
theorem Records.after_step
    (records : Records operations policy contracts tables annotations world before.stack entries)
    (layout : DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world after.stack retained)
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
    cases current with | dispose located built internal template => exact ⟨_, located⟩
  obtain ⟨nextCapture, nextLocated⟩ := locatedNow
  cases previous with
  | dispose saved located built recorded certificate =>
      have origin := SavedCaptureIdentity.raw_step_origin step (old _) nextLocated
      cases SourceTemplates.captured_in_unique unique located origin
      exact .dispose saved nextLocated built recorded certificate

/-- Lookup returns the template at the exact forest selected by the active
owner cut, rather than another plan with equal erased dependencies. -/
theorem selected_template {hints : Hints scope} {forest : Forest hints}
    {savedHints : Hints captured} {saved : Forest savedHints}
    (source : SourceScheduledFrames.Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements resumes forest outside incoming outgoing)
    (closing : Records operations policy contracts tables annotations world stack disposals)
    (matched : Matches annotations forest)
    (cut : SourceScheduledNeutral.OwnerCut owner forest front saved tail)
    (looked : RecursiveRequirements.lookup ⟨owner, .dispose⟩ (resumes ++ disposals) = some body)
    (unique : (ownedTickets stack).Nodup)
    (located : SourceTemplates.CapturedIn owner capture stack) :
    ∃ (plan : List CloseEntry) (raw : ProtectionContracts.Footprint)
      (requirements : RecursiveRequirements.Requirements (retirements plan)),
      makePlan capture = some plan ∧ body = ⟨retirements plan, requirements⟩ ∧
      Certificate operations policy contracts tables world plan saved raw requirements := by
  rcases List.mem_append.mp (SourceTemplates.lookup_member looked) with resume | disposal
  · have impossible := RecursiveRecords.resume_mode source.source.source.erase.erase.source.erase resume
    cases impossible
  · cases closing.member disposal with
    | dispose stored actual built recorded certificate =>
        cases SourceTemplates.captured_in_unique unique actual located
        have same := Option.some.inj (recorded.symm.trans (matched.selected cut))
        cases same
        exact ⟨_, _, _, built, rfl, certificate⟩

/-- The requirement body actually returned by lookup has the scheduling check
needed to run its stored callbacks in the recomposed disposal context. -/
theorem selected_checked {hints : Hints scope} {forest : Forest hints}
    {frontHints : Hints frontScope} {savedHints : Hints captured} {tailHints : Hints tailScope}
    {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
    (source : SourceScheduledFrames.Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements resumes forest outside incoming outgoing)
    (closing : Records operations policy contracts tables annotations world stack disposals)
    (matched : Matches annotations forest)
    (cut : SourceScheduledNeutral.OwnerCut owner forest front saved tail)
    (dispose : SourceScheduledChecks.Local outward actions phases world (.invoke (key := ⟨owner, .dispose⟩)) forest)
    (looked : RecursiveRequirements.lookup ⟨owner, .dispose⟩ (resumes ++ disposals) = some body)
    (unique : (ownedTickets stack).Nodup)
    (located : SourceTemplates.CapturedIn owner capture stack) :
    ∃ (plan : List CloseEntry) (raw : ProtectionContracts.Footprint)
      (requirements : RecursiveRequirements.Requirements (retirements plan)),
    ∃ plans : SourcePlannedClosingPlans.Plans plan (SourceContextualInvocationHints.forClosing savedHints),
      makePlan capture = some plan ∧ body = ⟨retirements plan, requirements⟩ ∧
      SourcePlannedClosingPlans.Template operations policy contracts tables world .none plans raw requirements ∧
      SourceRetainedPlans.closingForest plans = saved.forClosing ∧
      SourcePlannedClosingPlans.Checked outward actions (OwnerPhaseTransitions.spend phases owner) world
        (.running (frontHints.append (.spent (owner := owner) tailHints))) plans := by
  obtain ⟨plan, raw, requirements, built, bodySame, certificate⟩ :=
    selected_template source closing matched cut looked unique located
  obtain ⟨plans, template, same, checked⟩ := certificate.dispose_checked dispose cut.found cut.forest
  exact ⟨plan, raw, requirements, plans, built, bodySame, template, same, checked⟩

end Ash.OneShot.SourceScheduledClosingRecords

#print axioms Ash.OneShot.SourceScheduledClosingRecords.Records.erase
#print axioms Ash.OneShot.SourceScheduledClosingRecords.Records.transport
#print axioms Ash.OneShot.SourceScheduledClosingRecords.Records.capture

#print axioms Ash.OneShot.SourceScheduledClosingRecords.Records.member
#print axioms Ash.OneShot.SourceScheduledClosingRecords.Records.of_members
#print axioms Ash.OneShot.SourceScheduledClosingRecords.Records.after_step
#print axioms Ash.OneShot.SourceScheduledClosingRecords.selected_template

#print axioms Ash.OneShot.SourceScheduledClosingRecords.selected_checked

#print axioms Ash.OneShot.SourceScheduledClosingRecords.Records.capture_existing
