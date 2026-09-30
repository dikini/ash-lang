import SourcePlannedClosingAllocationData

/-! Disposal records retain the actual planned closing template and its exact
stored requirement body. Existing capture-location equations transport older
records; no new ownership or allocation semantics are introduced. -/
namespace Ash.OneShot.SourcePlannedClosingRecords
open ScopedExpressions ScopedExecution
open SourcePlannedTyping (Operations Contracts)
open SourcePlannedClosingAllocationData (Certificate)
open RecursiveRequirements (Store Key Template)
open OwnerClosingSource (retirements)
abbrev Receiving := SourceDependencyCapture.Scope

inductive Certified (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (annotations : Nat → Option Receiving) (world : List Nat) (root : Stack) :
    Key → Template → Prop where
  | dispose (located : SourceTemplates.CapturedIn owner capture root)
      (built : makePlan capture = some plan) (recorded : annotations owner = some captured)
      (certificate : Certificate operations policy contracts tables world plan captured raw requirements) :
      Certified operations policy contracts tables annotations world root ⟨owner, .dispose⟩ ⟨retirements plan, requirements⟩

inductive Records (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (annotations : Nat → Option Receiving) (world : List Nat) (root : Stack) : Store → Prop where
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
    SourceDependencySchemes.Closing.Records operations.erase policy contracts.erase tables annotations world root entries := by
  induction records with
  | nil => exact .nil
  | cons head tail ih => cases head with
    | dispose located built recorded certificate =>
        obtain ⟨hints, plans, template⟩ := certificate
        exact .cons (.dispose located built recorded template.erase) ih

theorem Records.transport
    (records : Records operations policy contracts tables annotations world root entries)
    (extension : contracts.Extends nextContracts)
    (annotationExtension : ∀ owner captured, annotations owner = some captured → nextAnnotations owner = some captured)
    (locations : ∀ owner capture, SourceTemplates.CapturedIn owner capture root → SourceTemplates.CapturedIn owner capture nextRoot) :
    Records operations policy nextContracts tables nextAnnotations world nextRoot entries := by
  induction records with
  | nil => exact .nil
  | cons head tail ih => cases head with
    | dispose located built recorded certificate =>
        exact .cons (.dispose (locations _ _ located) built (annotationExtension _ _ recorded)
          (certificate.transport extension)) ih

theorem Records.capture {capture : Stack}
    (records : Records operations policy contracts tables annotations world whole entries)
    (cut : HandlerCut requested whole capture tail handler)
    (built : makePlan capture = some plan) (fresh : annotations owner = none)
    (certificate : Certificate operations policy contracts tables world plan captured raw requirements)
    (extension : contracts.Extends nextContracts) :
    Records operations policy nextContracts tables (fun other => if other = owner then some captured else annotations other) world
      (.live owner inputType answerType capture caller tail)
      ((⟨owner, .dispose⟩, ⟨retirements plan, requirements⟩) :: entries) := by
  have annotationExtension : ∀ other saved, annotations other = some saved →
      (if other = owner then some captured else annotations other) = some saved := by
    intro other saved known
    by_cases same : other = owner
    · subst other; rw [fresh] at known; cases known
    · simpa only [if_neg same] using known
  have locations : ∀ other saved, SourceTemplates.CapturedIn other saved whole →
      SourceTemplates.CapturedIn other saved (.live owner inputType answerType capture caller tail) := by
    intro other saved located
    rw [handler_cut_reconstructs cut] at located
    rcases SavedCaptureIdentity.located_append.mp located with inside | outside
    · exact .saved inside
    · exact .tail outside
  exact .cons (.dispose .here built (by simp) (certificate.transport extension))
    (records.transport extension annotationExtension locations)

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
  | dispose located built recorded certificate =>
      have origin := SavedCaptureIdentity.raw_step_origin step (old _) nextLocated
      cases SourceTemplates.captured_in_unique unique located origin
      exact .dispose nextLocated built recorded certificate

/-- Select the stronger template for the exact record evaluated by lookup. -/
theorem selected_template
    (source : SourcePlannedCheckedFrames.Segment operations policy contracts tables families required actions outward phases world
      stack input output demand requirements resumes hints outside incoming outgoing)
    (closing : Records operations policy contracts tables annotations world stack disposals)
    (looked : RecursiveRequirements.lookup ⟨owner, .dispose⟩ (resumes ++ disposals) = some body)
    (unique : (ownedTickets stack).Nodup)
    (located : SourceTemplates.CapturedIn owner capture stack) :
    ∃ (plan : List CloseEntry) (raw : ProtectionContracts.Footprint)
      (requirements : RecursiveRequirements.Requirements (retirements plan)) (captured : Receiving),
      makePlan capture = some plan ∧ body = ⟨retirements plan, requirements⟩ ∧
      annotations owner = some captured ∧ Certificate operations policy contracts tables world plan captured raw requirements := by
  rcases List.mem_append.mp (SourceTemplates.lookup_member looked) with resume | disposal
  · have impossible := RecursiveRecords.resume_mode source.source.erase.erase.source.erase resume
    cases impossible
  · cases closing.member disposal with
    | dispose actual built recorded certificate =>
        cases SourceTemplates.captured_in_unique unique actual located
        exact ⟨_, _, _, _, built, rfl, recorded, certificate⟩

end Ash.OneShot.SourcePlannedClosingRecords

#print axioms Ash.OneShot.SourcePlannedClosingRecords.Records.erase
#print axioms Ash.OneShot.SourcePlannedClosingRecords.Records.transport
#print axioms Ash.OneShot.SourcePlannedClosingRecords.Records.capture

#print axioms Ash.OneShot.SourcePlannedClosingRecords.Records.member
#print axioms Ash.OneShot.SourcePlannedClosingRecords.Records.of_members
#print axioms Ash.OneShot.SourcePlannedClosingRecords.Records.after_step
#print axioms Ash.OneShot.SourcePlannedClosingRecords.selected_template
