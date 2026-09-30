import SourceAnnotatedClosingPlans
import SourceAnnotatedCaptureIdentity

/-! The generic allocator carries annotated closing evidence at the existing
raw plan indices. Its witness retains the actual callback syntax and source;
erasure supplies the older certificate from that same witness. -/
namespace Ash.OneShot.SourceAnnotatedClosingData
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Contracts)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest closingForest)
open SourceAnnotatedClosingPlans (Plans Template)
open RecursiveRequirements (Requirements)
open OwnerClosingSource (retirements)
abbrev Receiving := SourceDependencyCapture.Scope

inductive ErasedCertificate (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (world : List Nat) : (plan : List CloseEntry) →
    {captured : Receiving} → {hints : Hints captured} → Forest hints →
    Footprint → Requirements (retirements plan) → Prop where
  | checked {plans : Plans annotated (SourceContextualInvocationHints.forClosing hints)}
      (template : Template operations policy contracts tables world .none plans raw requirements)
      (same : closingForest plans.erase = saved.forClosing) :
      ErasedCertificate operations policy contracts tables world (annotated.map SourceAnnotatedRuntime.CloseEntry.erase) saved raw requirements


inductive Certificate (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (world : List Nat) (capture : SourceAnnotatedRuntime.Stack) : (plan : List CloseEntry) →
    {captured : Receiving} → {hints : Hints captured} → Forest hints →
    Footprint → Requirements (retirements plan) → Prop where
  | checked {plans : Plans annotated (SourceContextualInvocationHints.forClosing hints)}
      (built : SourceAnnotatedRuntime.makePlan capture = some annotated)
      (template : Template operations policy contracts tables world .none plans raw requirements)
      (same : closingForest plans.erase = saved.forClosing) :
      Certificate operations policy contracts tables world capture (annotated.map SourceAnnotatedRuntime.CloseEntry.erase) saved raw requirements

theorem Certificate.erase {hints : Hints captured} {saved : Forest hints}
    (certificate : Certificate operations policy contracts tables world capture plan saved raw requirements) :
    SourceScheduledClosingData.Certificate operations policy contracts tables world plan saved raw requirements := by
  cases certificate with
  | checked built template same => exact ⟨_, template.erase, same⟩

theorem Certificate.transport
    (certificate : Certificate operations policy contracts tables world capture plan saved raw requirements)
    (extension : contracts.Extends nextContracts) :
    Certificate operations policy nextContracts tables world capture plan saved raw requirements := by
  cases certificate with
  | checked built template same => exact .checked built (template.transport extension) same

theorem Certificate.world_weaken
    (certificate : Certificate operations policy contracts tables world capture plan saved raw requirements)
    (larger : world ⊆ nextWorld) :
    Certificate operations policy contracts tables nextWorld capture plan saved raw requirements := by
  cases certificate with
  | checked built template same => exact .checked built (template.world_weaken larger) same

theorem Certificate.tables_congr
    (certificate : Certificate operations policy contracts tables world capture plan saved raw requirements) :
    Certificate operations policy contracts nextTables world capture plan saved raw requirements := by
  cases certificate with
  | checked built template same => exact .checked built template.tables_congr same

end Ash.OneShot.SourceAnnotatedClosingData

namespace Ash.OneShot.SourceAnnotatedClosingRecords
open ScopedExpressions ScopedExecution
open SourcePlannedTyping (Operations Contracts)
open SourceAnnotatedClosingData (Certificate)
open SourceScheduledSavedPlans (Saved Annotations Matches)
open SourceRetainedPlans (Forest)
open SourceContextualHints (Hints)
open RecursiveRequirements (Store Key Template)
open OwnerClosingSource (retirements)
abbrev Receiving := SourceDependencyCapture.Scope

inductive Certified (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (annotations : Annotations) (world : List Nat) (root : SourceAnnotatedRuntime.Stack) :
    Key → Template → Prop where
  | dispose (saved : Saved) (located : SourceAnnotatedRuntime.CapturedIn owner capture root)
      (built : makePlan capture.erase = some plan) (recorded : annotations owner = some saved)
      (certificate : Certificate operations policy contracts tables world capture plan saved.forest raw requirements) :
      Certified operations policy contracts tables annotations world root ⟨owner, .dispose⟩ ⟨retirements plan, requirements⟩

inductive Records (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (annotations : Annotations) (world : List Nat) (root : SourceAnnotatedRuntime.Stack) : Store → Prop where
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
    SourceScheduledClosingRecords.Records operations policy contracts tables annotations world root.erase entries := by
  induction records with
  | nil => exact .nil
  | cons head tail ih => cases head with
    | dispose saved located built recorded certificate =>
        exact .cons (.dispose saved located.erase built recorded certificate.erase) ih

theorem Records.transport
    (records : Records operations policy contracts tables annotations world root entries)
    (extension : contracts.Extends nextContracts)
    (annotationExtension : ∀ owner captured, annotations owner = some captured → nextAnnotations owner = some captured)
    (locations : ∀ owner capture, SourceAnnotatedRuntime.CapturedIn owner capture root → SourceAnnotatedRuntime.CapturedIn owner capture nextRoot) :
    Records operations policy nextContracts tables nextAnnotations world nextRoot entries := by
  induction records with
  | nil => exact .nil
  | cons head tail ih => cases head with
    | dispose saved located built recorded certificate =>
        exact .cons (.dispose saved (locations _ _ located) built (annotationExtension _ _ recorded)
          (certificate.transport extension)) ih

/-- Capture moves prior certificates into the saved and waiting branches.
This does not require or create a disposal certificate for the new owner. -/
theorem Records.capture_existing {capture : SourceAnnotatedRuntime.Stack} {savedHints : Hints captured} {saved : Forest savedHints}
    (records : Records operations policy contracts tables annotations world whole entries)
    (split : whole = capture.append tail)
    (fresh : annotations owner = none)
    (extension : contracts.Extends nextContracts) :
    Records operations policy nextContracts tables (annotations.insert owner ⟨captured, savedHints, saved⟩) world
      (.live owner inputType answerType capture caller tail) entries := by
  have locations : ∀ other saved, SourceAnnotatedRuntime.CapturedIn other saved whole →
      SourceAnnotatedRuntime.CapturedIn other saved (.live owner inputType answerType capture caller tail) := by
    intro other saved located
    rw [split] at located
    rcases SourceAnnotatedRuntime.located_append.mp located with inside | outside
    · exact .saved inside
    · exact .tail outside
  exact records.transport extension (SourceScheduledSavedPlans.insert_extends fresh) locations

theorem Records.capture {capture : SourceAnnotatedRuntime.Stack} {savedHints : Hints captured} {saved : Forest savedHints}
    (records : Records operations policy contracts tables annotations world whole entries)
    (split : whole = capture.append tail)
    (built : makePlan capture.erase = some plan) (fresh : annotations owner = none)
    (certificate : Certificate operations policy contracts tables world capture plan saved raw requirements)
    (extension : contracts.Extends nextContracts) :
    Records operations policy nextContracts tables (annotations.insert owner ⟨captured, savedHints, saved⟩) world
      (.live owner inputType answerType capture caller tail)
      ((⟨owner, .dispose⟩, ⟨retirements plan, requirements⟩) :: entries) := by
  exact .cons (.dispose ⟨captured, savedHints, saved⟩ .here built (by simp [Annotations.insert]) (certificate.transport extension))
    (records.capture_existing split fresh extension)

/-- Reuse the established post-step layout and origin/uniqueness facts to
retain each exact stronger template. No fresh ticket is allocated by this step. -/
theorem Records.after_step
    (records : Records operations policy contracts tables annotations world root entries)
    (layout : DeclaredSourceClosing.Records operations.erase.erase policy contracts.erase.erase tables world nextRoot.erase retained)
    (included : retained ⊆ entries)
    (origins : ∀ owner capture, SourceAnnotatedRuntime.CapturedIn owner capture nextRoot →
      SourceAnnotatedRuntime.CapturedIn owner capture root)
    (unique : (ownedTickets root.erase).Nodup) :
    Records operations policy contracts tables annotations world nextRoot retained := by
  apply Records.of_members
  intro key body member
  have previous := records.member (included member)
  have current := DeclaredSourceClosing.records_certified layout member
  have locatedNow : ∃ capture, SourceTemplates.CapturedIn key.owner capture nextRoot.erase := by
    cases current with | dispose located built internal template => exact ⟨_, located⟩
  obtain ⟨rawCapture, rawLocated⟩ := locatedNow
  obtain ⟨nextCapture, nextLocated, _⟩ := SourceAnnotatedRuntime.CapturedIn.of_raw rawLocated
  cases previous with
  | dispose saved located built recorded certificate =>
      cases SourceAnnotatedRuntime.captured_in_unique unique located (origins _ _ nextLocated)
      exact .dispose saved nextLocated built recorded certificate

theorem Records.world_weaken
    (records : Records operations policy contracts tables annotations world root entries)
    (larger : world ⊆ nextWorld) :
    Records operations policy contracts tables annotations nextWorld root entries := by
  induction records with
  | nil => exact .nil
  | cons head tail ih => cases head with
    | dispose saved located built recorded certificate =>
        exact .cons (.dispose saved located built recorded (certificate.world_weaken larger)) ih

theorem Records.tables_congr
    (records : Records operations policy contracts tables annotations world root entries) :
    Records operations policy contracts nextTables annotations world root entries := by
  induction records with
  | nil => exact .nil
  | cons head tail ih => cases head with
    | dispose saved located built recorded certificate =>
        exact .cons (.dispose saved located built recorded certificate.tables_congr) ih

end Ash.OneShot.SourceAnnotatedClosingRecords

#print axioms Ash.OneShot.SourceAnnotatedClosingData.Certificate.erase
#print axioms Ash.OneShot.SourceAnnotatedClosingData.Certificate.transport
#print axioms Ash.OneShot.SourceAnnotatedClosingData.Certificate.world_weaken
#print axioms Ash.OneShot.SourceAnnotatedClosingData.Certificate.tables_congr

#print axioms Ash.OneShot.SourceAnnotatedClosingRecords.Records.member
#print axioms Ash.OneShot.SourceAnnotatedClosingRecords.Records.of_members
#print axioms Ash.OneShot.SourceAnnotatedClosingRecords.Records.erase
#print axioms Ash.OneShot.SourceAnnotatedClosingRecords.Records.transport
#print axioms Ash.OneShot.SourceAnnotatedClosingRecords.Records.capture_existing
#print axioms Ash.OneShot.SourceAnnotatedClosingRecords.Records.capture
#print axioms Ash.OneShot.SourceAnnotatedClosingRecords.Records.after_step
#print axioms Ash.OneShot.SourceAnnotatedClosingRecords.Records.world_weaken
#print axioms Ash.OneShot.SourceAnnotatedClosingRecords.Records.tables_congr
