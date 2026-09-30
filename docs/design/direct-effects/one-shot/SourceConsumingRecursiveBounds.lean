import SourceConsumingReinterpretationBounds

/-! Finite operation bounds across arbitrarily nested one-shot resumptions.
The source forest retains each continuation and invokes it from pending code.
The annotation generator and proof recurse on that finite source; scheduling
and owner consumption use the existing capability compiler. This is the
resumption-chain case, not general recursive consuming-clause admission. -/
namespace Ash.OneShot.SourceConsumingRecursiveBounds
open SourceContextualHints (Hints Requirement checkRequirements)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledCapabilityAnnotations (Code Retained)
open SourceConsumingClauseAnnotations (Bounds)
open OwnerPhaseTransitions (Phases spend)

def chainScope (owners : List Nat) (terminal : Scope) : Scope :=
  match owners with
  | [] => terminal
  | owner :: rest => .plain (.sequence .pure (.invoke ⟨owner, .resume⟩)) (.live owner (chainScope rest terminal) .nil)

def chainHints (owners : List Nat) (terminal : Hints scope) : Hints (chainScope owners scope) :=
  match owners with
  | [] => terminal
  | _ :: rest => .plain (.live (chainHints rest terminal) .nil)

def chain (owners : List Nat) {hints : Hints scope} (terminal : Forest hints) :
    Forest (chainHints owners hints) :=
  match owners with
  | [] => terminal
  | _ :: rest => .plain (.sequence .pure .invoke) (.live (chain rest terminal) .nil)

/-- No owner permission or phase proof is needed to construct the annotation.
The same suffix is annotated before consumption and with the owner spent. -/
def annotate (owners : List Nat) {hints : Hints scope} {terminal : Forest hints}
    (source : Interfaces world terminal) {outsideHints : Hints outsideScope}
    {outside : Forest outsideHints} (receiver : Interfaces world outside) :
    Retained world (chain owners terminal) outside :=
  match owners with
  | [] => .operations source
  | owner :: rest =>
      .plain
        (.sequence (.operations [] .pure .pure)
          (.resume .hit (annotate rest source (.spent (owner := owner) receiver))
            (.operations .nil) (.operations receiver)))
        (.live (annotate rest source receiver) (.operations .nil))

private theorem check_spent {hints : Hints scope} {terminal : Forest hints}
    (source : Interfaces world terminal) (checked : source.check outside = true) :
    source.check (.spent owner outside) = true := by
  apply source.check_transport checked
  exact SourceScheduledAdaptationCompilation.requirements_prefix (front := .spent owner .nil)
    (fun _ => rfl) (source.exposed_requirements checked)

/-- Induction is on source depth, not execution length. Spending the selected
owner preserves every distinct remaining owner's availability. Operation
transport across the spent marker reuses the established boundary theorem. -/
theorem annotate_valid (owners : List Nat) {hints : Hints scope} {terminal : Forest hints}
    (source : Interfaces world terminal) {outsideHints : Hints outsideScope}
    {outside : Forest outsideHints} (receiver : Interfaces world outside)
    (unique : owners.Nodup)
    (permissions : ∀ owner ∈ owners, (actions owner).any (fun rights => rights.resume) = true)
    (available : ∀ owner ∈ owners, phases owner = .available)
    (sourceReady : source.check outsideScope = true) (receiverReady : receiver.check .nil = true) :
    (annotate owners source receiver).Valid outward actions phases := by
  induction owners generalizing outsideScope phases with
  | nil => exact sourceReady
  | cons owner rest ih =>
      obtain ⟨fresh, unique⟩ := List.nodup_cons.mp unique
      have restPermissions := fun actual member => permissions actual (List.mem_cons_of_mem owner member)
      have restAvailable := fun actual member => available actual (List.mem_cons_of_mem owner member)
      have spentAvailable : ∀ actual ∈ rest, spend phases owner actual = .available := by
        intro actual member
        have different : actual ≠ owner := by
          intro same
          subst actual
          exact fresh member
        simpa only [spend, if_neg different] using restAvailable actual member
      exact ⟨⟨rfl, ⟨permissions owner List.mem_cons_self, available owner List.mem_cons_self,
          ih (.spent receiver) unique restPermissions spentAvailable (check_spent source sourceReady) receiverReady,
          rfl, receiverReady⟩⟩,
        ih receiver unique restPermissions restAvailable sourceReady receiverReady, rfl⟩

/-- Validation recovers the terminal interface and every separate capability
condition. A repeated owner fails in the recursively checked spent phase. -/
theorem annotate_facts (owners : List Nat) {hints : Hints scope} {terminal : Forest hints}
    (source : Interfaces world terminal) {outsideHints : Hints outsideScope}
    {outside : Forest outsideHints} (receiver : Interfaces world outside)
    (checked : (annotate owners source receiver).Valid outward actions phases) :
    source.check outsideScope = true ∧ owners.Nodup ∧
      (∀ owner ∈ owners, (actions owner).any (fun rights => rights.resume) = true ∧ phases owner = .available) ∧
      (owners ≠ [] → receiver.check .nil = true) := by
  induction owners generalizing outsideScope phases with
  | nil => exact ⟨checked, List.nodup_nil, by simp, by simp⟩
  | cons owner rest ih =>
      obtain ⟨⟨_, ⟨permission, available, resumed, _, receiverReady⟩⟩, dormant, _⟩ := checked
      obtain ⟨sourceReady, unique, remaining, _⟩ := ih receiver dormant
      have consumed := (ih (.spent receiver) resumed).2.2.1
      have fresh : owner ∉ rest := by
        intro member
        have impossible := (consumed owner member).2
        simp [spend] at impossible
      refine ⟨sourceReady, List.nodup_cons.mpr ⟨fresh, unique⟩, ?_, fun _ => receiverReady⟩
      intro actual member
      rcases List.mem_cons.mp member with same | member
      · subst actual
        exact ⟨permission, available⟩
      · exact remaining actual member

/-- Exact factorization: recursive depth changes the owner checks but adds
no operation requirement beyond the terminal source and actual receiver. -/
theorem annotate_valid_iff (owners : List Nat) {hints : Hints scope} {terminal : Forest hints}
    (source : Interfaces world terminal) {outsideHints : Hints outsideScope}
    {outside : Forest outsideHints} (receiver : Interfaces world outside) :
    (annotate owners source receiver).Valid outward actions phases ↔
      source.check outsideScope = true ∧ owners.Nodup ∧
        (∀ owner ∈ owners, (actions owner).any (fun rights => rights.resume) = true ∧ phases owner = .available) ∧
        (owners ≠ [] → receiver.check .nil = true) := by
  refine ⟨annotate_facts owners source receiver, ?_⟩
  intro ⟨sourceReady, unique, capabilities, receiverReady⟩
  cases owners with
  | nil => exact sourceReady
  | cons owner rest =>
      exact annotate_valid _ source receiver unique
        (fun actual member => (capabilities actual member).1)
        (fun actual member => (capabilities actual member).2) sourceReady (receiverReady (by simp))

/-- Reuse the established owner trace theorem for the complete recursive
consumption order. This statement concerns phase accounting, not termination. -/
theorem annotate_trace (owners : List Nat) {hints : Hints scope} {terminal : Forest hints}
    (source : Interfaces world terminal) {outsideHints : Hints outsideScope}
    {outside : Forest outsideHints} (receiver : Interfaces world outside)
    (checked : (annotate owners source receiver).Valid outward actions phases) :
    OwnerPhaseTransitions.Trace phases owners (OwnerPhaseTransitions.spendAll phases owners) := by
  have facts := annotate_facts owners source receiver checked
  exact OwnerPhaseTransitions.trace_of_available facts.2.1 (fun owner member => (facts.2.2.1 owner member).2)

/-- Allocating a fresh outer continuation leaves the recursive source's
existing capabilities unchanged. Freshness is independent of operation bounds. -/
theorem annotate_fresh_owner (owners : List Nat) {hints : Hints scope} {terminal : Forest hints}
    (source : Interfaces world terminal) {outsideHints : Hints outsideScope}
    {outside : Forest outsideHints} (receiver : Interfaces world outside)
    (checked : (annotate owners source receiver).Valid outward actions phases)
    (fresh : owner ∉ owners) :
    (annotate owners source receiver).Valid outward (actions.insert owner rights)
      (OwnerPhaseTransitions.introduce phases owner) := by
  obtain ⟨sourceReady, unique, capabilities, receiverReady⟩ := annotate_facts owners source receiver checked
  apply (annotate_valid_iff owners source receiver).mpr
  refine ⟨sourceReady, unique, ?_, receiverReady⟩
  intro actual member
  have different : actual ≠ owner := fun same => fresh (same ▸ member)
  simpa only [Syntax.UsageTickets.insert, OwnerPhaseTransitions.introduce, if_neg different] using capabilities actual member

/-- A finite bound authenticates all operation requirements reached through
the recursive calls. The premises contain the original terminal check and a
finite replacement-receiver check, never a successful future chain schedule. -/
theorem annotate_valid_from_bound (owners : List Nat) {hints : Hints scope} {terminal : Forest hints}
    (source : Interfaces world terminal) {outsideHints : Hints outsideScope}
    {outside : Forest outsideHints} (receiver : Interfaces world outside)
    (unique : owners.Nodup)
    (permissions : ∀ owner ∈ owners, (actions owner).any (fun rights => rights.resume) = true)
    (available : ∀ owner ∈ owners, phases owner = .available)
    (original : source.check originalOutside = true) (bounded : source.exposed ⊆ required)
    (supplied : checkRequirements outsideScope required = true) (receiverReady : receiver.check .nil = true) :
    (annotate owners source receiver).Valid outward actions phases :=
  annotate_valid owners source receiver unique permissions available
    (source.check_from_bound original bounded supplied) receiverReady

/-- The generated recursive source reaches the same scheduling judgment and
therefore the existing one-shot recomposition machinery. -/
theorem schedule_from_bound (owners : List Nat) {hints : Hints scope} {terminal : Forest hints}
    (source : Interfaces world terminal) {outsideHints : Hints outsideScope}
    {outside : Forest outsideHints} (receiver : Interfaces world outside)
    (unique : owners.Nodup)
    (permissions : ∀ owner ∈ owners, (actions owner).any (fun rights => rights.resume) = true)
    (available : ∀ owner ∈ owners, phases owner = .available)
    (original : source.check originalOutside = true) (bounded : source.exposed ⊆ required)
    (supplied : checkRequirements outsideScope required = true) (receiverReady : receiver.check .nil = true) :
    SourceScheduledChecks.Pending outward actions phases world (chain owners terminal) outside :=
  (annotate owners source receiver).compile
    (annotate_valid_from_bound owners source receiver unique permissions available original bounded supplied receiverReady)

/-- A repeated capability cannot be rescued by any operation bound or
receiver. This follows from the existing phase checks in the annotation. -/
theorem repeated_owner_rejected {hints : Hints scope} {terminal : Forest hints}
    (source : Interfaces world terminal) {outsideHints : Hints outsideScope}
    {outside : Forest outsideHints} (receiver : Interfaces world outside) :
    ¬ (annotate [owner, owner] source receiver).Valid outward actions phases := by
  intro checked
  have unique := (annotate_facts _ source receiver checked).2.1
  simp at unique

/-- Keep an actual captured suffix after the recursive prefix. In particular,
the selected handler remains on the active spine of a physical capture. -/
def annotateSuffix (owners : List Nat) {hints : Hints scope} {terminal : Forest hints}
    (source : Interfaces world terminal) {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
    (retained : Interfaces world suffix) {outsideHints : Hints outsideScope}
    {outside : Forest outsideHints} (receiver : Interfaces world outside) :
    Retained world ((chain owners terminal).append suffix) outside :=
  match owners with
  | [] => .operations (source.append retained)
  | owner :: rest =>
      .plain
        (.sequence (.operations [] .pure .pure)
          (.resume .hit (annotate rest source (.spent (owner := owner) (retained.append receiver)))
            (.operations .nil) (.operations (retained.append receiver))))
        (.live (annotate rest source (retained.append receiver)) (.operations retained))

theorem annotateSuffix_valid (owners : List Nat) {hints : Hints scope} {terminal : Forest hints}
    (source : Interfaces world terminal) {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
    (retained : Interfaces world suffix) {outsideHints : Hints outsideScope}
    {outside : Forest outsideHints} (receiver : Interfaces world outside)
    (checked : (annotate owners source (retained.append receiver)).Valid outward actions phases)
    (suffixReady : retained.check outsideScope = true) :
    (annotateSuffix owners source retained receiver).Valid outward actions phases := by
  cases owners with
  | nil => exact (source.check_append retained).trans (Bool.and_eq_true_iff.mpr ⟨checked, suffixReady⟩)
  | cons owner rest => exact ⟨checked.1, checked.2.1, suffixReady⟩

theorem annotateSuffix_facts (owners : List Nat) {hints : Hints scope} {terminal : Forest hints}
    (source : Interfaces world terminal) {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
    (retained : Interfaces world suffix) {outsideHints : Hints outsideScope}
    {outside : Forest outsideHints} (receiver : Interfaces world outside)
    (checked : (annotateSuffix owners source retained receiver).Valid outward actions phases) :
    (source.append retained).check outsideScope = true ∧ owners.Nodup ∧
      (∀ owner ∈ owners, (actions owner).any (fun rights => rights.resume) = true ∧ phases owner = .available) := by
  cases owners with
  | nil => exact ⟨checked, List.nodup_nil, by simp⟩
  | cons owner rest =>
      have original : (annotate (owner :: rest) source (retained.append receiver)).Valid outward actions phases :=
        ⟨checked.1, checked.2.1, rfl⟩
      have facts := annotate_facts _ source _ original
      exact ⟨(source.check_append retained).trans (Bool.and_eq_true_iff.mpr ⟨facts.1, checked.2.2⟩),
        facts.2.1, facts.2.2.1⟩

theorem annotateSuffix_fresh_owner (owners : List Nat) {hints : Hints scope} {terminal : Forest hints}
    (source : Interfaces world terminal) {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
    (retained : Interfaces world suffix) {outsideHints : Hints outsideScope}
    {outside : Forest outsideHints} (receiver : Interfaces world outside)
    (checked : (annotateSuffix owners source retained receiver).Valid outward actions phases)
    (fresh : owner ∉ owners) :
    (annotateSuffix owners source retained receiver).Valid outward (actions.insert owner rights)
      (OwnerPhaseTransitions.introduce phases owner) := by
  cases owners with
  | nil => exact checked
  | cons first rest =>
      have original : (annotate (first :: rest) source (retained.append receiver)).Valid outward actions phases :=
        ⟨checked.1, checked.2.1, rfl⟩
      exact annotateSuffix_valid _ source retained receiver
        (annotate_fresh_owner _ source _ original fresh) checked.2.2

theorem annotateSuffix_valid_from_bound (owners : List Nat) {hints : Hints scope} {terminal : Forest hints}
    (source : Interfaces world terminal) {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
    (retained : Interfaces world suffix) {outsideHints : Hints outsideScope}
    {outside : Forest outsideHints} (receiver : Interfaces world outside)
    (unique : owners.Nodup)
    (permissions : ∀ owner ∈ owners, (actions owner).any (fun rights => rights.resume) = true)
    (available : ∀ owner ∈ owners, phases owner = .available)
    (original : (source.append retained).check originalOutside = true)
    (bounded : (source.append retained).exposed ⊆ required)
    (supplied : checkRequirements outsideScope required = true) (receiverReady : receiver.check .nil = true) :
    (annotateSuffix owners source retained receiver).Valid outward actions phases := by
  have parts := Bool.and_eq_true_iff.mp
    ((source.check_append retained).symm.trans ((source.append retained).check_from_bound original bounded supplied))
  apply annotateSuffix_valid owners source retained receiver _ parts.2
  apply annotate_valid owners source (retained.append receiver) unique permissions available parts.1
  rw [retained.check_append receiver]
  simpa only [SourceDependencyProjection.scope_append_nil] using Bool.and_eq_true_iff.mpr ⟨parts.2, receiverReady⟩

/-- Instantiate an admitted handler-around-resume clause with the actual
recursive captured source. The installed interpretation precedes the waiting
tail at every nested call; the outer owner remains spent throughout. -/
def handlerAnnotation {plans : SourceDeclarationPlans.ClausePlans clauses families}
    (bounds : SourceConsumingClauseAnnotations.ClauseBounds plans)
    (evidence : SourcePlannedRecipeDeclarations.Declarations handlerRequired plans)
    (owners : List Nat) {hints : Hints scope} {terminal : Forest hints}
    (source : Interfaces world terminal) {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
    (retained : Interfaces world suffix) {waitingHints : Hints waitingScope}
    {waiting : Forest waitingHints} (after : Interfaces world waiting) :
    Code world (.handler (effect := effect) (table := table) handlerRequired plans
      (.invoke (key := ⟨owner, .resume⟩))) (.live (owner := owner) ((chain owners terminal).append suffix) waiting) :=
  .handler evidence
    (.resume (.handler .hit)
      (annotateSuffix owners source retained (.handler _ (.spent after)))
      (.operations (.handler .nil .nil)) (.operations after)) (some bounds)

/-- The existing structural clause judgment supplies the finite caller check.
The original recursive annotation supplies the nested permissions and phases;
freshness of the new owner keeps those permissions available after its use. -/
theorem handlerAnnotation_valid
    {plans : SourceDeclarationPlans.ClausePlans clauses families}
    {bounds : SourceConsumingClauseAnnotations.ClauseBounds plans}
    {evidence : SourcePlannedRecipeDeclarations.Declarations handlerRequired plans}
    (admitted : SourceConsumingClauseAnnotations.Admitted rights resumeRequired closeRequired
      (SourceConsumingClauseAnnotations.Body.handler (effect := effect) (table := table) bounds evidence
        (SourceConsumingClauseAnnotations.Body.resume (world := world) (owner := owner))) required)
    (owners : List Nat) {hints : Hints scope} {terminal : Forest hints}
    (source : Interfaces world terminal) {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
    (retained : Interfaces world suffix) {waitingHints : Hints waitingScope}
    {waiting : Forest waitingHints} (after : Interfaces world waiting)
    {originalHints : Hints originalScope} {original : Forest originalHints}
    (oldReceiver : Interfaces world original)
    (originalReady : (annotateSuffix owners source retained oldReceiver).Valid outward actions phases)
    (fresh : owner ∉ owners) (known : actions owner = some rights) (available : phases owner = .available)
    (bounded : (source.append retained).exposed ⊆ resumeRequired)
    (supplied : checkRequirements waitingScope required = true) (afterReady : after.check .nil = true) :
    (handlerAnnotation (effect := effect) (table := table) (owner := owner) bounds evidence owners source retained after).Valid
      outward actions phases := by
  obtain ⟨sourceReady, unique, capabilities⟩ := annotateSuffix_facts owners source retained oldReceiver originalReady
  have contract := admitted.at_capture (captured := (chainScope owners scope).append suffixScope) known available supplied
  obtain ⟨installed, permission, ready, resumeSupplied, callerReady⟩ := contract
  refine ⟨installed, permission, ready, ?_, callerReady, afterReady⟩
  refine annotateSuffix_valid_from_bound owners source retained _ unique
    (fun actual member => (capabilities actual member).1) ?_ sourceReady bounded resumeSupplied ?_
  · intro actual member
    have different : actual ≠ owner := fun same => fresh (same ▸ member)
    exact (OwnerPhaseTransitions.spend_other different).trans (capabilities actual member).2
  · apply Bool.and_eq_true_iff.mpr
    refine ⟨?_, afterReady⟩
    change checkRequirements ((Scope.spent owner waitingScope).append .nil) handlerRequired = true
    have installedOutside : checkRequirements (Scope.spent owner waitingScope) handlerRequired = true :=
      (Bool.and_eq_true_iff.mp callerReady).1
    simpa only [SourceDependencyProjection.scope_append_nil] using installedOutside

/-- Recursive capture reaches the existing scheduler and the exact selected
mode's finite resume bound. Both follow from original source evidence and the
structural clause judgment, with no future-body success premise. -/
theorem handler_schedule_and_bound
    {plans : SourceDeclarationPlans.ClausePlans clauses families}
    {bounds : SourceConsumingClauseAnnotations.ClauseBounds plans}
    {evidence : SourcePlannedRecipeDeclarations.Declarations handlerRequired plans}
    (admitted : SourceConsumingClauseAnnotations.Admitted rights resumeRequired closeRequired
      (SourceConsumingClauseAnnotations.Body.handler (effect := effect) (table := table) bounds evidence
        (SourceConsumingClauseAnnotations.Body.resume (world := world) (owner := owner))) required)
    (owners : List Nat) {hints : Hints scope} {terminal : Forest hints}
    (source : Interfaces world terminal) {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
    (retained : Interfaces world suffix) {waitingHints : Hints waitingScope}
    {waiting : Forest waitingHints} (after : Interfaces world waiting)
    {originalHints : Hints originalScope} {original : Forest originalHints}
    (oldReceiver : Interfaces world original)
    (originalReady : (annotateSuffix owners source retained oldReceiver).Valid outward actions phases)
    (fresh : owner ∉ owners) (known : actions owner = some rights) (available : phases owner = .available)
    (bounded : (source.append retained).exposed ⊆ resumeRequired)
    (supplied : checkRequirements waitingScope required = true) (afterReady : after.check .nil = true)
    (found : bounds.lookup operation held = some selected) :
    SourceScheduledChecks.Local outward actions phases world
        (.handler (effect := effect) (table := table) handlerRequired plans (.invoke (key := ⟨owner, .resume⟩)))
        (.live (owner := owner) ((chain owners terminal).append suffix) waiting) ∧
      selected.check ⟨true, false⟩
        ((source.append retained).append (Interfaces.handler (effect := effect) (table := table) (families := families)
          (required := handlerRequired) .nil .nil)).exposed closing = true :=
  ⟨(handlerAnnotation bounds evidence owners source retained after).compile
      (handlerAnnotation_valid admitted owners source retained after oldReceiver originalReady fresh known available
        bounded supplied afterReady),
    admitted.handler_resume_recomposition found (source.append retained) bounded⟩

/-- The value operand of a source resume contributes a pure prefix before
the primitive invocation. Retain that plan shape at the allocator boundary. -/
def valueHandlerAnnotation {plans : SourceDeclarationPlans.ClausePlans clauses families}
    (bounds : SourceConsumingClauseAnnotations.ClauseBounds plans)
    (evidence : SourcePlannedRecipeDeclarations.Declarations handlerRequired plans)
    (owners : List Nat) {hints : Hints scope} {terminal : Forest hints}
    (source : Interfaces world terminal) {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
    (retained : Interfaces world suffix) {waitingHints : Hints waitingScope}
    {waiting : Forest waitingHints} (after : Interfaces world waiting) :
    Code world (.handler (effect := effect) (table := table) handlerRequired plans
      (.sequence .pure (.invoke (key := ⟨owner, .resume⟩))))
      (.live (owner := owner) ((chain owners terminal).append suffix) waiting) :=
  .handler evidence (.sequence (.operations [] .pure .pure)
    (.resume (.handler .hit)
      (annotateSuffix owners source retained (.handler _ (.spent after)))
      (.operations (.handler .nil .nil)) (.operations after))) (some bounds)

/-- An actual selected clause and physical capture cut receive the generated
recursive annotation. The existing allocator API accepts this certificate;
no operation-only interface for the captured invocation chain is required. -/
theorem capture_annotation
    {handlerPlans : SourceDeclarationPlans.ClausePlans handlerClauses handlerFamilies}
    {bounds : SourceConsumingClauseAnnotations.ClauseBounds handlerPlans}
    {evidence : SourcePlannedRecipeDeclarations.Declarations handlerRequired handlerPlans}
    (admitted : SourceConsumingClauseAnnotations.Admitted code.requiredActions resumeRequired closeRequired
      (SourceConsumingClauseAnnotations.Body.handler (effect := installed) (table := table) bounds evidence
        (SourceConsumingClauseAnnotations.Body.resume (world := world) (owner := owner))) required)
    (owners : List Nat) {hints : Hints scope} {terminal : Forest hints}
    (source : Interfaces world terminal) {suffixHints : Hints suffixScope} {suffix : Forest suffixHints}
    (retained : Interfaces world suffix) {waitingHints : Hints waitingScope}
    {waiting : Forest waitingHints} (after : Interfaces world waiting)
    {originalHints : Hints originalScope} {original : Forest originalHints}
    (oldReceiver : Interfaces world original)
    (originalReady : (annotateSuffix owners source retained oldReceiver).Valid outward actions phases)
    (fresh : owner ∉ owners) (bounded : (source.append retained).exposed ⊆ resumeRequired)
    (supplied : checkRequirements waitingScope required = true) (afterReady : after.check .nil = true)
    {wholeHints : Hints wholeScope} {whole : Forest wholeHints}
    (cut : SourceScheduledNeutral.Cut effect operation offered modes whole ((chain owners terminal).append suffix) waiting)
    {plans : SourceDeclarationPlans.ClausePlans clauses families}
    (selected : SourcePlannedRecipeDeclarations.Selected operation ((chainScope owners scope).append suffixScope).held
      plans parameter binder code
      (fun actual => .handler (effect := installed) (table := table) handlerRequired handlerPlans
        (.sequence .pure (.invoke (key := ⟨actual, .resume⟩))))) :
    ∃ certificate : SourceScheduledCaptureAnnotations.Capture world owner effect operation offered modes
      plans parameter binder code whole, certificate.Valid outward actions phases := by
  refine ⟨.site cut selected (valueHandlerAnnotation bounds evidence owners source retained after), ?_⟩
  have valid := handlerAnnotation_valid admitted owners source retained after oldReceiver
    (annotateSuffix_fresh_owner (rights := code.requiredActions) owners source retained oldReceiver originalReady fresh) fresh
    (by simp [Syntax.UsageTickets.insert]) (by simp [OwnerPhaseTransitions.introduce])
    bounded supplied afterReady
  exact ⟨valid.1, rfl, valid.2⟩

namespace Examples
open SourceDependencyCapture.Examples (effectF resumeTable)
open SourceScheduledClauseHandlers.Examples (innerFamilies)
open SourceConsumingClauseAnnotations.ReinterpretationExamples (effectG)

def terminalHints : Hints (.plain (.sequence (.request effectF 0) (.request effectG 0)) .nil) := .plain .nil
def terminal : Forest terminalHints := .plain (.sequence .request .request) .nil
def source : Interfaces [] terminal :=
  .plain .nil [(effectF, 0), (effectG, 0)] (.sequence .request .request) (.sequence .request .request) .nil
def callerHints : Hints (.handler effectF resumeTable innerFamilies .nil) := .handler [] .nil
def caller : Forest callerHints := .handler .nil
def callerSource : Interfaces [] caller := .handler .nil .nil
def waitingHints : Hints (.handler effectG resumeTable innerFamilies .nil) := .handler [] .nil
def waiting : Forest waitingHints := .handler .nil
def waitingSource : Interfaces [] waiting := .handler .nil .nil
def receiver : Interfaces [] (caller.append waiting) := callerSource.append waitingSource
def actions : Syntax.UsageTickets := fun _ => some ⟨true, false⟩
def phases : Phases := fun _ => .available

/-- Three nested resumptions use the F interpretation installed at the caller
and the outer G interpretation. Source admission works at any chain depth. -/
theorem nested_reinterpretation :
    (annotate [19, 23, 31] source receiver).Valid [] actions phases := by
  apply annotate_valid_from_bound (originalOutside :=
    .handler effectF resumeTable innerFamilies (.handler effectG resumeTable innerFamilies .nil))
    (required := [(effectF, 0), (effectG, 0)])
  · decide
  · intro owner member
    rfl
  · intro owner member
    rfl
  · rfl
  · exact List.Subset.refl _
  · rfl
  · rfl

/-- The F handler must allow G in a continuation it intercepts, including
when that continuation becomes active through nested resumptions. -/
theorem transitive_bound_checked :
    (Bounds.mk [(effectG, 0)] []).check ⟨true, false⟩ (source.append callerSource).exposed [] = true ∧
      (Bounds.mk [] []).check ⟨true, false⟩ (source.append callerSource).exposed [] = false := ⟨rfl, rfl⟩

theorem missing_transitive_operation_rejected :
    ¬ (annotate [19, 23, 31] source callerSource).Valid [] actions phases := by
  intro checked
  have impossible : false = true := (annotate_facts _ source callerSource checked).1
  cases impossible

theorem denied_nested_permission_rejected :
    ¬ (annotate [19, 23, 31] source receiver).Valid []
      (fun owner => if owner = 23 then some ⟨false, true⟩ else some ⟨true, false⟩) phases := by
  intro checked
  have impossible := ((annotate_facts _ source receiver checked).2.2.1 23 (by decide)).1
  cases impossible

def clauseCode : ScopedExpressions.Code :=
  .handle (Instantiation.freezeEffect effectF) (.resume 9 .unit)
    SourceScheduledClauseHandlers.Examples.innerClauses
def clauseBodies (owner : Nat) := SourceDeclarationPlans.Plan.handler (effect := effectF) (table := resumeTable) []
  SourceScheduledClauseHandlers.Examples.innerPlans (.sequence .pure (.invoke (key := ⟨owner, .resume⟩)))
def clauseFamilies : SourceDependencyAnnotations.ClauseDependencies :=
  [(0, some (fun owner => .handler effectF resumeTable innerFamilies (.sequence .pure (.invoke ⟨owner, .resume⟩))),
    some (fun owner => .handler effectF resumeTable innerFamilies (.sequence .pure (.invoke ⟨owner, .resume⟩))))]
def clauses : ScopedExpressions.Clauses := .cons 0 1 9 clauseCode .nil
def plans : SourceDeclarationPlans.ClausePlans clauses clauseFamilies :=
  .cons (.available clauseBodies) (.available clauseBodies) .nil
def suffixHints : Hints (.handler SourceDependencyCapture.Examples.effectE resumeTable clauseFamilies .nil) :=
  .handler [] .nil
def suffix : Forest suffixHints := .handler .nil
def suffixSource : Interfaces [] suffix := .handler .nil .nil
def captured := (chain [23, 31] terminal).append suffix
def whole := captured.append (caller.append waiting)
def modes : SourcePlannedCuts.Modes := (SourceDependencyCapture.lookupDependencies 0 clauseFamilies).getD (none, none)
def captureActions : Syntax.UsageTickets := fun owner =>
  if owner ∈ [23, 31] then some ⟨true, false⟩ else none
def capturePhases : Phases := OwnerPhaseTransitions.available [23, 31]

theorem fresh_capture_owner : captureActions 19 = none ∧ capturePhases 19 = .consumed := ⟨rfl, rfl⟩

/-- The selected E boundary lies on the active spine after the recursive
prefix. Its dormant continuation contains a further invocation of owner 31. -/
theorem physical_cut : SourceScheduledNeutral.Cut SourceDependencyCapture.Examples.effectE 0
    ⟨false, some [], some []⟩ modes whole captured (caller.append waiting) :=
  .plain (.live (.hit rfl rfl))

theorem recursive_source_ready :
    (annotateSuffix [23, 31] source suffixSource receiver).Valid [] captureActions capturePhases := by
  apply annotateSuffix_valid_from_bound (originalOutside :=
    .handler effectF resumeTable innerFamilies (.handler effectG resumeTable innerFamilies .nil))
    (required := [(effectF, 0), (effectG, 0)])
  · decide
  · intro owner member
    simp only [captureActions, if_pos member, Option.any_some]
  · intro owner member
    exact if_pos member
  · rfl
  · exact List.Subset.refl _
  · rfl
  · rfl

/-- A nonempty recursive capture constructs the certificate consumed by the
existing typed allocator, using an actual cut and an actual selected clause. -/
theorem recursive_capture_certificate :
    ∃ certificate : SourceScheduledCaptureAnnotations.Capture [] 19 SourceDependencyCapture.Examples.effectE 0
      ⟨false, some [], some []⟩ modes plans 1 9 clauseCode whole,
      certificate.Valid [] captureActions capturePhases := by
  apply capture_annotation (code := clauseCode)
    SourceConsumingClauseAnnotations.ReinterpretationExamples.installer_admitted
    [23, 31] source suffixSource receiver receiver recursive_source_ready
  · decide
  · exact List.Subset.refl _
  · rfl
  · rfl
  · exact physical_cut
  · exact .ordinary

end Examples

end Ash.OneShot.SourceConsumingRecursiveBounds

#print axioms Ash.OneShot.SourceConsumingRecursiveBounds.annotate_valid
#print axioms Ash.OneShot.SourceConsumingRecursiveBounds.annotate_facts
#print axioms Ash.OneShot.SourceConsumingRecursiveBounds.annotate_valid_iff
#print axioms Ash.OneShot.SourceConsumingRecursiveBounds.annotate_trace
#print axioms Ash.OneShot.SourceConsumingRecursiveBounds.annotate_fresh_owner
#print axioms Ash.OneShot.SourceConsumingRecursiveBounds.annotate_valid_from_bound
#print axioms Ash.OneShot.SourceConsumingRecursiveBounds.schedule_from_bound
#print axioms Ash.OneShot.SourceConsumingRecursiveBounds.repeated_owner_rejected
#print axioms Ash.OneShot.SourceConsumingRecursiveBounds.annotateSuffix_valid
#print axioms Ash.OneShot.SourceConsumingRecursiveBounds.annotateSuffix_facts
#print axioms Ash.OneShot.SourceConsumingRecursiveBounds.annotateSuffix_fresh_owner
#print axioms Ash.OneShot.SourceConsumingRecursiveBounds.annotateSuffix_valid_from_bound
#print axioms Ash.OneShot.SourceConsumingRecursiveBounds.handlerAnnotation_valid
#print axioms Ash.OneShot.SourceConsumingRecursiveBounds.handler_schedule_and_bound
#print axioms Ash.OneShot.SourceConsumingRecursiveBounds.capture_annotation
#print axioms Ash.OneShot.SourceConsumingRecursiveBounds.Examples.nested_reinterpretation
#print axioms Ash.OneShot.SourceConsumingRecursiveBounds.Examples.transitive_bound_checked
#print axioms Ash.OneShot.SourceConsumingRecursiveBounds.Examples.missing_transitive_operation_rejected
#print axioms Ash.OneShot.SourceConsumingRecursiveBounds.Examples.denied_nested_permission_rejected
#print axioms Ash.OneShot.SourceConsumingRecursiveBounds.Examples.physical_cut
#print axioms Ash.OneShot.SourceConsumingRecursiveBounds.Examples.fresh_capture_owner
#print axioms Ash.OneShot.SourceConsumingRecursiveBounds.Examples.recursive_source_ready
#print axioms Ash.OneShot.SourceConsumingRecursiveBounds.Examples.recursive_capture_certificate
