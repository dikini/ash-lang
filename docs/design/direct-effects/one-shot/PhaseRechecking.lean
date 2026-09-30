import SharedClosingSource

/-!
Finite source requirements evaluated at the caller's actual owner phases.
Branch arms are checked from the same phase and agree on their consumption set;
they are not sequenced as executions. Referenced record rows remain annotations.
-/

namespace Ash.OneShot.PhaseRechecking
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals CoherentSourceTypes
open OwnerPhaseTransitions (Phases Trace spendAll)

theorem spendAll_append (before : Phases) (first second : List Nat) :
    spendAll before (first ++ second) = spendAll (spendAll before first) second := by
  induction first generalizing before with
  | nil => rfl
  | cons owner rest ih => exact ih _

theorem spendAll_permutation (same : first.Perm second) : spendAll before first = spendAll before second := by
  funext owner
  simp only [OwnerPhaseTransitions.spendAll_at, same.mem_iff]

def checkOwners (before : Phases) (owners : List Nat) : Bool :=
  decide owners.Nodup && owners.all (fun owner => decide (before owner = .available))

theorem check_owners_iff : checkOwners before owners = true ↔ Trace before owners (spendAll before owners) := by
  simp [checkOwners, OwnerPhaseTransitions.trace_iff]

theorem trace_checked (trace : Trace before owners after) : checkOwners before owners = true := by
  apply check_owners_iff.mpr
  rw [← OwnerPhaseTransitions.trace_result trace]
  exact trace

/-- The index is the one-shot consumption demand of the existing source.
    These constructors are checking data, not new computation forms. -/
inductive Requirements : List Nat → Type where
  | request (nearerContext : OwnerPhases.Context) (raw : Footprint) : Requirements []
  | consume (owners : List Nat) (row : Footprint) : Requirements owners
  | spent (owner : Nat) : Requirements []
  | sequence (first : Requirements a) (second : Requirements b) : Requirements (a ++ b)
  | emitAfter (body : Requirements owners) (nearerContext : OwnerPhases.Context) (raw : Footprint) : Requirements owners
  | choice (first : Requirements a) (second : Requirements b) (same : a.Perm b) : Requirements a

def Requirements.evaluate (receiving : OwnerPhases.Context) (before : Phases) : {owners : List Nat} → Requirements owners → Option Footprint
  | _, .request nearerContext raw => OwnerSource.exportAt (nearerContext ++ receiving) before raw
  | _, .consume owners row => if checkOwners before owners then some row else none
  | _, .spent owner => if before owner = .consumed then some [] else none
  | _, @Requirements.sequence a _ first second => merge (first.evaluate receiving before) (second.evaluate receiving (spendAll before a))
  | owners, .emitAfter body nearerContext raw => merge (body.evaluate receiving before) (OwnerSource.exportAt (nearerContext ++ receiving) (spendAll before owners) raw)
  | _, .choice first second _ => merge (first.evaluate receiving before) (second.evaluate receiving before)

def Requirements.prepend (nearer : OwnerPhases.Context) : {owners : List Nat} → Requirements owners → Requirements owners
  | _, .request nearerContext raw => .request (nearerContext ++ nearer) raw
  | _, .consume owners row => .consume owners row
  | _, .spent owner => .spent owner
  | _, .sequence first second => .sequence (first.prepend nearer) (second.prepend nearer)
  | _, .emitAfter body nearerContext raw => .emitAfter (body.prepend nearer) (nearerContext ++ nearer) raw
  | _, .choice first second same => .choice (first.prepend nearer) (second.prepend nearer) same

theorem evaluate_prepend (requirements : Requirements owners) :
    (requirements.prepend nearer).evaluate receiving before = requirements.evaluate (nearer ++ receiving) before := by
  induction requirements generalizing before with
  | request => simp [Requirements.prepend, Requirements.evaluate, List.append_assoc]
  | consume | spent => rfl
  | sequence first second ihFirst ihSecond => simp [Requirements.prepend, Requirements.evaluate, ihFirst, ihSecond]
  | emitAfter body nearerContext raw ih => simp [Requirements.prepend, Requirements.evaluate, ih, List.append_assoc]
  | choice first second same ihFirst ihSecond => simp [Requirements.prepend, Requirements.evaluate, ihFirst, ihSecond]

theorem merge_split (checked : merge first second = some row) :
    ∃ a b, first = some a ∧ second = some b ∧ row = a ++ b := by
  cases first <;> cases second <;> simp_all [merge]

theorem sequence_split {first : Requirements firstOwners} {second : Requirements secondOwners} (checked : (Requirements.sequence first second).evaluate receiving before = some row) :
    ∃ a b, first.evaluate receiving before = some a ∧ second.evaluate receiving (spendAll before firstOwners) = some b ∧ row = a ++ b :=
  merge_split checked

theorem emit_split {body : Requirements owners} (checked : (Requirements.emitAfter body nearerContext raw).evaluate receiving before = some row) :
    ∃ a b, body.evaluate receiving before = some a ∧ OwnerSource.exportAt (nearerContext ++ receiving) (spendAll before owners) raw = some b ∧ row = a ++ b :=
  merge_split checked

theorem choice_split {first : Requirements firstOwners} {second : Requirements secondOwners} (checked : (Requirements.choice first second same).evaluate receiving before = some row) :
    ∃ a b, first.evaluate receiving before = some a ∧ second.evaluate receiving before = some b ∧ row = a ++ b :=
  merge_split checked

theorem consume_split (checked : (Requirements.consume owners row).evaluate receiving before = some actual) :
    Trace before owners (spendAll before owners) ∧ actual = row := by
  simp only [Requirements.evaluate] at checked
  split at checked
  · exact ⟨check_owners_iff.mp (by assumption), (Option.some.inj checked).symm⟩
  · cases checked

theorem evaluate_trace (requirements : Requirements owners) (checked : requirements.evaluate receiving before = some row) :
    Trace before owners (spendAll before owners) := by
  induction requirements generalizing before row with
  | request | spent => exact .nil
  | consume => exact (consume_split checked).1
  | sequence first second ihFirst ihSecond =>
      obtain ⟨a, b, left, right, same⟩ := sequence_split checked
      simpa only [spendAll_append] using OwnerPhaseTransitions.trace_append (ihFirst left) (ihSecond right)
  | emitAfter body nearerContext raw ih =>
      obtain ⟨a, b, bodyChecked, exported, same⟩ := emit_split checked
      exact ih bodyChecked
  | choice first second same ihFirst ihSecond =>
      obtain ⟨a, b, left, right, rows⟩ := choice_split checked
      exact ihFirst left

theorem evaluate_once (requirements : Requirements owners) (checked : requirements.evaluate receiving before = some row) : owners.Nodup :=
  OwnerPhaseTransitions.trace_nodup (evaluate_trace requirements checked)

def requestFrom {inside : OwnerPhases.Context} {before : Phases} {raw row : Footprint}
    (_ : OwnerSource.exportAt inside before raw = some row) : Requirements [] := .request [] raw

def emitFrom (body : Requirements owners) {inside : OwnerPhases.Context} {before : Phases} {raw row : Footprint}
    (_ : OwnerSource.exportAt inside before raw = some row) : Requirements owners := .emitAfter body [] raw

def protectedFrom (body : Requirements owners) {inside : OwnerPhases.Context} {before : Phases} {latent row : Footprint}
    (_ : residualize (.barrier true :: OwnerPhaseTransitions.project inside before) latent = some row) : Requirements owners :=
  .emitAfter body [] (qualify true latent)

def resuming {contracts : Owners.Contracts} {owner : Nat} {contract : Owners.Contract}
    (_ : contracts owner = some contract) : Requirements (owner :: contract.resumeDemand) :=
  .consume (owner :: contract.resumeDemand) contract.resumeRow

theorem source_rechecks
    (source : Owners.Derives operations policy contracts inside world environment allowed scope before code after result demand row) :
    ∃ requirements : Requirements demand,
      requirements.evaluate inside before = some row ∧
      ∀ receiving start actual, requirements.evaluate receiving start = some actual →
        Owners.Derives operations policy contracts receiving world environment allowed scope start code (spendAll start demand) result demand actual := by
  induction source with
  | stable summary exported =>
      exact ⟨requestFrom exported, exported, fun _ _ _ checked => .stable summary checked⟩
  | pair left right ihLeft ihRight =>
      obtain ⟨a, originalA, recheckA⟩ := ihLeft
      obtain ⟨b, originalB, recheckB⟩ := ihRight
      refine ⟨.sequence a b, ?_, ?_⟩
      · simp only [Requirements.evaluate, ← OwnerPhaseTransitions.trace_result (Owners.source_trace left), originalA, originalB, merge]
      · intro receiving start actual checked
        obtain ⟨x, y, checkedA, checkedB, rfl⟩ := sequence_split checked
        simpa only [spendAll_append] using Owners.Derives.pair (recheckA _ _ _ checkedA) (recheckB _ _ _ checkedB)
  | app function argument admitted exported ihFunction ihArgument =>
      obtain ⟨a, originalA, recheckA⟩ := ihFunction
      obtain ⟨b, originalB, recheckB⟩ := ihArgument
      refine ⟨emitFrom (.sequence a b) exported, ?_, ?_⟩
      · simp only [emitFrom, Requirements.evaluate, spendAll_append,
          ← OwnerPhaseTransitions.trace_result (Owners.source_trace function),
          ← OwnerPhaseTransitions.trace_result (Owners.source_trace argument), List.nil_append, originalA, originalB, exported, merge]
      · intro receiving start actual checked
        obtain ⟨xy, call, both, callChecked, rfl⟩ := emit_split checked
        obtain ⟨x, y, checkedA, checkedB, rfl⟩ := sequence_split both
        simpa only [spendAll_append] using Owners.Derives.app (recheckA _ _ _ checkedA) (recheckB _ _ _ checkedB) admitted
          (by simpa only [spendAll_append, List.nil_append] using callChecked)
  | bind initializer body ihInit ihBody =>
      obtain ⟨a, originalA, recheckA⟩ := ihInit
      obtain ⟨b, originalB, recheckB⟩ := ihBody
      refine ⟨.sequence a b, ?_, ?_⟩
      · simp only [Requirements.evaluate, ← OwnerPhaseTransitions.trace_result (Owners.source_trace initializer), originalA, originalB, merge]
      · intro receiving start actual checked
        obtain ⟨x, y, checkedA, checkedB, rfl⟩ := sequence_split checked
        simpa only [spendAll_append] using Owners.Derives.bind (recheckA _ _ _ checkedA) (recheckB _ _ _ checkedB)
  | branch condition yes no ihCondition ihYes ihNo =>
      obtain ⟨a, originalA, recheckA⟩ := ihCondition
      obtain ⟨b, originalB, recheckB⟩ := ihYes
      obtain ⟨c, originalC, recheckC⟩ := ihNo
      have same := Owners.branch_demands_agree yes no
      refine ⟨.sequence a (.choice b c same), ?_, ?_⟩
      · simp only [Requirements.evaluate, ← OwnerPhaseTransitions.trace_result (Owners.source_trace condition), originalA, originalB, originalC, merge, List.append_assoc]
      · intro receiving start actual checked
        obtain ⟨x, yz, checkedA, checkedChoice, rfl⟩ := sequence_split checked
        obtain ⟨y, z, checkedB, checkedC, rfl⟩ := choice_split checkedChoice
        have alternative := recheckC _ _ _ checkedC
        rw [← spendAll_permutation same] at alternative
        simpa only [spendAll_append, List.append_assoc] using Owners.Derives.branch (recheckA _ _ _ checkedA) (recheckB _ _ _ checkedB) alternative
  | perform known admitted operand formed exported ih =>
      obtain ⟨a, original, recheck⟩ := ih
      refine ⟨emitFrom a exported, ?_, ?_⟩
      · simp only [emitFrom, Requirements.evaluate, ← OwnerPhaseTransitions.trace_result (Owners.source_trace operand), List.nil_append, original, exported, merge]
      · intro receiving start actual checked
        obtain ⟨x, request, checkedOperand, checkedRequest, rfl⟩ := emit_split checked
        exact .perform known admitted (recheck _ _ _ checkedOperand) formed checkedRequest
  | resource initializer body formed effectsBound admitted outward exported ih =>
      obtain ⟨a, original, recheck⟩ := ih
      refine ⟨emitFrom a exported, ?_, ?_⟩
      · simp only [emitFrom, Requirements.evaluate, ← OwnerPhaseTransitions.trace_result (Owners.source_trace initializer), List.nil_append, original, exported, merge]
      · intro receiving start actual checked
        obtain ⟨x, request, checkedInitializer, checkedRequest, rfl⟩ := emit_split checked
        exact .resource (recheck _ _ _ checkedInitializer) body formed effectsBound admitted outward checkedRequest
  | resume known resolved permission operand transition admitted formed ih =>
      obtain ⟨a, original, recheck⟩ := ih
      refine ⟨.sequence a (resuming known), ?_, ?_⟩
      · simp only [resuming, Requirements.evaluate, ← OwnerPhaseTransitions.trace_result (Owners.source_trace operand), original, trace_checked transition, ite_true, merge]
      · intro receiving start actual checked
        obtain ⟨x, resumed, checkedOperand, checkedResume, rfl⟩ := sequence_split checked
        obtain ⟨changed, rfl⟩ := consume_split checkedResume
        simpa only [spendAll_append] using Owners.Derives.resume known resolved permission (recheck _ _ _ checkedOperand) changed admitted formed
  | discard known resolved permission unprotected closable transition admitted =>
      rename_i owner contract binder bound initial final permitted env localScope
      refine ⟨.consume _ bound, by simp only [Requirements.evaluate, trace_checked transition, ite_true], ?_⟩
      intro receiving start actual checked
      obtain ⟨changed, rfl⟩ := consume_split checked
      exact .discard known resolved permission unprotected closable changed admitted
  | cleanup callback body admitted exported ihCallback ihBody =>
      obtain ⟨a, originalA, recheckA⟩ := ihCallback
      obtain ⟨b, originalB, recheckB⟩ := ihBody
      have exportedRaw := exported
      simp only [residualize, DisposalProtection.through_barrier] at exportedRaw
      refine ⟨protectedFrom (.sequence a b) exported, ?_, ?_⟩
      · simp only [protectedFrom, Requirements.evaluate, spendAll_append,
          ← OwnerPhaseTransitions.trace_result (Owners.source_trace callback),
          ← OwnerPhaseTransitions.trace_result (Owners.source_trace body), List.nil_append, originalA, originalB, OwnerSource.exportAt, exportedRaw, merge]
      · intro receiving start actual checked
        obtain ⟨xy, call, both, checkedCall, rfl⟩ := emit_split checked
        obtain ⟨x, y, checkedA, checkedB, rfl⟩ := sequence_split both
        have invoked := checkedCall
        change residualize (OwnerPhaseTransitions.project receiving (spendAll start _)) (qualify true _) = some call at invoked
        simpa only [spendAll_append] using Owners.Derives.cleanup (recheckA _ _ _ checkedA) (recheckB _ _ _ checkedB) admitted
          (by simpa only [spendAll_append, residualize, DisposalProtection.through_barrier] using invoked)

theorem context_rechecks
    (context : SharedSourceSegments.Context operations policy contracts inside world environment allowed scope position before input after output demand row) :
    ∃ requirements : Requirements demand,
      requirements.evaluate inside before = some row ∧
      ∀ receiving start actual, requirements.evaluate receiving start = some actual →
        SharedSourceSegments.Context operations policy contracts receiving world environment allowed scope position
          start input (spendAll start demand) output demand actual := by
  cases context with
  | pairLeft right =>
      obtain ⟨a, original, recheck⟩ := source_rechecks right
      exact ⟨a, original, fun _ _ _ checked => .pairLeft (recheck _ _ _ checked)⟩
  | pairRight left =>
      refine ⟨.consume [] [], rfl, ?_⟩
      intro receiving start actual checked
      obtain ⟨_, rfl⟩ := consume_split checked
      exact .pairRight left
  | appFunction argument admitted exported =>
      obtain ⟨a, original, recheck⟩ := source_rechecks argument
      refine ⟨emitFrom a exported, ?_, ?_⟩
      · simp only [emitFrom, Requirements.evaluate, ← OwnerPhaseTransitions.trace_result (Owners.source_trace argument),
          List.nil_append, original, exported, merge]
      · intro receiving start actual checked
        obtain ⟨body, call, checkedBody, checkedCall, rfl⟩ := emit_split checked
        exact .appFunction (recheck _ _ _ checkedBody) admitted checkedCall
  | appArgument function admitted exported =>
      exact ⟨requestFrom exported, exported, fun _ _ _ checked => .appArgument function admitted checked⟩
  | bind body =>
      obtain ⟨a, original, recheck⟩ := source_rechecks body
      exact ⟨a, original, fun _ _ _ checked => .bind (recheck _ _ _ checked)⟩
  | branch yes no =>
      obtain ⟨a, originalA, recheckA⟩ := source_rechecks yes
      obtain ⟨b, originalB, recheckB⟩ := source_rechecks no
      have same := Owners.branch_demands_agree yes no
      refine ⟨.choice a b same, by simp only [Requirements.evaluate, originalA, originalB, merge], ?_⟩
      intro receiving start actual checked
      obtain ⟨x, y, checkedA, checkedB, rfl⟩ := choice_split checked
      have alternative := recheckB _ _ _ checkedB
      rw [← spendAll_permutation same] at alternative
      exact .branch (recheckA _ _ _ checkedA) alternative
  | perform known admitted formed exported =>
      exact ⟨requestFrom exported, exported, fun _ _ _ checked => .perform known admitted formed checked⟩
  | resource body formed effectsBound admitted outward exported =>
      exact ⟨requestFrom exported, exported, fun _ _ _ checked => .resource body formed effectsBound admitted outward checked⟩
  | resume known resolved permission transition admitted formed =>
      refine ⟨resuming known, by simp only [resuming, Requirements.evaluate, trace_checked transition, ite_true], ?_⟩
      intro receiving start actual checked
      obtain ⟨changed, rfl⟩ := consume_split checked
      exact .resume known resolved permission changed admitted formed
  | cleanup body admitted exported =>
      obtain ⟨a, original, recheck⟩ := source_rechecks body
      have exportedRaw := exported
      simp only [residualize, DisposalProtection.through_barrier] at exportedRaw
      refine ⟨protectedFrom a exported, ?_, ?_⟩
      · simp only [protectedFrom, Requirements.evaluate, ← OwnerPhaseTransitions.trace_result (Owners.source_trace body),
          List.nil_append, original, OwnerSource.exportAt, exportedRaw, merge]
      · intro receiving start actual checked
        obtain ⟨body, call, checkedBody, checkedCall, rfl⟩ := emit_split checked
        exact .cleanup (recheck _ _ _ checkedBody) admitted
          (by simpa only [List.nil_append, OwnerSource.exportAt, residualize, DisposalProtection.through_barrier] using checkedCall)

theorem frame_rechecks
    (frame : SharedSourceSegments.Frame operations policy contracts inside world entry before input after output demand row) :
    ∃ requirements : Requirements demand,
      requirements.evaluate inside before = some row ∧
      ∀ receiving start actual, requirements.evaluate receiving start = some actual →
        SharedSourceSegments.Frame operations policy contracts receiving world entry start input (spendAll start demand) output demand actual := by
  cases frame with
  | plain source scopeTyped inputAnnotation outputAnnotation =>
      obtain ⟨a, original, recheck⟩ := context_rechecks source
      exact ⟨a, original, fun _ _ _ checked => .plain (recheck _ _ _ checked) scopeTyped inputAnnotation outputAnnotation⟩
  | handler typed annotation =>
      refine ⟨.consume [] [], rfl, ?_⟩
      intro receiving start actual checked
      obtain ⟨_, rfl⟩ := consume_split checked
      exact .handler typed annotation
  | cell scopeKnown noEscape annotation =>
      refine ⟨.consume [] [], rfl, ?_⟩
      intro receiving start actual checked
      obtain ⟨_, rfl⟩ := consume_split checked
      exact .cell scopeKnown noEscape annotation
  | armed scopeKnown callback annotation exported =>
      exact ⟨requestFrom exported, exported, fun _ _ _ checked => .armed scopeKnown callback annotation checked⟩
  | running scopeKnown callback saved annotation =>
      refine ⟨.consume [] [], rfl, ?_⟩
      intro receiving start actual checked
      obtain ⟨_, rfl⟩ := consume_split checked
      exact .running scopeKnown callback saved annotation
  | closing scopeKnown =>
      refine ⟨.consume [] [], rfl, ?_⟩
      intro receiving start actual checked
      obtain ⟨_, rfl⟩ := consume_split checked
      exact .closing scopeKnown
  | retiring known transition =>
      refine ⟨.consume _ [], by simp only [Requirements.evaluate, trace_checked transition, ite_true], ?_⟩
      intro receiving start actual checked
      obtain ⟨changed, rfl⟩ := consume_split checked
      exact .retiring known changed

theorem spent_split (checked : (Requirements.spent owner).evaluate receiving before = some row) :
    before owner = .consumed ∧ row = [] := by
  simp only [Requirements.evaluate] at checked
  split at checked
  · exact ⟨by assumption, (Option.some.inj checked).symm⟩
  · cases checked

def spentFrom {before : Phases} {owner : Nat}
    (_ : before owner = .consumed) : Requirements [] := .spent owner

theorem segment_rechecks
    (segment : SharedSourceSegments.Segment operations policy contracts tables world fixed stack before input after output demand row) :
    ∃ requirements : Requirements demand,
      requirements.evaluate (OwnerPhases.ofStack tables fixed) before = some row ∧
      ∀ receiving start actual, requirements.evaluate (OwnerPhases.ofStack tables receiving) start = some actual →
        SharedSourceSegments.Segment operations policy contracts tables world receiving stack start input (spendAll start demand) output demand actual := by
  induction segment with
  | nil =>
      refine ⟨.consume [] [], rfl, ?_⟩
      intro receiving start actual checked
      obtain ⟨_, rfl⟩ := consume_split checked
      exact .nil
  | @push entry before input middle intermediate headDemand headRow fixed rest after output tailDemand tailRow head tail ih =>
      obtain ⟨a, originalA, recheckA⟩ := frame_rechecks head
      obtain ⟨b, originalB, recheckB⟩ := ih
      refine ⟨.sequence (a.prepend (OwnerPhases.ofStack tables rest)) b, ?_, ?_⟩
      · simp only [Requirements.evaluate, evaluate_prepend, ← OwnerPhases.stack_append,
          ← OwnerPhaseTransitions.trace_result (OwnerSource.frame_trace (SharedSourceSegments.frame_source head)), originalA, originalB, merge]
      · intro receiving start actual checked
        obtain ⟨x, y, checkedA, checkedB, rfl⟩ := sequence_split checked
        rw [evaluate_prepend, ← OwnerPhases.stack_append] at checkedA
        simpa only [spendAll_append] using SharedSourceSegments.Segment.push (recheckA _ _ _ checkedA) (recheckB _ _ _ checkedB)
  | live known inputAnnotation answerAnnotation scopeKnown held consumed saved covered tail ihSaved ihTail =>
      obtain ⟨a, original, recheck⟩ := ihTail
      refine ⟨.sequence (spentFrom consumed) a, ?_, ?_⟩
      · simp only [spentFrom, Requirements.evaluate, consumed, ite_true, spendAll, original, merge, List.nil_append]
      · intro receiving start actual checked
        obtain ⟨guardRow, tailRow, guardChecked, tailChecked, rfl⟩ := sequence_split checked
        obtain ⟨done, rfl⟩ := spent_split guardChecked
        exact .live known inputAnnotation answerAnnotation scopeKnown held done saved covered (recheck _ _ _ tailChecked)
  | spent known answerAnnotation scopeKnown consumed tail ih =>
      obtain ⟨a, original, recheck⟩ := ih
      refine ⟨.sequence (spentFrom consumed) a, ?_, ?_⟩
      · simp only [spentFrom, Requirements.evaluate, consumed, ite_true, spendAll, original, merge, List.nil_append]
      · intro receiving start actual checked
        obtain ⟨guardRow, tailRow, guardChecked, tailChecked, rfl⟩ := sequence_split checked
        obtain ⟨done, rfl⟩ := spent_split guardChecked
        exact .spent known answerAnnotation scopeKnown done (recheck _ _ _ tailChecked)

theorem configuration_rechecks
    (source : SharedSourceSegments.Source operations policy contracts tables world fixed outside scope code stack before after output demand row) :
    ∃ requirements : Requirements demand,
      requirements.evaluate (OwnerPhases.ofStack tables fixed) before = some row ∧
      ∀ receiving start actual, requirements.evaluate (OwnerPhases.ofStack tables receiving) start = some actual →
        checkFootprint outside actual = true →
        SharedSourceSegments.Source operations policy contracts tables world receiving outside scope code stack
          start (spendAll start demand) output demand actual := by
  cases source with
  | checked current scopeTyped pending accepted =>
      obtain ⟨a, originalA, recheckA⟩ := source_rechecks current
      obtain ⟨b, originalB, recheckB⟩ := segment_rechecks pending
      refine ⟨.sequence (a.prepend (OwnerPhases.ofStack tables stack)) b, ?_, ?_⟩
      · simp only [Requirements.evaluate, evaluate_prepend, ← OwnerPhases.stack_append,
          ← OwnerPhaseTransitions.trace_result (Owners.source_trace current), originalA, originalB, merge]
      · intro receiving start actual checked admitted
        obtain ⟨x, y, checkedA, checkedB, rfl⟩ := sequence_split checked
        rw [evaluate_prepend, ← OwnerPhases.stack_append] at checkedA
        simpa only [spendAll_append] using SharedSourceSegments.Source.checked
          (recheckA _ _ _ checkedA) scopeTyped (recheckB _ _ _ checkedB) admitted

namespace Examples
open OwnerPhaseTransitions (available empty)

def alternatives : Requirements [19] :=
  .choice (.consume [19] []) (.consume [19] []) (.refl _)

theorem branches_consume_once : alternatives.evaluate [] (available [19, 23]) = some [] := by decide

theorem sequence_cannot_consume_twice :
    (Requirements.sequence (.consume [19] []) (.consume [19] [])).evaluate [] (available [19, 23]) = none := by decide

theorem unavailable_owner_rejected : alternatives.evaluate [] (available [23]) = none := by decide

theorem unrelated_owner_retained : spendAll (available [19, 23]) [19] 23 = .available := by decide

def differentOrders : Requirements [19, 29] :=
  .choice (.consume [19, 29] []) (.consume [29, 19] []) (List.Perm.swap _ _ _)

theorem different_orders_admitted : differentOrders.evaluate [] (available [19, 29, 23]) = some [] := by decide

theorem different_orders_same_state :
    spendAll (available [19, 29, 23]) [19, 29] = spendAll (available [19, 29, 23]) [29, 19] :=
  spendAll_permutation (List.Perm.swap _ _ _)

theorem different_branch_owners_rejected : ¬ ([19] : List Nat).Perm [29] := by
  intro same
  have member := same.mem_iff.mp (List.mem_cons_self (a := 19) (l := []))
  simp at member

def effect : Instance := .user 81 []
def raw : Footprint := [⟨effect, 0, false⟩]
def protection : OwnerPhases.Context :=
  [.live 19 true, .ordinary (.handler effect 4 [(0, ⟨true, some [], none⟩)])]
def request : Requirements [] := .request [] raw

theorem available_protection_rejects : request.evaluate protection (available [19]) = none := by decide

theorem consumed_protection_admits : request.evaluate protection empty = some [] := by decide

theorem consumption_precedes_request :
    (Requirements.sequence (.consume [19] []) request).evaluate protection (available [19]) = some [] := by decide

theorem request_cannot_precede_consumption :
    (Requirements.sequence request (.consume [19] [])).evaluate protection (available [19]) = none := by decide

open SharedSourceSegments.Examples (operations policy contracts contract owner_known resumePlain tables nested nested_shared)

theorem resume_expression_reconstructs
    (checked : (Requirements.consume [19] []).evaluate inside start = some row) :
    Owners.Derives operations policy contracts inside [] Environment.empty [] (.ticket 7 19) start
      (.resume 7 (.integer 17)) (spendAll start [19]) .boolean [19] row := by
  obtain ⟨transition, rfl⟩ := consume_split checked
  have operand : Owners.Derives operations policy contracts inside [] Environment.empty [] (.ticket 7 19)
      start (.integer 17) start .integer [] [] :=
    .stable .integer (by simp [OwnerSource.exportAt, residual_empty])
  exact .resume owner_known rfl rfl operand transition
    (by simp [contract]) (by simp [contract, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])

theorem branch_source_reconstructs
    (checked : alternatives.evaluate inside start = some row) :
    Owners.Derives operations policy contracts inside [] Environment.empty [] (.ticket 7 19) start
      (.branch (.boolean true) (.resume 7 (.integer 17)) (.resume 7 (.integer 17)))
      (spendAll start [19]) .boolean [19] row := by
  obtain ⟨a, b, checkedA, checkedB, rfl⟩ := choice_split checked
  have condition : Owners.Derives operations policy contracts inside [] Environment.empty [] (.ticket 7 19)
      start (.boolean true) start .boolean [] [] :=
    .stable .boolean (by simp [OwnerSource.exportAt, residual_empty])
  exact .branch condition
    (resume_expression_reconstructs checkedA) (resume_expression_reconstructs checkedB)

theorem branch_source_at_new_phase :
    Owners.Derives operations policy contracts [] [] Environment.empty [] (.ticket 7 19) (available [19, 23])
      (.branch (.boolean true) (.resume 7 (.integer 17)) (.resume 7 (.integer 17)))
      (spendAll (available [19, 23]) [19]) .boolean [19] [] :=
  branch_source_reconstructs branches_consume_once

theorem resume_frame_reconstructs
    (checked : (Requirements.consume [19] []).evaluate inside start = some row) :
    SharedSourceSegments.Frame operations policy contracts inside [] (.plain resumePlain)
      start .integer (spendAll start [19]) .boolean [19] row := by
  obtain ⟨transition, rfl⟩ := consume_split checked
  have context : SharedSourceSegments.Context operations policy contracts inside [] Environment.empty []
      (.ticket 7 19) (.resume 7) start .integer (spendAll start [19]) .boolean [19] [] :=
    .resume owner_known rfl rfl transition (by simp [contract])
      (by simp [contract, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
  exact .plain context (.bound (Owners.ports_lookup owner_known)) rfl rfl

theorem resume_frame_at_new_phase :
    SharedSourceSegments.Frame operations policy contracts inside [] (.plain resumePlain)
      (available [19, 23]) .integer (spendAll (available [19, 23]) [19]) .boolean [19] [] :=
  resume_frame_reconstructs (by simp [Requirements.evaluate, checkOwners, available])

theorem nested_boundary_reconstructs
    (checked : (Requirements.spent 19).evaluate (OwnerPhases.ofStack tables fixed) start = some row) :
    SharedSourceSegments.Segment operations policy contracts tables [] fixed nested
      start .boolean start .boolean [] row := by
  obtain ⟨done, rfl⟩ := spent_split checked
  exact .live owner_known rfl rfl ⟨.none, .none⟩ rfl done (receiver := Stack.nil)
    SharedSourceSegments.Examples.captured_shared (EffectBounds.covers_refl []) .nil

theorem nested_boundary_at_new_phase :
    SharedSourceSegments.Segment operations policy contracts tables [] .nil nested
      (available [23]) .boolean (available [23]) .boolean [] [] :=
  nested_boundary_reconstructs (by decide)

theorem nested_history_retained :
    CaptureAuthentication.Retained operations.protection policy contracts.source tables nested :=
  SharedSourceSegments.segment_authenticated nested_boundary_at_new_phase

theorem available_boundary_rejected : (Requirements.spent 19).evaluate [] (available [19, 23]) = none := by decide

end Examples

end Ash.OneShot.PhaseRechecking

#print axioms Ash.OneShot.PhaseRechecking.spendAll_append
#print axioms Ash.OneShot.PhaseRechecking.spendAll_permutation
#print axioms Ash.OneShot.PhaseRechecking.check_owners_iff
#print axioms Ash.OneShot.PhaseRechecking.trace_checked
#print axioms Ash.OneShot.PhaseRechecking.evaluate_prepend
#print axioms Ash.OneShot.PhaseRechecking.merge_split
#print axioms Ash.OneShot.PhaseRechecking.sequence_split
#print axioms Ash.OneShot.PhaseRechecking.emit_split
#print axioms Ash.OneShot.PhaseRechecking.choice_split
#print axioms Ash.OneShot.PhaseRechecking.consume_split
#print axioms Ash.OneShot.PhaseRechecking.evaluate_trace
#print axioms Ash.OneShot.PhaseRechecking.evaluate_once
#print axioms Ash.OneShot.PhaseRechecking.source_rechecks
#print axioms Ash.OneShot.PhaseRechecking.context_rechecks
#print axioms Ash.OneShot.PhaseRechecking.frame_rechecks
#print axioms Ash.OneShot.PhaseRechecking.spent_split
#print axioms Ash.OneShot.PhaseRechecking.segment_rechecks
#print axioms Ash.OneShot.PhaseRechecking.configuration_rechecks
#print axioms Ash.OneShot.PhaseRechecking.Examples.branches_consume_once
#print axioms Ash.OneShot.PhaseRechecking.Examples.sequence_cannot_consume_twice
#print axioms Ash.OneShot.PhaseRechecking.Examples.unavailable_owner_rejected
#print axioms Ash.OneShot.PhaseRechecking.Examples.unrelated_owner_retained
#print axioms Ash.OneShot.PhaseRechecking.Examples.different_orders_admitted
#print axioms Ash.OneShot.PhaseRechecking.Examples.different_orders_same_state
#print axioms Ash.OneShot.PhaseRechecking.Examples.different_branch_owners_rejected
#print axioms Ash.OneShot.PhaseRechecking.Examples.available_protection_rejects
#print axioms Ash.OneShot.PhaseRechecking.Examples.consumed_protection_admits
#print axioms Ash.OneShot.PhaseRechecking.Examples.consumption_precedes_request
#print axioms Ash.OneShot.PhaseRechecking.Examples.request_cannot_precede_consumption
#print axioms Ash.OneShot.PhaseRechecking.Examples.resume_expression_reconstructs
#print axioms Ash.OneShot.PhaseRechecking.Examples.branch_source_reconstructs
#print axioms Ash.OneShot.PhaseRechecking.Examples.branch_source_at_new_phase
#print axioms Ash.OneShot.PhaseRechecking.Examples.resume_frame_reconstructs
#print axioms Ash.OneShot.PhaseRechecking.Examples.resume_frame_at_new_phase
#print axioms Ash.OneShot.PhaseRechecking.Examples.nested_boundary_reconstructs
#print axioms Ash.OneShot.PhaseRechecking.Examples.nested_boundary_at_new_phase
#print axioms Ash.OneShot.PhaseRechecking.Examples.nested_history_retained
#print axioms Ash.OneShot.PhaseRechecking.Examples.available_boundary_rejected
