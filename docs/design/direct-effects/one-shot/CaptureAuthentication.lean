import ResumeSpecialization

/-!
Historical source certificates for every physically retained live capture.
The recursive judgment follows both dormant captures and the active tail.
It checks resume-source provenance, not closing annotations, shared port
agreement or admission of the current expression. A historical receiver is
retained as evidence; a future resume still rechecks its actual receiver.
-/

namespace Ash.OneShot.CaptureAuthentication
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts OwnerSource
open OwnerCaptureContracts (SavedSource Extends)

inductive Certified (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Contracts) (tables : CallableProtectionFrames.Tables) : Nat → Stack → Prop where
  | saved (known : contracts owner = some contract)
      (source : SavedSource operations policy contracts tables receiver capture before after contract) :
      Certified operations policy contracts tables owner capture

/-- Each live node has its own source certificate and recursively checked
    dormant contents. Frames introduce no dormant capture in this machine. -/
inductive Retained (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Contracts) (tables : CallableProtectionFrames.Tables) : Stack → Prop where
  | nil : Retained operations policy contracts tables .nil
  | push (rest : Retained operations policy contracts tables tail) :
      Retained operations policy contracts tables (.push frame tail)
  | live (certificate : Certified operations policy contracts tables owner capture)
      (saved : Retained operations policy contracts tables capture)
      (rest : Retained operations policy contracts tables tail) :
      Retained operations policy contracts tables (.live owner input answer capture scope tail)
  | spent (rest : Retained operations policy contracts tables tail) :
      Retained operations policy contracts tables (.spent owner answer scope tail)

variable {front capture tail : Stack}

theorem certified_extension (certificate : Certified operations policy contracts tables owner capture)
    (extension : Extends contracts larger) : Certified operations policy larger tables owner capture := by
  cases certificate with
  | saved known source => exact .saved (extension _ _ known) (source.extend extension)

theorem retained_extension (retained : Retained operations policy contracts tables stack)
    (extension : Extends contracts larger) : Retained operations policy larger tables stack := by
  induction retained with
  | nil => exact .nil
  | push rest ih => exact .push ih
  | live certificate saved rest ihSaved ihRest => exact .live (certified_extension certificate extension) ihSaved ihRest
  | spent rest ih => exact .spent ih

theorem append (front : Retained operations policy contracts tables first)
    (tail : Retained operations policy contracts tables second) :
    Retained operations policy contracts tables (first.append second) := by
  induction front with
  | nil => exact tail
  | push rest ih => exact .push ih
  | live certificate saved rest ihSaved ihRest => exact .live certificate saved ihRest
  | spent rest ih => exact .spent ih

theorem decompose (front : Stack)
    (retained : Retained operations policy contracts tables (front.append tail)) :
    Retained operations policy contracts tables front ∧ Retained operations policy contracts tables tail := by
  induction front with
  | nil => exact ⟨.nil, retained⟩
  | push frame rest ih => cases retained with
      | push tail =>
          obtain ⟨first, second⟩ := ih tail
          exact ⟨.push first, second⟩
  | live owner input answer capture scope rest ihCapture ihRest => cases retained with
      | live certificate saved tail =>
          obtain ⟨first, second⟩ := ihRest tail
          exact ⟨.live certificate saved first, second⟩
  | spent owner answer scope rest ih => cases retained with
      | spent tail =>
          obtain ⟨first, second⟩ := ih tail
          exact ⟨.spent first, second⟩

theorem cut (selection : HandlerCut requested whole capture tail handler)
    (retained : Retained operations policy contracts tables whole) :
    Retained operations policy contracts tables capture ∧ Retained operations policy contracts tables tail := by
  rw [handler_cut_reconstructs selection] at retained
  exact decompose capture retained

theorem pop (retained : Retained operations policy contracts tables (.push frame tail)) :
    Retained operations policy contracts tables tail := by cases retained; assumption

theorem pop_spent (retained : Retained operations policy contracts tables (.spent owner answer scope tail)) :
    Retained operations policy contracts tables tail := by cases retained; assumption

theorem selected (retained : Retained operations policy contracts tables
    (front.append (.live owner input answer capture scope tail))) :
    Certified operations policy contracts tables owner capture ∧
    Retained operations policy contracts tables capture ∧
    Retained operations policy contracts tables front ∧ Retained operations policy contracts tables tail := by
  obtain ⟨first, last⟩ := decompose front retained
  cases last with
  | live certificate saved rest => exact ⟨certificate, saved, first, rest⟩

theorem resume (retained : Retained operations policy contracts tables
    (front.append (.live owner input answer capture scope tail))) :
    Retained operations policy contracts tables (capture.append (front.append (.spent owner answer scope tail))) := by
  obtain ⟨certificate, saved, first, rest⟩ := selected retained
  exact append saved (append first (.spent rest))

theorem close_control (plan : List CloseEntry) :
    Retained operations policy contracts tables (closeControl scope plan) := by
  induction plan with
  | nil => exact .nil
  | cons entry rest ih => exact .push ih

theorem discard (retained : Retained operations policy contracts tables
    (front.append (.live owner input answer capture caller tail))) :
    Retained operations policy contracts tables ((closeControl scope plan).append
      (.push (.closing closeId scope) (front.append (.spent owner answer caller tail)))) := by
  obtain ⟨certificate, saved, first, rest⟩ := selected retained
  exact append (close_control plan) (.push (append first (.spent rest)))

theorem cell_update (update : CellUpdate identity old new before after)
    (retained : Retained operations policy contracts tables before) :
    Retained operations policy contracts tables after := by
  induction update with
  | hit => exact .push (pop retained)
  | push miss next ih => exact .push (ih (pop retained))
  | live next ih => cases retained with
      | live certificate saved rest => exact .live certificate saved (ih rest)
  | spent next ih => exact .spent (ih (pop_spent retained))

/-- Every transition except fresh capture preserves this component directly.
    Disposal removes dormant source obligations; this does not check its plan. -/
theorem non_capture_step (step : RawStep before after created discharged)
    (noTicket : ∀ owner, Owner.ticket owner ∉ created)
    (retained : Retained operations policy contracts tables before.stack) :
    Retained operations policy contracts tables after.stack := by
  cases step with
  | focus => exact .push retained
  | plug => exact pop retained
  | bind | beta | ifTrue | ifFalse => exact retained
  | enterHandler | enterCell | enterCleanup => exact .push retained
  | leaveHandler | leaveCell | finishCleanup | finishClose | retire => exact pop retained
  | startCleanup => exact .push (pop retained)
  | capture requested operation parameter binder ticket => exact False.elim (noTicket ticket List.mem_cons_self)
  | resume => exact resume retained
  | discard => exact discard retained
  | leaveClause => exact pop_spent retained
  | readCell identity payload scope before after update => exact cell_update update retained
  | writeCell identity old new scope before after update => exact cell_update update retained

/-- Capture obtains the new certificate from the actual source cut, then
    extends all older certificates. No after-forest premise is supplied. -/
theorem capture_from_source
    (selection : HandlerCut requested whole capture tail handler)
    (source : Source operations policy contracts tables fixed outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole before after output demand row)
    (isValue : operand.IsValue) (closeDemand : List Nat) (closeRow : Option Footprint)
    (retained : Retained operations policy contracts tables whole)
    (fresh : contracts owner = none) :
    ∃ contract : ResumeContract,
      contract.closeDemand = closeDemand ∧ contract.closeRow = closeRow ∧
      Retained operations policy (OwnerCaptureContracts.insert contracts owner contract) tables
        (.live owner inputType handler.answer capture handler.scope tail) := by
  obtain ⟨environment, raw, requestRow, middle, contract, remaining, restRow,
    summary, exported, ⟨saved⟩, pending, sameCloseDemand, sameCloseRow, names, effects, accepted⟩ :=
    OwnerCaptureContracts.capture_contract selection source isValue closeDemand closeRow
  obtain ⟨savedRetained, tailRetained⟩ := cut selection retained
  have extension := OwnerCaptureContracts.insert_extends (contract := contract) fresh
  exact ⟨contract, sameCloseDemand, sameCloseRow,
    .live (.saved OwnerCaptureContracts.insert_lookup (saved.extend extension))
      (retained_extension savedRetained extension) (retained_extension tailRetained extension)⟩

theorem capture_step_from_source
    (selection : HandlerCut requested whole capture tail handler)
    (clause : ClauseAt operation handler.clauses parameter binder body)
    (closed : ClosedValue operand) (environmentReady : ClosedExcept parameter body)
    (source : Source operations policy contracts tables fixed outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole before after output demand row)
    (retained : Retained operations policy contracts tables whole)
    (fresh : contracts owner = none) (closeDemand : List Nat) (closeRow : Option Footprint) :
    ∃ contract : ResumeContract,
      RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩
        ⟨body.subst parameter operand, .ticket binder owner,
          .live owner inputType handler.answer capture handler.scope tail⟩ [.ticket owner] [] ∧
      Retained operations policy (OwnerCaptureContracts.insert contracts owner contract) tables
        (.live owner inputType handler.answer capture handler.scope tail) := by
  obtain ⟨contract, closeDemandSame, closeRowSame, authenticated⟩ :=
    capture_from_source selection source closed.1 closeDemand closeRow retained fresh
  exact ⟨contract, .capture requested operation parameter binder owner operand body scope whole capture tail handler inputType
    selection clause closed environmentReady, authenticated⟩

/-- Retrieval exposes checked source, not just membership in a registry. -/
theorem certified_source (certificate : Certified operations policy contracts tables owner capture)
    (known : contracts owner = some contract) :
    ∃ receiver before after, Nonempty (SavedSource operations policy contracts tables receiver capture before after contract) := by
  cases certificate with
  | saved actual source =>
      cases Option.some.inj (actual.symm.trans known)
      exact ⟨_, _, _, ⟨source⟩⟩

theorem certified_rechecks (certificate : Certified operations policy contracts tables owner capture)
    (known : contracts owner = some contract) :
    ∃ receiver before after originalRow, ∃ requirements : SourceReinterpretation.Requirements,
      requirements.evaluate (OwnerPhases.ofStack tables receiver) = some originalRow ∧
      EffectBounds.Covers contract.resumeRow originalRow ∧
      (∀ receiving row, requirements.evaluate (OwnerPhases.ofStack tables receiving) = some row →
        Segment operations policy contracts tables receiving capture before contract.input after contract.answer contract.resumeDemand row) := by
  obtain ⟨receiver, before, after, ⟨saved⟩⟩ := certified_source certificate known
  obtain ⟨requirements, original, recheck⟩ := SourceReinterpretation.segment_rechecks saved.source
  exact ⟨receiver, before, after, saved.actualRow, requirements, original, saved.covered, recheck⟩

/-- The resumed capture and every nested capture remain authenticated while
    the selected source requirements are available for checking at this caller. -/
theorem resume_with_requirements
    (retained : Retained operations policy contracts tables (front.append (.live owner input answer capture caller tail)))
    (known : contracts owner = some contract)
    (resolved : scope.resolve binder = some owner) (closed : ClosedValue value) :
    RawStep ⟨.resume binder value, scope, front.append (.live owner input answer capture caller tail)⟩
      ⟨value, scope, capture.append (front.append (.spent owner answer caller tail))⟩ [] [.ticket owner] ∧
    Retained operations policy contracts tables (capture.append (front.append (.spent owner answer caller tail))) ∧
    ∃ receiver before after originalRow, ∃ requirements : SourceReinterpretation.Requirements,
      requirements.evaluate (OwnerPhases.ofStack tables receiver) = some originalRow ∧
      (∀ actual, requirements.evaluate (OwnerPhases.ofStack tables (front.append (.spent owner answer caller tail))) = some actual →
        Segment operations policy contracts tables (front.append (.spent owner answer caller tail)) capture
          before contract.input after contract.answer contract.resumeDemand actual) := by
  obtain ⟨certificate, saved, first, rest⟩ := selected retained
  obtain ⟨receiver, before, after, originalRow, requirements, original, covered, recheck⟩ := certified_rechecks certificate known
  exact ⟨.resume binder owner scope caller input answer front capture tail value closed resolved, resume retained,
    receiver, before, after, originalRow, requirements, original, fun actual checked => recheck _ actual checked⟩

namespace Examples
open OwnerPhaseTransitions (empty)

def operations : Operations := fun _ _ => none
def tables : CallableProtectionFrames.Tables := fun _ => []
def policy : Syntax.TicketPolicy := fun _ => ⟨true, true⟩
def contract : ResumeContract := ⟨.scalar, .scalar, false, [], [], [], none⟩
def contracts : Contracts := fun owner => if owner = 19 ∨ owner = 29 then some contract else none
def missing : Stack := .live 23 .unit .unit .nil .none .nil
def nested : Stack := .live 29 .unit .unit missing .none .nil
def outer : Stack := .live 19 .unit .unit nested .none .nil

theorem known_outer : contracts 19 = some contract := by decide
theorem known_inner : contracts 29 = some contract := by decide

/-- The old active-segment rule alone skips the inner owner's dormant code. -/
theorem active_segment_skips_missing :
    Segment operations policy contracts tables .nil nested empty .scalar empty .scalar [] [] :=
  .live known_inner rfl rfl .nil

def outerSaved : SavedSource operations policy contracts tables .nil nested empty empty contract :=
  ⟨[], active_segment_skips_missing, EffectBounds.covers_refl [], rfl⟩

theorem outer_certificate_alone : Certified operations policy contracts tables 19 nested :=
  .saved known_outer outerSaved

theorem missing_certificate_rejected : ¬ Certified operations policy contracts tables 23 .nil := by
  intro certificate
  cases certificate with
  | saved known source => simp [contracts] at known

theorem nested_missing_rejected : ¬ Retained operations policy contracts tables outer := by
  intro retained
  cases retained with
  | live certificate saved rest => cases saved with
      | live certificate saved rest => cases saved with
          | live certificate saved rest => exact missing_certificate_rejected certificate

def goodNested : Stack := .live 29 .unit .unit .nil .none .nil
def goodOuter : Stack := .live 19 .unit .unit goodNested .none .nil
def emptySaved : SavedSource operations policy contracts tables .nil .nil empty empty contract :=
  ⟨[], .nil, EffectBounds.covers_refl [], rfl⟩
def nestedSaved : SavedSource operations policy contracts tables .nil goodNested empty empty contract :=
  ⟨[], .live known_inner rfl rfl .nil, EffectBounds.covers_refl [], rfl⟩

theorem nested_admitted : Retained operations policy contracts tables goodOuter :=
  .live (.saved known_outer nestedSaved) (.live (.saved known_inner emptySaved) .nil .nil) .nil

theorem nested_resume_preserved : Retained operations policy contracts tables
    (goodNested.append (.spent 19 .unit .none .nil)) :=
  resume (front := Stack.nil) nested_admitted

theorem nested_disposal_preserved : Retained operations policy contracts tables
    ((closeControl (.ticket 7 19) [.retire 29]).append
      (.push (.closing 41 (.ticket 7 19)) (.spent 19 .unit .none .nil))) :=
  discard (front := Stack.nil) nested_admitted

theorem nested_resume_step :
    RawStep ⟨.resume 7 .unit, .ticket 7 19, goodOuter⟩
      ⟨.unit, .ticket 7 19, goodNested.append (.spent 19 .unit .none .nil)⟩ [] [.ticket 19] ∧
    Retained operations policy contracts tables (goodNested.append (.spent 19 .unit .none .nil)) :=
  ⟨.resume 7 19 (.ticket 7 19) .none .unit .unit .nil goodNested .nil .unit
    CallableProtection.Examples.unit_closed rfl, nested_resume_preserved⟩

theorem nested_disposal_step :
    RawStep ⟨.discard 7, .ticket 7 19, goodOuter⟩
      ⟨.unit, .ticket 7 19, (closeControl (.ticket 7 19) [.retire 29]).append
        (.push (.closing 41 (.ticket 7 19)) (.spent 19 .unit .none .nil))⟩ [.close 41] [.ticket 19] ∧
    Retained operations policy contracts tables ((closeControl (.ticket 7 19) [.retire 29]).append
      (.push (.closing 41 (.ticket 7 19)) (.spent 19 .unit .none .nil))) :=
  ⟨.discard 7 19 41 (.ticket 7 19) .none .unit .unit .nil goodNested .nil [.retire 29] rfl rfl,
    nested_disposal_preserved⟩

end Examples

end Ash.OneShot.CaptureAuthentication

#print axioms Ash.OneShot.CaptureAuthentication.certified_extension
#print axioms Ash.OneShot.CaptureAuthentication.retained_extension
#print axioms Ash.OneShot.CaptureAuthentication.append
#print axioms Ash.OneShot.CaptureAuthentication.decompose
#print axioms Ash.OneShot.CaptureAuthentication.cut
#print axioms Ash.OneShot.CaptureAuthentication.pop
#print axioms Ash.OneShot.CaptureAuthentication.pop_spent
#print axioms Ash.OneShot.CaptureAuthentication.selected
#print axioms Ash.OneShot.CaptureAuthentication.resume
#print axioms Ash.OneShot.CaptureAuthentication.close_control
#print axioms Ash.OneShot.CaptureAuthentication.discard
#print axioms Ash.OneShot.CaptureAuthentication.cell_update
#print axioms Ash.OneShot.CaptureAuthentication.non_capture_step
#print axioms Ash.OneShot.CaptureAuthentication.capture_from_source
#print axioms Ash.OneShot.CaptureAuthentication.capture_step_from_source
#print axioms Ash.OneShot.CaptureAuthentication.certified_source
#print axioms Ash.OneShot.CaptureAuthentication.certified_rechecks
#print axioms Ash.OneShot.CaptureAuthentication.resume_with_requirements
#print axioms Ash.OneShot.CaptureAuthentication.Examples.known_outer
#print axioms Ash.OneShot.CaptureAuthentication.Examples.known_inner
#print axioms Ash.OneShot.CaptureAuthentication.Examples.active_segment_skips_missing
#print axioms Ash.OneShot.CaptureAuthentication.Examples.outer_certificate_alone
#print axioms Ash.OneShot.CaptureAuthentication.Examples.missing_certificate_rejected
#print axioms Ash.OneShot.CaptureAuthentication.Examples.nested_missing_rejected
#print axioms Ash.OneShot.CaptureAuthentication.Examples.nested_admitted
#print axioms Ash.OneShot.CaptureAuthentication.Examples.nested_resume_preserved
#print axioms Ash.OneShot.CaptureAuthentication.Examples.nested_disposal_preserved
#print axioms Ash.OneShot.CaptureAuthentication.Examples.nested_resume_step
#print axioms Ash.OneShot.CaptureAuthentication.Examples.nested_disposal_step
