import CoherentSourceTypes

/-!
Finite requirements retain source demands before interpreting a receiving
suffix. Rechecking them reconstructs source derivations at changed contexts.
Existing referenced continuation rows remain fixed annotations; recursively
authenticating and specializing those records is a separate obligation.
-/

namespace Ash.OneShot.SourceReinterpretation
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals OwnerSource
open OwnerPhaseTransitions (Phases)

/-- A requirement remembers its position and owner phase. Literal rows come
    from referenced continuation contracts, not newly interpreted operations. -/
inductive Requirements where
  | request : OwnerPhases.Context → Phases → Footprint → Requirements
  | literal : Footprint → Requirements
  | append : Requirements → Requirements → Requirements

def Requirements.evaluate (receiving : OwnerPhases.Context) : Requirements → Option Footprint
  | .request localContext phases raw => exportAt (localContext ++ receiving) phases raw
  | .literal row => some row
  | .append left right => merge (left.evaluate receiving) (right.evaluate receiving)

def Requirements.prepend (nearer : OwnerPhases.Context) : Requirements → Requirements
  | .request localContext phases raw => .request (localContext ++ nearer) phases raw
  | .literal row => .literal row
  | .append left right => .append (left.prepend nearer) (right.prepend nearer)

theorem evaluate_prepend (requirements : Requirements) :
    (requirements.prepend nearer).evaluate receiving = requirements.evaluate (nearer ++ receiving) := by
  induction requirements with
  | request => simp [Requirements.prepend, Requirements.evaluate, List.append_assoc]
  | literal => rfl
  | append left right ihLeft ihRight => simp [Requirements.prepend, Requirements.evaluate, ihLeft, ihRight]

theorem evaluate_append_split
    (checked : (Requirements.append left right).evaluate receiving = some row) :
    ∃ first second, left.evaluate receiving = some first ∧ right.evaluate receiving = some second ∧ row = first ++ second := by
  cases first : left.evaluate receiving <;> cases second : right.evaluate receiving <;>
    simp_all [Requirements.evaluate, merge]

def atom {inside : OwnerPhases.Context} {phases : Phases} {raw row : Footprint}
    (_ : exportAt inside phases raw = some row) : Requirements := .request [] phases raw

theorem atom_original (exported : exportAt inside phases raw = some row) : (atom exported).evaluate inside = some row := exported

theorem atom_rechecked (exported : exportAt inside phases raw = some row)
    (checked : (atom exported).evaluate receiving = some next) : exportAt receiving phases raw = some next := checked

def protectedAtom {inside : OwnerPhases.Context} {phases : Phases} {latent row : Footprint}
    (_ : residualize (.barrier true :: OwnerPhaseTransitions.project inside phases) latent = some row) : Requirements :=
  .request [] phases (qualify true latent)

theorem protected_original
    (exported : residualize (.barrier true :: OwnerPhaseTransitions.project inside phases) latent = some row) :
    (protectedAtom exported).evaluate inside = some row := by
  simpa only [protectedAtom, Requirements.evaluate, List.nil_append, exportAt, residualize, DisposalProtection.through_barrier] using exported

theorem protected_rechecked
    (exported : residualize (.barrier true :: OwnerPhaseTransitions.project inside phases) latent = some row)
    (checked : (protectedAtom exported).evaluate receiving = some next) :
    residualize (.barrier true :: OwnerPhaseTransitions.project receiving phases) latent = some next := by
  simpa only [protectedAtom, Requirements.evaluate, List.nil_append, exportAt, residualize, DisposalProtection.through_barrier] using checked

/-- The new derivation is constructed from finite checks. No equality between
    the old and receiving interpretation contexts is required. -/
theorem source_rechecks
    (source : Derives operations policy contracts inside environment scope before code after result demand row) :
    ∃ requirements : Requirements, requirements.evaluate inside = some row ∧
      ∀ receiving next, requirements.evaluate receiving = some next →
        Derives operations policy contracts receiving environment scope before code after result demand next := by
  induction source with
  | stable summary exported =>
      exact ⟨atom exported, atom_original exported, fun _ _ checked => .stable summary (atom_rechecked exported checked)⟩
  | pair left right ihLeft ihRight =>
      obtain ⟨a, originalA, recheckA⟩ := ihLeft
      obtain ⟨b, originalB, recheckB⟩ := ihRight
      refine ⟨.append a b, by simp [Requirements.evaluate, originalA, originalB, merge], ?_⟩
      intro receiving next checked
      obtain ⟨first, second, checkedA, checkedB, rfl⟩ := evaluate_append_split checked
      exact .pair (recheckA _ _ checkedA) (recheckB _ _ checkedB)
  | app function argument exported ihFunction ihArgument =>
      obtain ⟨a, originalA, recheckA⟩ := ihFunction
      obtain ⟨b, originalB, recheckB⟩ := ihArgument
      refine ⟨.append (.append a b) (atom exported), by simp [Requirements.evaluate, originalA, originalB, atom_original, merge], ?_⟩
      intro receiving next checked
      obtain ⟨both, invocation, checkedBoth, checkedInvocation, rfl⟩ := evaluate_append_split checked
      obtain ⟨first, second, checkedA, checkedB, rfl⟩ := evaluate_append_split checkedBoth
      exact .app (recheckA _ _ checkedA) (recheckB _ _ checkedB) (atom_rechecked exported checkedInvocation)
  | bind initializer body ihInit ihBody =>
      obtain ⟨a, originalA, recheckA⟩ := ihInit
      obtain ⟨b, originalB, recheckB⟩ := ihBody
      refine ⟨.append a b, by simp [Requirements.evaluate, originalA, originalB, merge], ?_⟩
      intro receiving next checked
      obtain ⟨first, second, checkedA, checkedB, rfl⟩ := evaluate_append_split checked
      exact .bind (recheckA _ _ checkedA) (recheckB _ _ checkedB)
  | branch condition yes no ihCondition ihYes ihNo =>
      obtain ⟨a, originalA, recheckA⟩ := ihCondition
      obtain ⟨b, originalB, recheckB⟩ := ihYes
      obtain ⟨c, originalC, recheckC⟩ := ihNo
      refine ⟨.append (.append a b) c, by simp [Requirements.evaluate, originalA, originalB, originalC, merge], ?_⟩
      intro receiving next checked
      obtain ⟨both, last, checkedBoth, checkedC, rfl⟩ := evaluate_append_split checked
      obtain ⟨first, second, checkedA, checkedB, rfl⟩ := evaluate_append_split checkedBoth
      exact .branch (recheckA _ _ checkedA) (recheckB _ _ checkedB) (recheckC _ _ checkedC)
  | perform known operand exported ih =>
      obtain ⟨a, original, recheck⟩ := ih
      refine ⟨.append a (atom exported), by simp [Requirements.evaluate, original, atom_original, merge], ?_⟩
      intro receiving next checked
      obtain ⟨first, request, checkedA, checkedRequest, rfl⟩ := evaluate_append_split checked
      exact .perform known (recheck _ _ checkedA) (atom_rechecked exported checkedRequest)
  | resume known resolved allowed operand transition ih =>
      obtain ⟨a, original, recheck⟩ := ih
      refine ⟨.append a (.literal _), by simp [Requirements.evaluate, original, merge]; rfl, ?_⟩
      intro receiving next checked
      obtain ⟨first, fixed, checkedA, checkedFixed, rfl⟩ := evaluate_append_split checked
      cases Option.some.inj checkedFixed
      exact .resume known resolved allowed (recheck _ _ checkedA) transition
  | discard known resolved allowed unprotected closable transition =>
      exact ⟨.literal _, rfl, fun _ _ checked => by cases Option.some.inj checked; exact .discard known resolved allowed unprotected closable transition⟩
  | cleanup callback body exported ihCallback ihBody =>
      obtain ⟨a, originalA, recheckA⟩ := ihCallback
      obtain ⟨b, originalB, recheckB⟩ := ihBody
      refine ⟨.append (.append a b) (protectedAtom exported), by simp [Requirements.evaluate, originalA, originalB, protected_original, merge], ?_⟩
      intro receiving next checked
      obtain ⟨both, invocation, checkedBoth, checkedInvocation, rfl⟩ := evaluate_append_split checked
      obtain ⟨first, second, checkedA, checkedB, rfl⟩ := evaluate_append_split checkedBoth
      exact .cleanup (recheckA _ _ checkedA) (recheckB _ _ checkedB) (protected_rechecked exported checkedInvocation)
  | resource initializer body outward exported ih =>
      obtain ⟨a, original, recheck⟩ := ih
      refine ⟨.append a (atom exported), by simp [Requirements.evaluate, original, atom_original, merge], ?_⟩
      intro receiving next checked
      obtain ⟨first, remaining, checkedA, checkedRow, rfl⟩ := evaluate_append_split checked
      exact .resource (recheck _ _ checkedA) body outward (atom_rechecked exported checkedRow)

/-- Shared value annotations and ordinary effect allowances also survive the
    reconstruction; rechecking changes only the exported requirement row. -/
theorem shared_source_rechecks
    (source : CoherentSourceTypes.Owners.Derives operations policy contracts inside world environment allowed scope before code after result demand row) :
    ∃ requirements : Requirements, requirements.evaluate inside = some row ∧
      ∀ receiving next, requirements.evaluate receiving = some next →
        CoherentSourceTypes.Owners.Derives operations policy contracts receiving world environment allowed scope before code after result demand next := by
  induction source with
  | stable summary exported =>
      exact ⟨atom exported, atom_original exported, fun _ _ checked => .stable summary (atom_rechecked exported checked)⟩
  | pair left right ihLeft ihRight =>
      obtain ⟨a, originalA, recheckA⟩ := ihLeft
      obtain ⟨b, originalB, recheckB⟩ := ihRight
      refine ⟨.append a b, by simp [Requirements.evaluate, originalA, originalB, merge], ?_⟩
      intro receiving next checked
      obtain ⟨first, second, checkedA, checkedB, rfl⟩ := evaluate_append_split checked
      exact .pair (recheckA _ _ checkedA) (recheckB _ _ checkedB)
  | app function argument admitted exported ihFunction ihArgument =>
      obtain ⟨a, originalA, recheckA⟩ := ihFunction
      obtain ⟨b, originalB, recheckB⟩ := ihArgument
      refine ⟨.append (.append a b) (atom exported), by simp [Requirements.evaluate, originalA, originalB, atom_original, merge], ?_⟩
      intro receiving next checked
      obtain ⟨both, invocation, checkedBoth, checkedInvocation, rfl⟩ := evaluate_append_split checked
      obtain ⟨first, second, checkedA, checkedB, rfl⟩ := evaluate_append_split checkedBoth
      exact .app (recheckA _ _ checkedA) (recheckB _ _ checkedB) admitted (atom_rechecked exported checkedInvocation)
  | bind initializer body ihInit ihBody =>
      obtain ⟨a, originalA, recheckA⟩ := ihInit
      obtain ⟨b, originalB, recheckB⟩ := ihBody
      refine ⟨.append a b, by simp [Requirements.evaluate, originalA, originalB, merge], ?_⟩
      intro receiving next checked
      obtain ⟨first, second, checkedA, checkedB, rfl⟩ := evaluate_append_split checked
      exact .bind (recheckA _ _ checkedA) (recheckB _ _ checkedB)
  | branch condition yes no ihCondition ihYes ihNo =>
      obtain ⟨a, originalA, recheckA⟩ := ihCondition
      obtain ⟨b, originalB, recheckB⟩ := ihYes
      obtain ⟨c, originalC, recheckC⟩ := ihNo
      refine ⟨.append (.append a b) c, by simp [Requirements.evaluate, originalA, originalB, originalC, merge], ?_⟩
      intro receiving next checked
      obtain ⟨both, last, checkedBoth, checkedC, rfl⟩ := evaluate_append_split checked
      obtain ⟨first, second, checkedA, checkedB, rfl⟩ := evaluate_append_split checkedBoth
      exact .branch (recheckA _ _ checkedA) (recheckB _ _ checkedB) (recheckC _ _ checkedC)
  | perform known admitted operand formed exported ih =>
      obtain ⟨a, original, recheck⟩ := ih
      refine ⟨.append a (atom exported), by simp [Requirements.evaluate, original, atom_original, merge], ?_⟩
      intro receiving next checked
      obtain ⟨first, request, checkedA, checkedRequest, rfl⟩ := evaluate_append_split checked
      exact .perform known admitted (recheck _ _ checkedA) formed (atom_rechecked exported checkedRequest)
  | resume known resolved permission operand transition admitted formed ih =>
      obtain ⟨a, original, recheck⟩ := ih
      refine ⟨.append a (.literal _), by simp [Requirements.evaluate, original, merge]; rfl, ?_⟩
      intro receiving next checked
      obtain ⟨first, fixed, checkedA, checkedFixed, rfl⟩ := evaluate_append_split checked
      cases Option.some.inj checkedFixed
      exact .resume known resolved permission (recheck _ _ checkedA) transition admitted formed
  | discard known resolved permission unprotected closable transition admitted =>
      exact ⟨.literal _, rfl, fun _ _ checked => by cases Option.some.inj checked; exact .discard known resolved permission unprotected closable transition admitted⟩
  | cleanup callback body admitted exported ihCallback ihBody =>
      obtain ⟨a, originalA, recheckA⟩ := ihCallback
      obtain ⟨b, originalB, recheckB⟩ := ihBody
      refine ⟨.append (.append a b) (protectedAtom exported), by simp [Requirements.evaluate, originalA, originalB, protected_original, merge], ?_⟩
      intro receiving next checked
      obtain ⟨both, invocation, checkedBoth, checkedInvocation, rfl⟩ := evaluate_append_split checked
      obtain ⟨first, second, checkedA, checkedB, rfl⟩ := evaluate_append_split checkedBoth
      exact .cleanup (recheckA _ _ checkedA) (recheckB _ _ checkedB) admitted (protected_rechecked exported checkedInvocation)
  | resource initializer body formed effectsBound admitted outward exported ih =>
      obtain ⟨a, original, recheck⟩ := ih
      refine ⟨.append a (atom exported), by simp [Requirements.evaluate, original, atom_original, merge], ?_⟩
      intro receiving next checked
      obtain ⟨first, remaining, checkedA, checkedRow, rfl⟩ := evaluate_append_split checked
      exact .resource (recheck _ _ checkedA) body formed effectsBound admitted outward (atom_rechecked exported checkedRow)

theorem context_rechecks
    (source : ContextDerives operations policy contracts inside environment scope position before input after output demand row) :
    ∃ requirements : Requirements, requirements.evaluate inside = some row ∧
      ∀ receiving next, requirements.evaluate receiving = some next →
        ContextDerives operations policy contracts receiving environment scope position before input after output demand next := by
  cases source with
  | pairLeft right =>
      obtain ⟨a, original, recheck⟩ := source_rechecks right
      exact ⟨a, original, fun _ _ checked => .pairLeft (recheck _ _ checked)⟩
  | pairRight left =>
      exact ⟨.literal [], rfl, fun _ _ checked => by cases Option.some.inj checked; exact .pairRight left⟩
  | appFunction argument exported =>
      obtain ⟨a, original, recheck⟩ := source_rechecks argument
      refine ⟨.append a (atom exported), by simp [Requirements.evaluate, original, atom_original, merge], ?_⟩
      intro receiving next checked
      obtain ⟨first, invocation, checkedA, checkedInvocation, rfl⟩ := evaluate_append_split checked
      exact .appFunction (recheck _ _ checkedA) (atom_rechecked exported checkedInvocation)
  | appArgument function exported =>
      exact ⟨atom exported, atom_original exported, fun _ _ checked => .appArgument function (atom_rechecked exported checked)⟩
  | bind body =>
      obtain ⟨a, original, recheck⟩ := source_rechecks body
      exact ⟨a, original, fun _ _ checked => .bind (recheck _ _ checked)⟩
  | branch yes no =>
      obtain ⟨a, originalA, recheckA⟩ := source_rechecks yes
      obtain ⟨b, originalB, recheckB⟩ := source_rechecks no
      refine ⟨.append a b, by simp [Requirements.evaluate, originalA, originalB, merge], ?_⟩
      intro receiving next checked
      obtain ⟨first, second, checkedA, checkedB, rfl⟩ := evaluate_append_split checked
      exact .branch (recheckA _ _ checkedA) (recheckB _ _ checkedB)
  | perform known exported =>
      exact ⟨atom exported, atom_original exported, fun _ _ checked => .perform known (atom_rechecked exported checked)⟩
  | resume known resolved allowed transition =>
      exact ⟨.literal _, rfl, fun _ _ checked => by cases Option.some.inj checked; exact .resume known resolved allowed transition⟩
  | cleanup body exported =>
      obtain ⟨a, original, recheck⟩ := source_rechecks body
      refine ⟨.append a (protectedAtom exported), by simp [Requirements.evaluate, original, protected_original, merge], ?_⟩
      intro receiving next checked
      obtain ⟨first, invocation, checkedA, checkedInvocation, rfl⟩ := evaluate_append_split checked
      exact .cleanup (recheck _ _ checkedA) (protected_rechecked exported checkedInvocation)
  | resource body outward exported =>
      exact ⟨atom exported, atom_original exported, fun _ _ checked => .resource body outward (atom_rechecked exported checked)⟩

theorem frame_rechecks
    (source : FrameSource operations policy contracts inside frame before input after output demand row) :
    ∃ requirements : Requirements, requirements.evaluate inside = some row ∧
      ∀ receiving next, requirements.evaluate receiving = some next →
        FrameSource operations policy contracts receiving frame before input after output demand next := by
  cases source with
  | plain context =>
      obtain ⟨a, original, recheck⟩ := context_rechecks context
      exact ⟨a, original, fun _ _ checked => .plain (recheck _ _ checked)⟩
  | handler => exact ⟨.literal [], rfl, fun _ _ checked => by cases Option.some.inj checked; exact .handler⟩
  | cell => exact ⟨.literal [], rfl, fun _ _ checked => by cases Option.some.inj checked; exact .cell⟩
  | armed callback exported =>
      exact ⟨atom exported, atom_original exported, fun _ _ checked => .armed callback (atom_rechecked exported checked)⟩
  | running saved => exact ⟨.literal [], rfl, fun _ _ checked => by cases Option.some.inj checked; exact .running saved⟩
  | closing => exact ⟨.literal [], rfl, fun _ _ checked => by cases Option.some.inj checked; exact .closing⟩
  | retiring transition => exact ⟨.literal [], rfl, fun _ _ checked => by cases Option.some.inj checked; exact .retiring transition⟩

/-- A frame's obligations are located before its remaining saved frames and
    the supplied receiver. Induction covers live and spent owner boundaries. -/
theorem segment_rechecks
    (source : Segment operations policy contracts tables fixed capture before input after output demand row) :
    ∃ requirements : Requirements, requirements.evaluate (OwnerPhases.ofStack tables fixed) = some row ∧
      ∀ receiving next, requirements.evaluate (OwnerPhases.ofStack tables receiving) = some next →
        Segment operations policy contracts tables receiving capture before input after output demand next := by
  induction source with
  | nil => exact ⟨.literal [], rfl, fun _ _ checked => by cases Option.some.inj checked; exact .nil⟩
  | push head tail ih =>
      rename_i frame start input middle intermediate headDemand headRow rest finish output tailDemand tailRow
      obtain ⟨a, originalA, recheckA⟩ := frame_rechecks head
      obtain ⟨b, originalB, recheckB⟩ := ih
      refine ⟨.append (a.prepend (OwnerPhases.ofStack tables rest)) b, ?_, ?_⟩
      · simp only [Requirements.evaluate, evaluate_prepend, ← OwnerPhases.stack_append, originalA, originalB, merge]
      · intro receiving next checked
        obtain ⟨first, second, checkedA, checkedB, rfl⟩ := evaluate_append_split checked
        rw [evaluate_prepend, ← OwnerPhases.stack_append] at checkedA
        exact .push (recheckA _ _ checkedA) (recheckB _ _ checkedB)
  | live known held consumed tail ih =>
      obtain ⟨a, original, recheck⟩ := ih
      exact ⟨a, original, fun _ _ checked => .live known held consumed (recheck _ _ checked)⟩
  | spent known consumed tail ih =>
      obtain ⟨a, original, recheck⟩ := ih
      exact ⟨a, original, fun _ _ checked => .spent known consumed (recheck _ _ checked)⟩

theorem saved_rechecks
    (saved : OwnerCaptureContracts.SavedSource operations policy contracts tables fixed capture before after contract) :
    ∃ requirements : Requirements, requirements.evaluate (OwnerPhases.ofStack tables fixed) = some saved.actualRow ∧
      ∀ receiving next, requirements.evaluate (OwnerPhases.ofStack tables receiving) = some next →
        EffectBounds.Covers contract.resumeRow next →
        ∃ moved : OwnerCaptureContracts.SavedSource operations policy contracts tables receiving capture before after contract,
          moved.actualRow = next := by
  obtain ⟨requirements, original, recheck⟩ := segment_rechecks saved.source
  exact ⟨requirements, original, fun _ _ checked covered => ⟨⟨_, recheck _ _ checked, covered, saved.held⟩, rfl⟩⟩

/-- Successful re-evaluation and the advertised bound supply the old restoration
    theorem's saved-segment premise, even when interpretation changes. -/
theorem restore_rechecked {front tail fixed capture : Stack}
    (saved : OwnerCaptureContracts.SavedSource operations policy contracts tables (tail.append fixed) capture before capturedAfter contract)
    (consumed : before owner = .consumed)
    (source : Source operations policy contracts tables fixed outside scope (.resume binder value)
      (front.append (.live owner inputType answerType capture caller tail))
      (OwnerPhaseTransitions.introduce before owner) after output demand row)
    (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner) (isValue : value.IsValue) :
    ∃ requirements : Requirements, requirements.evaluate (OwnerPhases.ofStack tables (tail.append fixed)) = some saved.actualRow ∧
      ∀ actual, requirements.evaluate (OwnerPhases.ofStack tables ((front.append (.spent owner answerType caller tail)).append fixed)) = some actual →
        EffectBounds.Covers contract.resumeRow actual →
        ∃ remaining restRow,
          demand = owner :: (contract.resumeDemand ++ remaining) ∧ row = contract.resumeRow ++ restRow ∧
          Source operations policy contracts tables fixed outside scope value
            (capture.append (front.append (.spent owner answerType caller tail)))
            before after output (contract.resumeDemand ++ remaining) (actual ++ restRow) := by
  obtain ⟨requirements, original, recheck⟩ := saved_rechecks saved
  refine ⟨requirements, original, ?_⟩
  intro actual checked covered
  obtain ⟨moved, same⟩ := recheck _ _ checked covered
  obtain ⟨remaining, restRow, names, effects, restored⟩ := OwnerSourceResumption.restored_source source known resolved isValue
    (OwnerCaptureContracts.saved_resume_segment moved consumed) moved.covered
  rw [OwnerCaptureContracts.spend_introduced consumed, same] at restored
  exact ⟨remaining, restRow, names, effects, restored⟩

namespace Examples
open OwnerPhaseTransitions (empty)

def firstEffect : Instance := .user 81 []
def secondEffect : Instance := .user 82 []
def firstRow : Footprint := [⟨firstEffect, 0, false⟩]
def secondRow : Footprint := [⟨secondEffect, 0, false⟩]
def quiet : ClauseContract := ⟨false, some [], some []⟩
def emitting : ClauseContract := ⟨false, some secondRow, some secondRow⟩
def originalContext : OwnerPhases.Context := [.ordinary (.handler firstEffect 1 [(0, quiet)])]
def changedContext : OwnerPhases.Context := [.ordinary (.handler firstEffect 2 [(0, emitting)])]

theorem original_hides_request : exportAt originalContext empty firstRow = some [] := by decide
theorem changed_exposes_request : exportAt changedContext empty firstRow = some secondRow := by decide

/-- The old result has erased information: an empty source and a handled
    request have the same cached row but different requirements after rebasing. -/
theorem cached_row_cannot_determine_reinterpretation :
    ¬ ∃ transport : Option Footprint → Option Footprint,
      ∀ raw, transport (exportAt originalContext empty raw) = exportAt changedContext empty raw := by
  rintro ⟨transport, correct⟩
  have noRequest := correct []
  have request := correct firstRow
  simp only [exportAt, residual_empty] at noRequest
  rw [original_hides_request, changed_exposes_request, noRequest] at request
  cases request

def requirements : Requirements := atom original_hides_request

theorem retained_requirement_changes : requirements.evaluate originalContext = some [] ∧
    requirements.evaluate changedContext = some secondRow := ⟨original_hides_request, changed_exposes_request⟩

def originalHandler : HandlerData := ⟨1, firstEffect, .cons 0 0 7 (.resume 7 .unit) .nil, .none, .unit, rfl⟩
def changedHandler : HandlerData :=
  ⟨2, firstEffect, .cons 0 0 7 (.bind 8 (.perform (Instantiation.freezeEffect secondEffect) 0 .unit) (.resume 7 .unit)) .nil,
    .none, .unit, rfl⟩
def capturedHandler : HandlerData := ⟨3, secondEffect, .cons 0 0 7 (.resume 7 .unit) .nil, .none, .unit, rfl⟩
def tables : CallableProtectionFrames.Tables := fun handler => if handler.activation = 2 then [(0, emitting)] else [(0, quiet)]
def original : Stack := .push (.handler originalHandler) .nil
def receiving : Stack := .push (.handler changedHandler) .nil
def pending : PlainData := ⟨.perform (Instantiation.freezeEffect firstEffect) 0, .none, .unit, .unit, [], rfl⟩
def capture : Stack := .push (.plain pending) (.push (.handler capturedHandler) .nil)
def operations : CallableProtection.Operations := fun effect operation =>
  if effect = firstEffect ∧ operation = 0 then some (.scalar, .scalar) else none
def policy : Syntax.TicketPolicy := fun _ => ActionRequirements.resumeOnly
def contracts : OwnerSource.Contracts := fun _ => none

theorem selected_cut : HandlerCut secondEffect (capture.append original) capture original capturedHandler := by
  exact .push (.plain pending) _ _ _ _ (by decide) (.hit capturedHandler original rfl)

theorem captured_source : Segment operations policy contracts tables original capture empty .scalar empty .scalar [] [] := by
  have known : operations firstEffect 0 = some (.scalar, .scalar) := by decide
  have head : FrameSource operations policy contracts
      (OwnerPhases.ofStack tables ((Stack.push (.handler capturedHandler) .nil).append original))
      (.plain pending) empty .scalar empty .scalar [] [] :=
    .plain (environment := CallableProtection.Environment.empty) (.perform known (by decide))
  exact .push head (.push .handler .nil)

def locatedRequirements : Requirements :=
  .append (.request (OwnerPhases.ofStack tables (.push (.handler capturedHandler) .nil)) empty firstRow) (.literal [])

theorem located_original : locatedRequirements.evaluate (OwnerPhases.ofStack tables original) = some [] := by decide
theorem located_changed : locatedRequirements.evaluate (OwnerPhases.ofStack tables receiving) = some secondRow := by decide

theorem located_reconstructs (checked : locatedRequirements.evaluate (OwnerPhases.ofStack tables suffix) = some row) :
    Segment operations policy contracts tables suffix capture empty .scalar empty .scalar [] row := by
  have identity (value : Option Footprint) : merge value (some []) = value := by cases value <;> simp [merge]
  have exported : exportAt (OwnerPhases.ofStack tables ((Stack.push (.handler capturedHandler) .nil).append suffix)) empty firstRow = some row := by
    simpa only [locatedRequirements, Requirements.evaluate, identity, OwnerPhases.stack_append] using checked
  have known : operations firstEffect 0 = some (.scalar, .scalar) := by decide
  have head : FrameSource operations policy contracts
      (OwnerPhases.ofStack tables ((Stack.push (.handler capturedHandler) .nil).append suffix))
      (.plain pending) empty .scalar empty .scalar [] row :=
    .plain (environment := CallableProtection.Environment.empty) (.perform known exported)
  have tail : Segment operations policy contracts tables suffix (.push (.handler capturedHandler) .nil)
      empty .scalar empty .scalar [] [] := .push .handler .nil
  have result := Segment.push head tail
  simpa only [List.append_nil, capture] using result

theorem changed_source : Segment operations policy contracts tables receiving capture empty .scalar empty .scalar [] secondRow :=
  located_reconstructs located_changed

theorem old_bound_rejects_new_requirement : ¬ EffectBounds.Covers [] secondRow := by
  intro covered
  exact List.not_mem_nil (covered List.mem_cons_self)

theorem inner_handler_does_not_catch_outer_emission :
    locatedRequirements.evaluate (OwnerPhases.ofStack tables receiving) = some secondRow ∧ secondRow ≠ [] :=
  ⟨located_changed, by decide⟩

def rejectingContext : OwnerPhases.Context :=
  [.ordinary (.barrier true), .ordinary (.handler firstEffect 4 [(0, ⟨true, some [], none⟩)])]

theorem new_protection_rejects_disposal : requirements.evaluate rejectingContext = none := by decide

end Examples

end Ash.OneShot.SourceReinterpretation

#print axioms Ash.OneShot.SourceReinterpretation.evaluate_prepend
#print axioms Ash.OneShot.SourceReinterpretation.evaluate_append_split
#print axioms Ash.OneShot.SourceReinterpretation.atom_original
#print axioms Ash.OneShot.SourceReinterpretation.atom_rechecked
#print axioms Ash.OneShot.SourceReinterpretation.protected_original
#print axioms Ash.OneShot.SourceReinterpretation.protected_rechecked
#print axioms Ash.OneShot.SourceReinterpretation.source_rechecks
#print axioms Ash.OneShot.SourceReinterpretation.shared_source_rechecks
#print axioms Ash.OneShot.SourceReinterpretation.context_rechecks
#print axioms Ash.OneShot.SourceReinterpretation.frame_rechecks
#print axioms Ash.OneShot.SourceReinterpretation.segment_rechecks
#print axioms Ash.OneShot.SourceReinterpretation.saved_rechecks
#print axioms Ash.OneShot.SourceReinterpretation.restore_rechecked
#print axioms Ash.OneShot.SourceReinterpretation.Examples.original_hides_request
#print axioms Ash.OneShot.SourceReinterpretation.Examples.changed_exposes_request
#print axioms Ash.OneShot.SourceReinterpretation.Examples.cached_row_cannot_determine_reinterpretation
#print axioms Ash.OneShot.SourceReinterpretation.Examples.retained_requirement_changes
#print axioms Ash.OneShot.SourceReinterpretation.Examples.selected_cut
#print axioms Ash.OneShot.SourceReinterpretation.Examples.captured_source
#print axioms Ash.OneShot.SourceReinterpretation.Examples.located_original
#print axioms Ash.OneShot.SourceReinterpretation.Examples.located_changed
#print axioms Ash.OneShot.SourceReinterpretation.Examples.located_reconstructs
#print axioms Ash.OneShot.SourceReinterpretation.Examples.changed_source
#print axioms Ash.OneShot.SourceReinterpretation.Examples.old_bound_rejects_new_requirement
#print axioms Ash.OneShot.SourceReinterpretation.Examples.inner_handler_does_not_catch_outer_emission
#print axioms Ash.OneShot.SourceReinterpretation.Examples.new_protection_rejects_disposal
