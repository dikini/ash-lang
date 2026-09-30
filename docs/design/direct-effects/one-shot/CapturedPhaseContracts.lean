import OpenPhaseSegments

/-!
Captured source phase transitions become continuation contracts. Clause source
checking separates local one-shot use from the outside phase changed by resume.
Effect rows are bounds. General registry integration, interior live-owner groups
and complete source preservation remain separate obligations.
-/

namespace Ash.OneShot.CapturedPhaseContracts
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts ProtectionResiduals
open CallableProtectionFrames (Tables contextOf)
open ClauseProtection (Ticket phaseContext)
open ParametricClauseRows (Header)
open Syntax (UseState)

structure Contract where
  header : Header
  sourcePhase : UseState
  resultPhase : UseState
  resumeRow : Footprint
  closeRow : Option Footprint
  deriving DecidableEq, Repr

inductive Closing (operations : Operations) (capture : Stack) (outsideUses : List Nat) : Option Footprint → Prop where
  | protectedCapture (held : ProtectionContexts.protectedMode capture.erase = true) : Closing operations capture outsideUses none
  | outsideObligation (nonempty : outsideUses ≠ []) : Closing operations capture outsideUses none
  | plan (empty : outsideUses = []) (built : makePlan capture = some entries)
      (source : DisposalProtection.Rows operations entries actual)
      (covered : EffectBounds.Covers bound actual) : Closing operations capture outsideUses (some bound)

/-- Source, usage and disposal evidence concern the same saved stack. The
    exact source row is retained beneath its advertised effect bound. -/
structure Interface (operations : Operations) (policy : Syntax.TicketPolicy) (tickets : Syntax.UsageTickets)
    (outer : Ticket) (owner : Nat) (tables : Tables) (fixed capture : Stack) (outside : List Nat) (contract : Contract) where
  actualRow : Footprint
  source : OpenPhaseSegments.Segment operations policy outer owner tables fixed capture
    contract.sourcePhase contract.header.input contract.resultPhase contract.header.answer actualRow
  covered : EffectBounds.Covers contract.resumeRow actualRow
  usage : OpenOwnerUses.Interface policy tickets capture outside
  separate : owner ∉ ownedTickets capture
  held : contract.header.held = ProtectionContexts.protectedMode capture.erase
  closing : Closing operations capture usage.external contract.closeRow

def Interface.extend
    (interface : Interface operations policy tickets outer owner tables fixed capture outside contract)
    (extension : Syntax.UsageExtension tickets larger) : Interface operations policy larger outer owner tables fixed capture outside contract :=
  ⟨interface.actualRow, interface.source, interface.covered,
    ⟨interface.usage.demand, stack_usage_extension interface.usage.source extension⟩,
    interface.separate, interface.held, interface.closing⟩

theorem extension_retains_interface
    (interface : Interface operations policy tickets outer owner tables fixed capture outside contract)
    (extension : Syntax.UsageExtension tickets larger) :
    (interface.extend extension).actualRow = interface.actualRow ∧
      (interface.extend extension).usage.external = interface.usage.external := ⟨rfl, rfl⟩

theorem registry_usage_extension (extension : CallableJoint.RegistryExtends before after) :
    Syntax.UsageExtension before.joint.usage after.joint.usage := by
  intro owner rights known
  cases found : before owner with
  | none => simp [CallableJoint.Registry.joint, ScopedPortJoint.Registry.usage, found] at known
  | some record =>
      have next := extension owner record found
      simpa only [CallableJoint.Registry.joint, ScopedPortJoint.Registry.usage, found, next] using known

theorem interface_phase_monotone
    (interface : Interface operations policy tickets outer owner tables fixed capture outside contract) :
    contract.sourcePhase = .consumed → contract.resultPhase = .consumed :=
  OpenPhaseSegments.segment_phase_monotone interface.source

theorem closing_available
    (closing : Closing operations capture outsideUses (some bound)) :
    outsideUses = [] ∧ ∃ entries actual, makePlan capture = some entries ∧
      DisposalProtection.Rows operations entries actual ∧ EffectBounds.Covers bound actual := by
  cases closing with
  | plan empty built source covered => exact ⟨empty, _, _, built, source, covered⟩

theorem closing_unprotected (closing : Closing operations capture outsideUses (some bound)) :
    ProtectionContexts.protectedMode capture.erase = false := by
  obtain ⟨_, entries, actual, built, _, _⟩ := closing_available closing
  have possible := CaptureInterfaces.plan_available capture
  rw [built] at possible
  simpa using possible.symm

theorem disposal_preserves_outside_phase
    (interface : Interface operations policy tickets outer owner tables fixed capture outside contract)
    (available : contract.closeRow = some bound) : contract.sourcePhase = contract.resultPhase := by
  have closing := interface.closing
  rw [available] at closing
  have empty := (closing_available closing).1
  have source := interface.source
  have monotone := interface_phase_monotone interface
  cases first : contract.sourcePhase <;> cases last : contract.resultPhase
  · rfl
  · rw [first, last] at source
    have present := OpenPhaseSegments.consumed_owner_is_external source interface.usage interface.separate
    rw [empty] at present
    cases present
  · have impossible := monotone first
    rw [last] at impossible
    cases impossible
  · rfl

theorem outside_change_blocks_disposal
    (interface : Interface operations policy tickets outer owner tables fixed capture outside contract)
    (changes : contract.sourcePhase ≠ contract.resultPhase) : contract.closeRow = none := by
  cases available : contract.closeRow with
  | none => rfl
  | some bound => exact False.elim (changes (disposal_preserves_outside_phase interface available))

theorem interface_row_checked
    (interface : Interface operations policy tickets outer owner tables fixed capture outside contract)
    (accepted : checkFootprint receiving contract.resumeRow = true) : checkFootprint receiving interface.actualRow = true :=
  EffectBounds.check_covered accepted interface.covered

structure State where
  localPhase : UseState
  outsidePhase : UseState
  deriving DecidableEq, Repr

/-- The local owner precedes the fixed interpretations and the exposed owner.
    Each phase removes only that owner's barrier, not protected saved frames. -/
def context (contract : Contract) (outer : Ticket) (inside : ProtectionContracts.Context) (state : State) :
    ProtectionContracts.Context :=
  contract.header.context [] state.localPhase ++ phaseContext outer inside state.outsidePhase

def exportAt (contract : Contract) (outer : Ticket) (inside : ProtectionContracts.Context) (state : State) (row : Footprint) :
    Option Footprint := residualize (context contract outer inside state) row

inductive Derives (operations : Operations) (policy : Syntax.TicketPolicy) (contract : Contract)
    (outer : Ticket) (inside : ProtectionContracts.Context) :
    CallableProtection.Environment → State → Code → State → CallableProtection.Contract → Footprint → Prop where
  | stable (summary : Summarizes operations environment code result raw)
      (exported : exportAt contract outer inside state raw = some row) :
      Derives operations policy contract outer inside environment state code state result row
  | pair (left : Derives operations policy contract outer inside environment before a middle first leftRow)
      (right : Derives operations policy contract outer inside environment middle b after second rightRow) :
      Derives operations policy contract outer inside environment before (.pair a b) after (.pair first second) (leftRow ++ rightRow)
  | app (function : Derives operations policy contract outer inside environment before f middle (.function input output latent) functionRow)
      (argument : Derives operations policy contract outer inside environment middle a after input argumentRow)
      (exported : exportAt contract outer inside after latent = some invocationRow) :
      Derives operations policy contract outer inside environment before (.app f a) after output (functionRow ++ argumentRow ++ invocationRow)
  | bind (initializer : Derives operations policy contract outer inside environment before a middle input initializerRow)
      (body : Derives operations policy contract outer inside (environment.extend parameter input) middle b after output bodyRow) :
      Derives operations policy contract outer inside environment before (.bind parameter a b) after output (initializerRow ++ bodyRow)
  | branch (condition : Derives operations policy contract outer inside environment before test middle .scalar conditionRow)
      (yes : Derives operations policy contract outer inside environment middle a after output yesRow)
      (no : Derives operations policy contract outer inside environment middle b after output noRow) :
      Derives operations policy contract outer inside environment before (.branch test a b) after output (conditionRow ++ yesRow ++ noRow)
  | perform (known : operations effect operation = some (input, output))
      (operand : Derives operations policy contract outer inside environment before value after input operandRow)
      (exported : exportAt contract outer inside after [⟨effect, operation, false⟩] = some requestRow) :
      Derives operations policy contract outer inside environment before (.perform (Instantiation.freezeEffect effect) operation value)
        after output (operandRow ++ requestRow)
  | resume (allowed : (policy contract.header.binder).resume = true)
      (operand : Derives operations policy contract outer inside environment before value
        ⟨.available, contract.sourcePhase⟩ contract.header.input operandRow) :
      Derives operations policy contract outer inside environment before (.resume contract.header.binder value)
        ⟨.consumed, contract.resultPhase⟩ contract.header.answer (operandRow ++ contract.resumeRow)
  | discard (allowed : (policy contract.header.binder).dispose = true) (unprotected : contract.header.held = false)
      (available : contract.closeRow = some bound)
      (exported : residualize (.barrier true :: phaseContext outer inside contract.sourcePhase) bound = some row) :
      Derives operations policy contract outer inside environment ⟨.available, contract.sourcePhase⟩ (.discard contract.header.binder)
        ⟨.consumed, contract.sourcePhase⟩ .scalar row
  | cleanup (callback : Derives operations policy contract outer inside environment before action middle (.function .scalar .scalar latent) callbackRow)
      (body : Derives operations policy contract outer inside environment middle code after output bodyRow)
      (exported : residualize (.barrier true :: context contract outer inside after) latent = some executionRow) :
      Derives operations policy contract outer inside environment before (.cleanup action code) after output
        (callbackRow ++ bodyRow ++ executionRow)
  | resource {world : List Nat} {bodyRow : Nat → Footprint}
      (initializer : Derives operations policy contract outer inside environment before initial after .scalar initialRow)
      (body : ∀ identity, identity ∉ world → Summarizes operations environment
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output (bodyRow identity))
      (outward : ∀ identity, identity ∉ world → outsideCell identity (bodyRow identity) = raw)
      (exported : exportAt contract outer inside after raw = some row) :
      Derives operations policy contract outer inside environment before (.resource binder initial code) after output (initialRow ++ row)

theorem local_usage (source : Derives operations policy contract outer inside environment before code after result row) :
    Uses policy (.ticket contract.header.binder (policy contract.header.binder)) before.localPhase code after.localPhase := by
  induction source with
  | stable summary exported => exact ClauseProtection.stable_usage summary policy _ _
  | pair left right ihLeft ihRight => exact .pair ihLeft ihRight
  | app function argument exported ihFunction ihArgument => exact .app ihFunction ihArgument
  | bind initializer body ihInitializer ihBody => exact .bind ihInitializer ihBody
  | branch condition yes no ihCondition ihYes ihNo => exact .branch ihCondition ihYes ihNo
  | perform known operand exported ih => exact .perform ih
  | resume allowed operand ih => exact .resume allowed ih
  | discard allowed unprotected available exported => exact .discard allowed
  | cleanup callback body exported ihCallback ihBody => exact .cleanup ihCallback ihBody
  | resource initializer body outward exported ih =>
      obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
      exact .resource ih ((instantiation_preserves_usage_iff _ _).mp (ClauseProtection.stable_usage (body identity fresh) policy _ _))

theorem local_phase_monotone (source : Derives operations policy contract outer inside environment before code after result row) :
    before.localPhase = .consumed → after.localPhase = .consumed := Syntax.use_state_monotone (local_usage source)

theorem outside_phase_monotone
    (source : Derives operations policy contract outer inside environment before code after result row)
    (transfer : contract.sourcePhase = .consumed → contract.resultPhase = .consumed) :
    before.outsidePhase = .consumed → after.outsidePhase = .consumed := by
  induction source with
  | stable => exact id
  | pair left right ihLeft ihRight => exact fun spent => ihRight (ihLeft spent)
  | app function argument exported ihFunction ihArgument => exact fun spent => ihArgument (ihFunction spent)
  | bind initializer body ihInitializer ihBody => exact fun spent => ihBody (ihInitializer spent)
  | branch condition yes no ihCondition ihYes ihNo => exact fun spent => ihYes (ihCondition spent)
  | perform known operand exported ih => exact ih
  | resume allowed operand ih => exact fun spent => transfer (ih spent)
  | discard => exact id
  | cleanup callback body exported ihCallback ihBody => exact fun spent => ihBody (ihCallback spent)
  | resource initializer body outward exported ih => exact ih

theorem interface_outside_monotone
    (interface : Interface operations policy tickets outer owner tables fixed capture outside contract)
    (source : Derives operations policy contract outer inside environment before code after result row) :
    before.outsidePhase = .consumed → after.outsidePhase = .consumed :=
  outside_phase_monotone source (interface_phase_monotone interface)

theorem value_summary (source : Derives operations policy contract outer inside environment before value after result row)
    (isValue : value.IsValue) : Summarizes operations environment value result [] ∧ before = after ∧ row = [] := by
  induction source with
  | stable summary exported =>
      have empty := value_has_no_immediate_demands summary isValue
      rw [empty, exportAt, residual_empty] at exported
      cases Option.some.inj exported
      exact ⟨empty ▸ summary, rfl, rfl⟩
  | pair left right ihLeft ihRight =>
      obtain ⟨leftSource, first, emptyLeft⟩ := ihLeft isValue.1
      obtain ⟨rightSource, second, emptyRight⟩ := ihRight isValue.2
      exact ⟨.pair leftSource rightSource, first.trans second, by simp only [emptyLeft, emptyRight, List.nil_append]⟩
  | app | bind | branch | perform | resume | discard | cleanup | resource => cases isValue

theorem substitution
    (source : Derives operations policy contract outer inside (environment.extend name input) before code after result row)
    (replacement : Summarizes operations environment value input []) (closed : ClosedValue value) :
    Derives operations policy contract outer inside environment before (code.subst name value) after result row := by
  cases source with
  | stable summary exported => exact .stable (CallableProtection.substitution summary replacement closed) exported
  | pair left right => exact .pair (substitution left replacement closed) (substitution right replacement closed)
  | app function argument exported => exact .app (substitution function replacement closed) (substitution argument replacement closed) exported
  | bind initializer body =>
      rename_i a middle domain initializerRow parameter b bodyRow
      apply Derives.bind (substitution initializer replacement closed)
      by_cases same : name = parameter
      · subst parameter
        simpa only [ite_true, CallableProtection.Environment.extend_shadow] using body
      · simp only [if_neg same]
        have rearranged := body
        rw [CallableProtection.Environment.extend_commute environment name parameter input domain same] at rearranged
        exact substitution rearranged (closed_value_environment replacement closed (environment.extend parameter domain)) closed
  | branch condition yes no =>
      exact .branch (substitution condition replacement closed) (substitution yes replacement closed) (substitution no replacement closed)
  | perform known operand exported => exact .perform known (substitution operand replacement closed) exported
  | resume allowed operand => exact .resume allowed (substitution operand replacement closed)
  | discard allowed unprotected available exported => exact .discard allowed unprotected available exported
  | cleanup callback body exported => exact .cleanup (substitution callback replacement closed) (substitution body replacement closed) exported
  | resource initializer body outward exported =>
      apply Derives.resource (substitution initializer replacement closed) _ outward exported
      intro identity fresh
      rw [Code.instantiation_subst _ name value _ closed.2.1]
      exact CallableProtection.substitution (body identity fresh) replacement closed
termination_by code.nodes
decreasing_by all_goals subst_vars; all_goals simp only [Code.nodes]; all_goals omega

theorem consumed_export (spent : state.localPhase = .consumed) :
    exportAt contract outer inside state demands = ClauseProtection.exportAt outer inside state.outsidePhase demands := by
  simp only [exportAt, context, Header.context, phaseContext, ClauseProtection.ownedMode,
    List.nil_append, spent, List.singleton_append, OpenPhaseSegments.false_prefix_residual,
    ClauseProtection.exportAt, ClauseProtection.phaseContext]

theorem consumed_running_export (spent : state.localPhase = .consumed) :
    residualize (.barrier true :: context contract outer inside state) demands =
      residualize (.barrier true :: phaseContext outer inside state.outsidePhase) demands := by
  simp only [residualize, DisposalProtection.through_barrier]
  exact consumed_export (demands := qualify true demands) spent

/-- After the local owner is spent, the remaining clause code cannot change
    the outside phase again. Its source proof returns to the existing outside
    owner's judgment, retaining the full contract and exported effect row. -/
theorem consumed_to_outer
    (source : Derives operations policy contract outer inside environment before code after result row)
    (spent : before.localPhase = .consumed) :
    after.localPhase = .consumed ∧ before.outsidePhase = after.outsidePhase ∧
      ClauseProtection.Derives operations policy outer inside environment before.outsidePhase code before.outsidePhase result row := by
  induction source with
  | stable summary exported =>
      exact ⟨spent, rfl, .stable summary ((consumed_export spent).symm.trans exported)⟩
  | pair left right ihLeft ihRight =>
      obtain ⟨middleSpent, first, leftSource⟩ := ihLeft spent
      obtain ⟨afterSpent, second, rightSource⟩ := ihRight middleSpent
      rw [← first] at rightSource
      exact ⟨afterSpent, first.trans second, .pair leftSource rightSource⟩
  | app function argument exported ihFunction ihArgument =>
      obtain ⟨middleSpent, first, functionSource⟩ := ihFunction spent
      obtain ⟨afterSpent, second, argumentSource⟩ := ihArgument middleSpent
      have invoked := (consumed_export afterSpent).symm.trans exported
      rw [← second, ← first] at invoked
      rw [← first] at argumentSource
      exact ⟨afterSpent, first.trans second, .app functionSource argumentSource invoked⟩
  | bind initializer body ihInitializer ihBody =>
      obtain ⟨middleSpent, first, initializerSource⟩ := ihInitializer spent
      obtain ⟨afterSpent, second, bodySource⟩ := ihBody middleSpent
      rw [← first] at bodySource
      exact ⟨afterSpent, first.trans second, .bind initializerSource bodySource⟩
  | branch condition yes no ihCondition ihYes ihNo =>
      obtain ⟨middleSpent, first, conditionSource⟩ := ihCondition spent
      obtain ⟨afterSpent, second, yesSource⟩ := ihYes middleSpent
      obtain ⟨_, _, noSource⟩ := ihNo middleSpent
      rw [← first] at yesSource noSource
      exact ⟨afterSpent, first.trans second, .branch conditionSource yesSource noSource⟩
  | perform known operand exported ih =>
      obtain ⟨afterSpent, same, operandSource⟩ := ih spent
      have request := (consumed_export afterSpent).symm.trans exported
      rw [← same] at request
      exact ⟨afterSpent, same, .perform known operandSource request⟩
  | resume allowed operand ih =>
      have impossible := local_phase_monotone operand spent
      cases impossible
  | discard => cases spent
  | cleanup callback body exported ihCallback ihBody =>
      obtain ⟨middleSpent, first, callbackSource⟩ := ihCallback spent
      obtain ⟨afterSpent, second, bodySource⟩ := ihBody middleSpent
      have invoked := (consumed_running_export afterSpent).symm.trans exported
      rw [← second, ← first] at invoked
      rw [← first] at bodySource
      exact ⟨afterSpent, first.trans second, .cleanup callbackSource bodySource invoked⟩
  | resource initializer body outward exported ih =>
      obtain ⟨afterSpent, same, initial⟩ := ih spent
      have invoked := (consumed_export afterSpent).symm.trans exported
      rw [← same] at invoked
      exact ⟨afterSpent, same, .resource initial body outward invoked⟩

theorem unavailable_discard
    (source : Derives operations policy contract outer inside environment before (.discard binder) after result row) :
    ∃ bound, contract.closeRow = some bound := by
  cases source with
  | stable summary exported => cases summary
  | discard allowed unprotected available exported => exact ⟨_, available⟩

theorem changing_capture_cannot_be_discarded
    (interface : Interface operations policy tickets outer owner tables fixed capture outside contract)
    (changes : contract.sourcePhase ≠ contract.resultPhase) :
    ¬ Derives operations policy contract outer inside environment before (.discard binder) after result row := by
  intro source
  obtain ⟨bound, available⟩ := unavailable_discard source
  rw [outside_change_blocks_disposal interface changes] at available
  cases available

theorem local_consumed_cannot_resume
    (source : Derives operations policy contract outer inside environment before (.resume binder operand) after result row)
    (spent : before.localPhase = .consumed) : False := by
  cases source with
  | stable summary exported => cases summary
  | resume allowed operand =>
      have impossible := local_phase_monotone operand spent
      cases impossible

theorem false_head_check (tail : ProtectionContracts.Context) (row : Footprint) :
    checkFootprint (.barrier false :: tail) row = checkFootprint tail row :=
  ClauseProtection.false_barrier_check [] tail row

/-- The two source phases realize two actual nested owner boundaries. -/
theorem context_realizes {fixed : Stack}
    (innerBoundary : PhaseBoundaries.Boundary (contract.header.ticket contract.resumeRow contract.closeRow)
      localOwner state.localPhase localBase (fixed.append outerBase) localAnswer)
    (outerBoundary : PhaseBoundaries.Boundary outer outerOwner state.outsidePhase outerBase tail outerAnswer) :
    checkFootprint (context contract outer (contextOf tables fixed) state ++ contextOf tables tail) row =
      checkFootprint (contextOf tables localBase) row := by
  rcases state with ⟨localPhase, outsidePhase⟩
  cases innerBoundary <;> cases outerBoundary <;>
    simp_all [context, Header.context, Header.ticket, phaseContext, ClauseProtection.ownedMode,
      CallableProtectionFrames.contextOf, ProtectionResiduals.context_append, List.append_assoc]
  all_goals simp only [← List.cons_append, ClauseProtection.false_barrier_check]
  all_goals simp only [List.cons_append, false_head_check]

theorem export_checked_at_boundaries {fixed : Stack}
    (innerBoundary : PhaseBoundaries.Boundary (contract.header.ticket contract.resumeRow contract.closeRow)
      localOwner state.localPhase localBase (fixed.append outerBase) localAnswer)
    (outerBoundary : PhaseBoundaries.Boundary outer outerOwner state.outsidePhase outerBase tail outerAnswer)
    (exported : exportAt contract outer (contextOf tables fixed) state demands = some row) :
    checkFootprint (contextOf tables tail) row = checkFootprint (contextOf tables localBase) demands := by
  have equality := context_realizes (tables := tables) (row := demands) innerBoundary outerBoundary
  rw [← residual_check] at equality
  change checkResidual (contextOf tables tail)
    (exportAt contract outer (contextOf tables fixed) state demands) = _ at equality
  rw [exported] at equality
  exact equality

/-- The source clause is checked against the captured transition, then closed
    parameter substitution preserves both phases and the advertised effects. -/
theorem instantiate_clause
    (bodySource : Derives operations policy contract outer inside (environment.extend parameter argument)
      ⟨.available, contract.sourcePhase⟩ body ⟨.consumed, contract.resultPhase⟩ contract.header.answer row)
    (operandSource : Summarizes operations environment operand argument []) (closed : ClosedValue operand)
    (accepted : checkFootprint outside row = true) :
    Derives operations policy contract outer inside environment ⟨.available, contract.sourcePhase⟩
      (body.subst parameter operand) ⟨.consumed, contract.resultPhase⟩ contract.header.answer row ∧
      checkFootprint outside row = true ∧
      Uses policy (.ticket contract.header.binder (policy contract.header.binder)) .available
        (body.subst parameter operand) .consumed := by
  have instantiated := substitution bodySource operandSource closed
  exact ⟨instantiated, accepted, local_usage instantiated⟩

section Capture
variable {whole capture fixed : Stack} {issued completed : List Owner}

/-- Selected-clause admission uses the phase contract at the actual cut.
    It does not recheck all clause effects at the outside owner's entry phase. -/
theorem capture_clause
    (cut : HandlerCut requested whole capture (fixed.append outerBase) handler)
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩ result outgoing bound)
    (interface : Interface operations policy registry.joint.usage outer outerOwner tables fixed capture
      (activeTickets (fixed.append outerBase)) contract)
    (outerBoundary : PhaseBoundaries.Boundary outer outerOwner contract.sourcePhase outerBase tail outerAnswer)
    (selected : ClauseAt operation handler.clauses parameter contract.header.binder body)
    (known : operations requested operation = some (argument, contract.header.input))
    (bodySource : Derives operations policy contract outer (contextOf tables fixed) (environment.extend parameter argument)
      ⟨.available, contract.sourcePhase⟩ body ⟨.consumed, contract.resultPhase⟩ contract.header.answer row)
    (operandSource : Summarizes operations environment operand argument [])
    (accepted : checkFootprint (contextOf tables tail) row = true)
    (isValue : operand.IsValue) (fresh : (issued ++ [Owner.ticket localOwner]).Nodup) :
    ∃ (output : ScopedPorts.Port) (residual : List Instance) (record : CallableJoint.TicketRecord),
      record.joint = ⟨⟨output, ScopedPorts.eraseType handler.answer, residual, residual⟩, policy contract.header.binder⟩ ∧
      (∃ input, DeclarationResults.signature declarations requested operation = some (input, output)) ∧
      CallableJoint.RegistryExtends registry (registry.insert localOwner record) ∧
      let before : NamedState := ⟨⟨⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩
      let after : Configuration := ⟨body.subst parameter operand, .ticket contract.header.binder localOwner,
        .live localOwner (ScopedPorts.embedPort output) handler.answer capture handler.scope (fixed.append outerBase)⟩
      NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [.ticket localOwner] []) ∧
      CompletionJoint.Valid declarations policy (registry.insert localOwner record) ambient
        (ScopedPortJoint.advanceState before after [.ticket localOwner] []) result outgoing bound ∧
      Derives operations policy contract outer (contextOf tables fixed) environment
        ⟨.available, contract.sourcePhase⟩ after.expression ⟨.consumed, contract.resultPhase⟩ contract.header.answer row ∧
      checkFootprint (contextOf tables tail) row = true ∧
      operations requested operation = some (argument, contract.header.input) ∧
      ∃ retained : Interface operations policy (registry.insert localOwner record).joint.usage outer outerOwner tables fixed capture
        (activeTickets (fixed.append outerBase)) contract,
      retained.actualRow = interface.actualRow ∧ retained.usage.external = interface.usage.external ∧
      ∀ demands, checkFootprint
        (context contract outer (contextOf tables fixed) ⟨.available, contract.sourcePhase⟩ ++ contextOf tables tail) demands =
        checkFootprint (contextOf tables after.stack) demands := by
  obtain ⟨actualParameter, actualBinder, actualBody, output, residual, record, recordEq, chosen, signature,
    extension, step, preserved⟩ := CompletionJoint.capture_without_payload_premise cut valid isValue fresh
  obtain ⟨parameterEq, binderEq, bodyEq⟩ := CaptureAnnotations.clause_selection_unique selected chosen
  cases parameterEq
  cases binderEq
  cases bodyEq
  have closed := PhaseBoundaries.request_operand_closed valid isValue
  obtain ⟨instantiated, checked, usage⟩ := instantiate_clause bodySource operandSource closed accepted
  let retained := interface.extend (registry_usage_extension extension)
  refine ⟨output, residual, record, recordEq, signature, extension, step, preserved, instantiated, checked, known,
    retained, rfl, rfl, ?_⟩
  intro demands
  exact context_realizes (PhaseBoundaries.Boundary.live interface.held) outerBoundary

end Capture

namespace Examples

open OpenOwnerUses.Examples (operations policy tickets tables capture localHandler waiting)
open OpenPhaseSegments.Examples (protectedTicket)

def openContract : Contract := ⟨⟨20, .scalar, .scalar, false⟩, .available, .consumed, [], none⟩

theorem protected_waiting_source : ClauseProtectionFrames.ContextDerives operations policy protectedTicket
    (contextOf tables (.push (.handler localHandler) .nil)) CallableProtection.Environment.empty
    waiting.context .available .scalar .consumed .scalar [] := by
  have value : ClauseProtection.Derives operations policy protectedTicket
      (contextOf tables (.push (.handler localHandler) .nil)) (CallableProtection.Environment.empty.extend 4 .scalar)
      .available .unit .available .scalar [] := .stable .unit rfl
  exact .bind (.resume rfl value rfl)

theorem captured_segment : OpenPhaseSegments.Segment operations policy protectedTicket 9 tables .nil capture
    .available .scalar .consumed .scalar [] :=
  .push (.plain protected_waiting_source (by intro _ _; rfl)) (.push .handler .nil)

def openInterface : Interface operations policy tickets protectedTicket 9 tables .nil capture [9] openContract :=
  ⟨[], captured_segment, EffectBounds.covers_refl [], OpenOwnerUses.Examples.interface, by decide, rfl,
    .outsideObligation (by decide)⟩

theorem empty_plan_is_insufficient : makePlan capture = some [] ∧ openContract.header.held = false ∧
    openContract.closeRow = none := ⟨rfl, rfl, outside_change_blocks_disposal openInterface (by decide)⟩

def initial : State := ⟨.available, .available⟩
def completed : State := ⟨.consumed, .consumed⟩
def request : Code := .perform (Instantiation.freezeEffect (.user 71 [])) 0 .unit
def laterBody : Code := .bind 6 (.resume 20 .unit) request
def earlierBody : Code := .bind 6 request (.resume 20 .unit)
def laterRow : Footprint := [⟨.user 71 [], 0, false⟩]
def earlierRow : Footprint := [⟨.user 71 [], 0, true⟩]

theorem unit_source (environment : CallableProtection.Environment) (state : State) :
    Derives operations policy openContract protectedTicket [] environment state .unit state .scalar [] :=
  .stable .unit (by simp [exportAt, residual_empty])

theorem local_resume_source (environment : CallableProtection.Environment) :
    Derives operations policy openContract protectedTicket [] environment initial (.resume 20 .unit) completed .scalar [] :=
  .resume rfl (unit_source environment initial)

theorem selected_local_clause : ClauseAt 0 localHandler.clauses 2 openContract.header.binder (.resume 20 .unit) := .hit

theorem substituted_local_clause :
    Derives operations policy openContract protectedTicket [] CallableProtection.Environment.empty initial
      ((Code.resume 20 .unit).subst 2 .unit) completed .scalar [] ∧
      checkFootprint [] [] = true ∧
      Uses policy (.ticket 20 (policy 20)) .available ((Code.resume 20 .unit).subst 2 .unit) .consumed :=
  instantiate_clause (parameter := 2) (argument := .scalar)
    (local_resume_source _) .unit CallableProtection.Examples.unit_closed rfl

theorem later_source (environment : CallableProtection.Environment) :
    Derives operations policy openContract protectedTicket [] environment initial laterBody completed .scalar laterRow := by
  have later : Derives operations policy openContract protectedTicket [] (environment.extend 6 .scalar)
      completed request completed .scalar laterRow :=
    .perform (requestRow := laterRow) rfl (unit_source _ _) rfl
  exact .bind (local_resume_source environment) later

theorem later_suffix_returns_to_outer (environment : CallableProtection.Environment) :
    ClauseProtection.Derives operations policy protectedTicket [] environment .consumed request .consumed .scalar laterRow := by
  have source : Derives operations policy openContract protectedTicket [] environment completed request completed .scalar laterRow :=
    .perform (requestRow := laterRow) rfl (unit_source _ _) rfl
  exact (consumed_to_outer source rfl).2.2

theorem earlier_source (environment : CallableProtection.Environment) :
    Derives operations policy openContract protectedTicket [] environment initial earlierBody completed .scalar earlierRow := by
  have earlier : Derives operations policy openContract protectedTicket [] environment initial request initial .scalar earlierRow :=
    .perform (requestRow := earlierRow) rfl (unit_source _ _) rfl
  exact .bind earlier (local_resume_source _)

theorem later_effect_accepted : checkFootprint (contextOf OwnerPhases.Examples.tables OwnerPhases.Examples.tail) laterRow = true := by decide

theorem earlier_effect_rejected : checkFootprint (contextOf OwnerPhases.Examples.tables OwnerPhases.Examples.tail) earlierRow = false := by decide

/-- A flat clause row checked at entry sees the outside owner as still live.
    The phase-aware source places this demand after that owner is consumed. -/
def entryTail : Stack := .live 9 .unit .integer OwnerPhases.Examples.capture .none OwnerPhases.Examples.tail

theorem flat_entry_recheck_rejects_later_row :
    checkFootprint (contextOf OwnerPhases.Examples.tables entryTail) laterRow = false := by decide

theorem local_use_is_one_shot : Uses policy (.ticket 20 (policy 20)) .available laterBody .consumed :=
  local_usage (later_source CallableProtection.Environment.empty)

theorem discard_rejected : ¬ Derives operations policy openContract protectedTicket [] environment initial (.discard 20)
    after result row := changing_capture_cannot_be_discarded openInterface (by decide)

theorem second_local_resume_rejected : ¬ Derives operations policy openContract protectedTicket [] environment completed
    (.resume 20 .unit) after result row := fun source => local_consumed_cannot_resume source rfl

def neutralCapture : Stack := .push (.plain OpenOwnerUses.Examples.return17) .nil
def neutralContract : Contract := ⟨⟨20, .scalar, .scalar, false⟩, .available, .available, [], some []⟩

theorem neutral_segment : OpenPhaseSegments.Segment operations policy protectedTicket 9 tables .nil neutralCapture
    .available .scalar .available .scalar [] := by
  have head : ClauseProtectionFrames.ContextDerives operations policy protectedTicket [] CallableProtection.Environment.empty
      OpenOwnerUses.Examples.return17.context .available .scalar .available .scalar [] := .bind (.stable .integer rfl)
  have frame : OpenPhaseSegments.FrameSource operations policy protectedTicket 9 []
      (.plain OpenOwnerUses.Examples.return17) .available .scalar .available .scalar [] :=
    .plain head (by intro _ impossible; cases impossible)
  unfold neutralCapture
  exact .push (tables := tables) (fixed := .nil) frame .nil

theorem neutral_usage : StackUsage policy tickets neutralCapture [9] [] :=
  .push (.plain (.idle .none (.bind .unit .integer))) (by simp [frameActiveDemand]) .nil

def neutralInterface : Interface operations policy tickets protectedTicket 9 tables .nil neutralCapture [9] neutralContract :=
  ⟨[], neutral_segment, EffectBounds.covers_refl [], ⟨[], neutral_usage⟩, by decide, rfl,
    .plan rfl rfl .nil (EffectBounds.covers_refl [])⟩

theorem neutral_discard_source : Derives operations policy neutralContract protectedTicket [] environment initial (.discard 20)
    ⟨.consumed, .available⟩ .scalar [] := .discard rfl rfl rfl rfl

theorem neutral_discard_preserves_outside : neutralContract.sourcePhase = neutralContract.resultPhase :=
  disposal_preserves_outside_phase neutralInterface rfl

end Examples

end Ash.OneShot.CapturedPhaseContracts

#print axioms Ash.OneShot.CapturedPhaseContracts.extension_retains_interface
#print axioms Ash.OneShot.CapturedPhaseContracts.registry_usage_extension
#print axioms Ash.OneShot.CapturedPhaseContracts.interface_phase_monotone
#print axioms Ash.OneShot.CapturedPhaseContracts.closing_available
#print axioms Ash.OneShot.CapturedPhaseContracts.closing_unprotected
#print axioms Ash.OneShot.CapturedPhaseContracts.disposal_preserves_outside_phase
#print axioms Ash.OneShot.CapturedPhaseContracts.outside_change_blocks_disposal
#print axioms Ash.OneShot.CapturedPhaseContracts.interface_row_checked
#print axioms Ash.OneShot.CapturedPhaseContracts.local_usage
#print axioms Ash.OneShot.CapturedPhaseContracts.local_phase_monotone
#print axioms Ash.OneShot.CapturedPhaseContracts.outside_phase_monotone
#print axioms Ash.OneShot.CapturedPhaseContracts.interface_outside_monotone
#print axioms Ash.OneShot.CapturedPhaseContracts.value_summary
#print axioms Ash.OneShot.CapturedPhaseContracts.substitution
#print axioms Ash.OneShot.CapturedPhaseContracts.consumed_export
#print axioms Ash.OneShot.CapturedPhaseContracts.consumed_running_export
#print axioms Ash.OneShot.CapturedPhaseContracts.consumed_to_outer
#print axioms Ash.OneShot.CapturedPhaseContracts.unavailable_discard
#print axioms Ash.OneShot.CapturedPhaseContracts.changing_capture_cannot_be_discarded
#print axioms Ash.OneShot.CapturedPhaseContracts.local_consumed_cannot_resume
#print axioms Ash.OneShot.CapturedPhaseContracts.false_head_check
#print axioms Ash.OneShot.CapturedPhaseContracts.context_realizes
#print axioms Ash.OneShot.CapturedPhaseContracts.export_checked_at_boundaries
#print axioms Ash.OneShot.CapturedPhaseContracts.instantiate_clause
#print axioms Ash.OneShot.CapturedPhaseContracts.capture_clause
#print axioms Ash.OneShot.CapturedPhaseContracts.Examples.protected_waiting_source
#print axioms Ash.OneShot.CapturedPhaseContracts.Examples.captured_segment
#print axioms Ash.OneShot.CapturedPhaseContracts.Examples.empty_plan_is_insufficient
#print axioms Ash.OneShot.CapturedPhaseContracts.Examples.unit_source
#print axioms Ash.OneShot.CapturedPhaseContracts.Examples.local_resume_source
#print axioms Ash.OneShot.CapturedPhaseContracts.Examples.selected_local_clause
#print axioms Ash.OneShot.CapturedPhaseContracts.Examples.substituted_local_clause
#print axioms Ash.OneShot.CapturedPhaseContracts.Examples.later_source
#print axioms Ash.OneShot.CapturedPhaseContracts.Examples.later_suffix_returns_to_outer
#print axioms Ash.OneShot.CapturedPhaseContracts.Examples.earlier_source
#print axioms Ash.OneShot.CapturedPhaseContracts.Examples.later_effect_accepted
#print axioms Ash.OneShot.CapturedPhaseContracts.Examples.earlier_effect_rejected
#print axioms Ash.OneShot.CapturedPhaseContracts.Examples.flat_entry_recheck_rejects_later_row
#print axioms Ash.OneShot.CapturedPhaseContracts.Examples.local_use_is_one_shot
#print axioms Ash.OneShot.CapturedPhaseContracts.Examples.discard_rejected
#print axioms Ash.OneShot.CapturedPhaseContracts.Examples.second_local_resume_rejected
#print axioms Ash.OneShot.CapturedPhaseContracts.Examples.neutral_segment
#print axioms Ash.OneShot.CapturedPhaseContracts.Examples.neutral_usage
#print axioms Ash.OneShot.CapturedPhaseContracts.Examples.neutral_discard_source
#print axioms Ash.OneShot.CapturedPhaseContracts.Examples.neutral_discard_preserves_outside
