import CapturedPhaseContracts

/-!
Clause evaluation contexts and actual resumption into an open captured segment.
The local one-shot phase becomes spent immediately; the saved segment supplies
its outside phase transition before the waiting clause continues. This joins
source certificates to execution, not a whole-program source invariant.
-/

namespace Ash.OneShot.PhaseResumption
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts ProtectionResiduals
open CallableProtectionFrames (Tables contextOf)
open ClauseProtection (Ticket phaseContext)
open CapturedPhaseContracts (Derives Interface)
open PhaseContextChains (stackOf)

/-- Equivalent residual interpretation suffices; equality of lists is stronger
    than needed when inserting ordinary evaluation frames or spent markers. -/
theorem phase_residual_congr
    (same : ∀ row, residualize first row = residualize second row) :
    ClauseProtection.exportAt ticket first phase demands = ClauseProtection.exportAt ticket second phase demands := by
  simp only [ClauseProtection.exportAt, phaseContext, residual_append, same]

theorem running_phase_congr
    (same : ∀ row, residualize first row = residualize second row) :
    residualize (.barrier true :: phaseContext ticket first phase) demands =
      residualize (.barrier true :: phaseContext ticket second phase) demands := by
  simp only [residualize, DisposalProtection.through_barrier]
  exact phase_residual_congr same

theorem outer_context_congr
    (source : ClauseProtectionFrames.ContextDerives operations policy ticket first environment position before input after output row)
    (same : ∀ demands, residualize first demands = residualize second demands) :
    ClauseProtectionFrames.ContextDerives operations policy ticket second environment position before input after output row := by
  cases source with
  | pairLeft right => exact .pairLeft (CleanupProtection.inside_congr right same)
  | pairRight left => exact .pairRight left
  | appFunction argument exported =>
      exact .appFunction (CleanupProtection.inside_congr argument same)
        ((phase_residual_congr same).symm.trans exported)
  | appArgument function exported => exact .appArgument function ((phase_residual_congr same).symm.trans exported)
  | bind body => exact .bind (CleanupProtection.inside_congr body same)
  | branch yes no => exact .branch (CleanupProtection.inside_congr yes same) (CleanupProtection.inside_congr no same)
  | perform known exported => exact .perform known ((phase_residual_congr same).symm.trans exported)
  | resume allowed exported => exact .resume allowed ((same _).symm.trans exported)
  | cleanup body exported => exact .cleanup (CleanupProtection.inside_congr body same) ((running_phase_congr same).symm.trans exported)
  | resource body outward exported => exact .resource body outward ((phase_residual_congr same).symm.trans exported)

theorem frame_residual_congr
    (source : OpenPhaseSegments.FrameSource operations policy ticket owner first frame before input after output row)
    (same : ∀ demands, residualize first demands = residualize second demands) :
    OpenPhaseSegments.FrameSource operations policy ticket owner second frame before input after output row := by
  cases source with
  | plain source resolved => exact .plain (outer_context_congr source same) resolved
  | handler => exact .handler
  | cell => exact .cell
  | armed callback exported => exact .armed callback ((phase_residual_congr same).symm.trans exported)
  | running saved => exact .running saved
  | closing => exact .closing
  | retiring => exact .retiring

theorem segment_residual_congr
    (source : OpenPhaseSegments.Segment operations policy ticket owner tables fixed segment before input after output row)
    (same : ∀ demands, residualize (contextOf tables fixed) demands = residualize (contextOf tables replacement) demands) :
    OpenPhaseSegments.Segment operations policy ticket owner tables replacement segment before input after output row := by
  induction source with
  | nil => exact .nil
  | push head tail ih =>
      refine .push (frame_residual_congr head ?_) ih
      intro demands
      simp only [ProtectionResiduals.context_append, residual_append, same]
  | spent tail ih => exact .spent ih

inductive ContextDerives (operations : Operations) (policy : Syntax.TicketPolicy)
    (contract : CapturedPhaseContracts.Contract) (outer : Ticket) (inside : ProtectionContracts.Context)
    (environment : CallableProtection.Environment) :
    ScopedExecution.Context → CapturedPhaseContracts.State → CallableProtection.Contract → CapturedPhaseContracts.State → CallableProtection.Contract → Footprint → Prop where
  | pairLeft (right : Derives operations policy contract outer inside environment middle code after output row) :
      ContextDerives operations policy contract outer inside environment (.pairLeft code) middle input after (.pair input output) row
  | pairRight (left : Summarizes operations environment code input []) :
      ContextDerives operations policy contract outer inside environment (.pairRight code) state output state (.pair input output) []
  | appFunction (argument : Derives operations policy contract outer inside environment middle code after input argumentRow)
      (exported : CapturedPhaseContracts.exportAt contract outer inside after latent = some invocationRow) :
      ContextDerives operations policy contract outer inside environment (.appFunction code) middle (.function input output latent)
        after output (argumentRow ++ invocationRow)
  | appArgument (function : Summarizes operations environment code (.function input output latent) [])
      (exported : CapturedPhaseContracts.exportAt contract outer inside state latent = some invocationRow) :
      ContextDerives operations policy contract outer inside environment (.appArgument code) state input state output invocationRow
  | bind (body : Derives operations policy contract outer inside (environment.extend name input) middle code after output row) :
      ContextDerives operations policy contract outer inside environment (.bind name code) middle input after output row
  | branch (yes : Derives operations policy contract outer inside environment middle a after output yesRow)
      (no : Derives operations policy contract outer inside environment middle b after output noRow) :
      ContextDerives operations policy contract outer inside environment (.branch a b) middle .scalar after output (yesRow ++ noRow)
  | perform (known : operations effect operation = some (input, output))
      (exported : CapturedPhaseContracts.exportAt contract outer inside state [⟨effect, operation, false⟩] = some row) :
      ContextDerives operations policy contract outer inside environment (.perform (Instantiation.freezeEffect effect) operation)
        state input state output row
  | resume (allowed : (policy contract.header.binder).resume = true) : ContextDerives operations policy contract outer inside environment (.resume contract.header.binder)
      ⟨.available, contract.sourcePhase⟩ contract.header.input ⟨.consumed, contract.resultPhase⟩ contract.header.answer contract.resumeRow
  | cleanup (body : Derives operations policy contract outer inside environment middle code after output bodyRow)
      (exported : residualize (.barrier true :: CapturedPhaseContracts.context contract outer inside after) latent = some invocationRow) :
      ContextDerives operations policy contract outer inside environment (.cleanup code) middle (.function .scalar .scalar latent)
        after output (bodyRow ++ invocationRow)
  | resource {world : List Nat} {bodyRow : Nat → Footprint}
      (body : ∀ identity, identity ∉ world → Summarizes operations environment
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output (bodyRow identity))
      (outward : ∀ identity, identity ∉ world → outsideCell identity (bodyRow identity) = raw)
      (exported : CapturedPhaseContracts.exportAt contract outer inside state raw = some row) :
      ContextDerives operations policy contract outer inside environment (.resource binder code) state .scalar state output row

/-- Reconstruct the same direct expression while retaining the permission
    checked at each resumption position. -/
theorem context_plug
    (context : ContextDerives operations policy contract outer inside environment position middle input after output remainder)
    (child : Derives operations policy contract outer inside environment before code middle input row) :
    Derives operations policy contract outer inside environment before (position.plug code) after output (row ++ remainder) := by
  cases context with
  | pairLeft right => exact .pair child right
  | pairRight left =>
      simpa only [ScopedExecution.Context.plug, List.nil_append, List.append_nil] using Derives.pair
        (Derives.stable (row := []) left (by simp [CapturedPhaseContracts.exportAt, residual_empty])) child
  | appFunction argument exported => simpa only [ScopedExecution.Context.plug, List.append_assoc] using Derives.app child argument exported
  | appArgument function exported =>
      simpa only [ScopedExecution.Context.plug, List.nil_append] using Derives.app
        (Derives.stable (row := []) function (by simp [CapturedPhaseContracts.exportAt, residual_empty])) child exported
  | bind body => exact .bind child body
  | branch yes no => simpa only [ScopedExecution.Context.plug, List.append_assoc] using Derives.branch child yes no
  | perform known exported => exact .perform known child exported
  | resume allowed => exact .resume allowed child
  | cleanup body exported => simpa only [ScopedExecution.Context.plug, List.append_assoc] using Derives.cleanup child body exported
  | resource body outward exported => exact .resource child body outward exported

theorem split_export
    (exported : CapturedPhaseContracts.exportAt contract outer inside state (first ++ second) = some row) :
    ∃ firstRow secondRow,
      CapturedPhaseContracts.exportAt contract outer inside state first = some firstRow ∧
      CapturedPhaseContracts.exportAt contract outer inside state second = some secondRow ∧
      row = firstRow ++ secondRow := by
  unfold CapturedPhaseContracts.exportAt at *
  rw [residual_rows_append] at exported
  cases firstExport : residualize (CapturedPhaseContracts.context contract outer inside state) first with
  | none => simp [firstExport, merge] at exported
  | some firstRow =>
      cases secondExport : residualize (CapturedPhaseContracts.context contract outer inside state) second with
      | none => simp [firstExport, secondExport, merge] at exported
      | some secondRow =>
          exact ⟨firstRow, secondRow, rfl, rfl, by simpa [firstExport, secondExport, merge] using exported.symm⟩

theorem stable_context
    (context : CallableProtectionFrames.ContextSummarizes operations environment position input output raw)
    (exported : CapturedPhaseContracts.exportAt contract outer inside state raw = some row) :
    ContextDerives operations policy contract outer inside environment position state input state output row := by
  cases context with
  | pairLeft right => exact .pairLeft (.stable right exported)
  | pairRight left =>
      have empty : row = [] := by simpa [CapturedPhaseContracts.exportAt, residual_empty] using exported.symm
      subst row
      exact .pairRight left
  | appFunction argument =>
      obtain ⟨argumentRow, invocationRow, argumentExport, invocationExport, same⟩ := split_export exported
      subst row
      exact .appFunction (.stable argument argumentExport) invocationExport
  | appArgument function => exact .appArgument function exported
  | bind body => exact .bind (.stable body exported)
  | branch yes no =>
      obtain ⟨yesRow, noRow, yesExport, noExport, same⟩ := split_export exported
      subst row
      exact .branch (.stable yes yesExport) (.stable no noExport)
  | perform known => exact .perform known exported
  | cleanup body =>
      obtain ⟨bodyRow, invocationRow, bodyExport, invocationExport, same⟩ := split_export exported
      subst row
      exact .cleanup (.stable body bodyExport) (by
        simp only [residualize, DisposalProtection.through_barrier]
        exact invocationExport)
  | resource body outward => exact .resource body outward exported

theorem focus_decompose
    (checked : Derives operations policy contract outer inside environment before whole after output row)
    (focus : Focus whole child position) :
    ∃ middle input childRow remainder,
      Derives operations policy contract outer inside environment before child middle input childRow ∧
      ContextDerives operations policy contract outer inside environment position middle input after output remainder ∧
      row = childRow ++ remainder := by
  cases checked with
  | stable summary exported =>
      obtain ⟨input, childRaw, remainingRaw, childSummary, context, same⟩ :=
        CallableProtectionFrames.focus_decompose summary focus
      rw [same] at exported
      obtain ⟨childRow, remainder, childExport, remainderExport, same⟩ := split_export exported
      exact ⟨_, input, childRow, remainder, .stable childSummary childExport, stable_context context remainderExport, same⟩
  | pair left right => cases focus with
      | pairLeft => exact ⟨_, _, _, _, left, .pairLeft right, rfl⟩
      | pairRight value =>
          obtain ⟨summary, same, empty⟩ := CapturedPhaseContracts.value_summary left value
          subst_vars
          exact ⟨_, _, _, _, right, .pairRight summary, by simp⟩
  | app function argument exported => cases focus with
      | appFunction => exact ⟨_, _, _, _, function, .appFunction argument exported, List.append_assoc ..⟩
      | appArgument value =>
          obtain ⟨summary, same, empty⟩ := CapturedPhaseContracts.value_summary function value
          subst_vars
          exact ⟨_, _, _, _, argument, .appArgument summary exported, by simp⟩
  | bind initializer body => cases focus with
      | bind => exact ⟨_, _, _, _, initializer, .bind body, rfl⟩
  | branch condition yes no => cases focus with
      | branch => exact ⟨_, _, _, _, condition, .branch yes no, List.append_assoc ..⟩
  | perform known operand exported => cases focus with
      | perform => exact ⟨_, _, _, _, operand, .perform known exported, rfl⟩
  | resume allowed operand => cases focus with
      | resume => exact ⟨_, _, _, _, operand, .resume allowed, rfl⟩
  | discard => cases focus
  | cleanup callback body exported => cases focus with
      | cleanup => exact ⟨_, _, _, _, callback, .cleanup body exported, List.append_assoc ..⟩
  | resource initializer body outward exported => cases focus with
      | resource notValue => exact ⟨_, _, _, _, initializer, .resource body outward exported, rfl⟩

theorem context_consumed_to_outer
    (source : ContextDerives operations policy contract outer inside environment position before input after output row)
    (spent : before.localPhase = .consumed) :
    after.localPhase = .consumed ∧ before.outsidePhase = after.outsidePhase ∧
      ClauseProtectionFrames.ContextDerives operations policy outer inside environment position
        before.outsidePhase input before.outsidePhase output row := by
  cases source with
  | pairLeft right =>
      obtain ⟨afterSpent, same, source⟩ := CapturedPhaseContracts.consumed_to_outer right spent
      exact ⟨afterSpent, same, .pairLeft source⟩
  | pairRight left => exact ⟨spent, rfl, .pairRight left⟩
  | appFunction argument exported =>
      obtain ⟨afterSpent, same, source⟩ := CapturedPhaseContracts.consumed_to_outer argument spent
      have invoked := (CapturedPhaseContracts.consumed_export afterSpent).symm.trans exported
      rw [← same] at invoked
      exact ⟨afterSpent, same, .appFunction source invoked⟩
  | appArgument function exported => exact ⟨spent, rfl, .appArgument function ((CapturedPhaseContracts.consumed_export spent).symm.trans exported)⟩
  | bind body =>
      obtain ⟨afterSpent, same, source⟩ := CapturedPhaseContracts.consumed_to_outer body spent
      exact ⟨afterSpent, same, .bind source⟩
  | branch yes no =>
      obtain ⟨afterSpent, same, yesSource⟩ := CapturedPhaseContracts.consumed_to_outer yes spent
      obtain ⟨_, _, noSource⟩ := CapturedPhaseContracts.consumed_to_outer no spent
      exact ⟨afterSpent, same, .branch yesSource noSource⟩
  | perform known exported => exact ⟨spent, rfl, .perform known ((CapturedPhaseContracts.consumed_export spent).symm.trans exported)⟩
  | resume => cases spent
  | cleanup body exported =>
      obtain ⟨afterSpent, same, source⟩ := CapturedPhaseContracts.consumed_to_outer body spent
      have invoked := (CapturedPhaseContracts.consumed_running_export afterSpent).symm.trans exported
      rw [← same] at invoked
      exact ⟨afterSpent, same, .cleanup source invoked⟩
  | resource body outward exported =>
      exact ⟨spent, rfl, .resource body outward ((CapturedPhaseContracts.consumed_export spent).symm.trans exported)⟩

inductive Chain (operations : Operations) (policy : Syntax.TicketPolicy)
    (contract : CapturedPhaseContracts.Contract) (outer : Ticket) (inside : ProtectionContracts.Context)
    (environment : CallableProtection.Environment) :
    List PlainData → CapturedPhaseContracts.State → CallableProtection.Contract → CapturedPhaseContracts.State → CallableProtection.Contract → Footprint → Prop where
  | nil : Chain operations policy contract outer inside environment [] state result state result []
  | cons (head : ContextDerives operations policy contract outer inside environment frame.context before input middle intermediate headRow)
      (tail : Chain operations policy contract outer inside environment rest middle intermediate after output tailRow) :
      Chain operations policy contract outer inside environment (frame :: rest) before input after output (headRow ++ tailRow)

theorem chain_consumed_segment
    (source : Chain operations policy contract outer (contextOf tables fixed) environment frames before input after output row)
    (spent : before.localPhase = .consumed) :
    after.localPhase = .consumed ∧ before.outsidePhase = after.outsidePhase ∧
      OpenPhaseSegments.Segment operations policy outer owner tables fixed (stackOf frames .nil)
        before.outsidePhase input before.outsidePhase output row := by
  induction source with
  | nil => exact ⟨spent, rfl, .nil⟩
  | cons head tail ih =>
      obtain ⟨middleSpent, first, source⟩ := context_consumed_to_outer head spent
      obtain ⟨afterSpent, second, remaining⟩ := ih middleSpent
      rw [← first] at remaining
      refine ⟨afterSpent, first.trans second, .push (.plain (outer_context_congr source ?_) ?_) remaining⟩
      · intro demands
        simpa only [PhaseContextChains.stack_tail_append, Stack.append] using
          (PhaseContextChains.plain_prefix_residual tables _ fixed demands).symm
      · intro available consumed
        rw [available] at consumed
        cases consumed

theorem chain_append
    (first : Chain operations policy contract outer inside environment frames before input middle intermediate firstRow)
    (second : Chain operations policy contract outer inside environment rest middle intermediate after output secondRow) :
    Chain operations policy contract outer inside environment (frames ++ rest) before input after output (firstRow ++ secondRow) := by
  induction first with
  | nil => exact second
  | cons head remaining ih => simpa only [List.cons_append, List.append_assoc] using Chain.cons head (ih second)

theorem chain_decompose
    (chain : Chain operations policy contract outer inside environment (frames ++ rest) before input after output row) :
    ∃ middle intermediate firstRow secondRow,
      Chain operations policy contract outer inside environment frames before input middle intermediate firstRow ∧
      Chain operations policy contract outer inside environment rest middle intermediate after output secondRow ∧
      row = firstRow ++ secondRow := by
  induction frames generalizing before input row with
  | nil => exact ⟨before, input, [], row, .nil, chain, rfl⟩
  | cons frame remaining ih => cases chain with
      | cons head tail =>
          obtain ⟨middle, intermediate, firstRow, secondRow, first, second, same⟩ := ih tail
          exact ⟨middle, intermediate, _, secondRow, .cons head first, second, by simp [same, List.append_assoc]⟩

theorem chain_plug
    (chain : Chain operations policy contract outer inside environment frames middle input after output remainder)
    (child : Derives operations policy contract outer inside environment before code middle input row) :
    Derives operations policy contract outer inside environment before (PhaseContextChains.plug frames code) after output (row ++ remainder) := by
  induction chain generalizing before code row with
  | nil => simpa only [PhaseContextChains.plug, List.append_nil] using child
  | cons head rest ih =>
      simpa only [PhaseContextChains.plug, List.append_assoc] using ih (context_plug head child)

/-- Current code promises a particular return phase and full contract. The
    first pending context must accept both, and each following context must
    accept its predecessor's output. Earlier effects are not replayed. -/
inductive Source (operations : Operations) (policy : Syntax.TicketPolicy) (contract : CapturedPhaseContracts.Contract) (outer : Ticket)
    (inside outside : ProtectionContracts.Context) (environment : CallableProtection.Environment) :
    Code → List PlainData → CapturedPhaseContracts.State → CapturedPhaseContracts.State → Contract → Footprint → Prop where
  | checked (current : Derives operations policy contract outer inside environment before code middle input currentRow)
      (pending : Chain operations policy contract outer inside environment frames middle input after output remaining)
      (accepted : checkFootprint outside (currentRow ++ remaining) = true) :
      Source operations policy contract outer inside outside environment code frames before after output (currentRow ++ remaining)

theorem source_reconstruct
    (source : Source operations policy contract outer inside outside environment code frames before after output row) :
    Derives operations policy contract outer inside environment before (PhaseContextChains.plug frames code) after output row ∧
      checkFootprint outside row = true := by
  cases source with
  | checked current pending accepted => exact ⟨chain_plug pending current, accepted⟩

theorem source_focus
    (source : Source operations policy contract outer inside outside environment whole frames before after output row)
    (focus : Focus whole child plain.context) :
    Source operations policy contract outer inside outside environment child (plain :: frames) before after output row := by
  cases source with
  | checked current pending accepted =>
      obtain ⟨middle, input, childRow, frameRow, childSource, context, same⟩ :=
        focus_decompose current focus
      rw [same, List.append_assoc] at accepted ⊢
      exact .checked childSource (.cons context pending) accepted

theorem source_return
    (source : Source operations policy contract outer inside outside environment value frames before after output row)
    (isValue : value.IsValue) :
    ∃ input, Summarizes operations environment value input [] ∧
      Chain operations policy contract outer inside environment frames before input after output row ∧
      checkFootprint outside row = true := by
  cases source with
  | checked current pending accepted =>
      obtain ⟨summary, same, empty⟩ := CapturedPhaseContracts.value_summary current isValue
      cases same
      subst_vars
      exact ⟨_, summary, pending, accepted⟩

theorem source_plug
    (source : Source operations policy contract outer inside outside environment value (plain :: frames) before after output row)
    (closed : ClosedValue value) :
    Source operations policy contract outer inside outside environment (plain.context.plug value) frames before after output row := by
  obtain ⟨input, summary, pending, accepted⟩ := source_return source closed.1
  cases pending with
  | cons head rest =>
      have current : Derives operations policy contract outer inside environment before value before input [] :=
        .stable summary (by simp [CapturedPhaseContracts.exportAt, residual_empty])
      exact .checked (context_plug head current) rest accepted


/-- At a value-operand resume, the saved segment starts at the contract's
    input phase; waiting code starts only at its promised output phase. -/
theorem source_resume_parts
    (source : Source operations policy contract outer inside outside environment
      (.resume contract.header.binder value) frames before after output row)
    (isValue : value.IsValue) :
    ∃ remaining,
      before = ⟨.available, contract.sourcePhase⟩ ∧
      Summarizes operations environment value contract.header.input [] ∧
      Chain operations policy contract outer inside environment frames
        ⟨.consumed, contract.resultPhase⟩ contract.header.answer after output remaining ∧
      row = contract.resumeRow ++ remaining ∧
      checkFootprint outside (contract.resumeRow ++ remaining) = true := by
  cases source with
  | checked current pending accepted => cases current with
      | stable summary exported => cases summary
      | resume allowed operand =>
          obtain ⟨summary, same, empty⟩ := CapturedPhaseContracts.value_summary operand isValue
          subst_vars
          exact ⟨_, rfl, summary, pending, rfl, accepted⟩

/-- Only contiguous plain frames and the spent local marker are inserted here.
    No handler, resource or protected frame is commuted across the capture. -/
theorem saved_at_waiting
    (interface : Interface operations policy tickets outer owner tables fixed capture outside contract) :
    OpenPhaseSegments.Segment operations policy outer owner tables
      ((stackOf frames .nil).append (.spent localOwner answer caller fixed)) capture
      contract.sourcePhase contract.header.input contract.resultPhase contract.header.answer interface.actualRow := by
  apply segment_residual_congr interface.source
  intro demands
  simpa only [PhaseContextChains.stack_tail_append, Stack.append, contextOf] using
    (PhaseContextChains.plain_prefix_residual tables frames (.spent localOwner answer caller fixed) demands).symm

/-- Source resumption produces a certificate for the actual restored prefix.
    The saved segment and waiting clause agree on both phase and full contract;
    the retained actual row may be smaller than the advertised resume bound. -/
theorem restored_source
    (interface : Interface operations policy tickets outer owner tables fixed capture external contract)
    (source : Source operations policy contract outer (contextOf tables fixed) outside environment
      (.resume contract.header.binder value) frames before after output row)
    (isValue : value.IsValue) :
    ∃ remaining,
      before = ⟨.available, contract.sourcePhase⟩ ∧ after.localPhase = .consumed ∧
      row = contract.resumeRow ++ remaining ∧
      OpenPhaseSegments.Source operations policy outer owner tables fixed outside scope value
        (capture.append ((stackOf frames .nil).append (.spent localOwner answer caller .nil)))
        contract.sourcePhase after.outsidePhase output (interface.actualRow ++ remaining) := by
  obtain ⟨remaining, starts, operand, pending, same, accepted⟩ := source_resume_parts source isValue
  obtain ⟨spent, phase, waitingSource⟩ := chain_consumed_segment (owner := owner) pending rfl
  have waitingAtSpent := segment_residual_congr waitingSource
    (replacement := .spent localOwner answer caller fixed) (fun _ => rfl)
  have savedSource := saved_at_waiting (frames := frames) (localOwner := localOwner)
    (answer := answer) (caller := caller) interface
  have restored := OpenPhaseSegments.restore_recompose savedSource waitingAtSpent
  change contract.resultPhase = after.outsidePhase at phase
  rw [phase] at restored
  have acceptedActual : checkFootprint outside (interface.actualRow ++ remaining) = true := by
    rw [check_footprint_append, Bool.and_eq_true_iff] at accepted ⊢
    exact ⟨EffectBounds.check_covered accepted.1 interface.covered, accepted.2⟩
  refine ⟨remaining, starts, spent, same, ?_⟩
  simpa only [List.nil_append] using OpenPhaseSegments.Source.checked
    (scope := scope)
    (ClauseProtection.Derives.stable (outside := []) operand (by simp [ClauseProtection.exportAt, residual_empty]))
    (by intro available consumed; rw [available] at consumed; cases consumed) restored acceptedActual

theorem plain_prefix_check (tables : Tables) (frames : List PlainData) (tail : Stack) (row : Footprint) :
    checkFootprint (contextOf tables (stackOf frames tail)) row = checkFootprint (contextOf tables tail) row := by
  have same := congrArg (checkResidual []) (PhaseContextChains.plain_prefix_residual tables frames tail row)
  simpa only [residual_check, List.append_nil] using same

theorem context_realizes {fixed : Stack}
    (innerBoundary : PhaseBoundaries.Boundary (contract.header.ticket contract.resumeRow contract.closeRow)
      localOwner state.localPhase localBase (fixed.append outerBase) localAnswer)
    (outerBoundary : PhaseBoundaries.Boundary outer outerOwner state.outsidePhase outerBase tail outerAnswer) :
    checkFootprint (CapturedPhaseContracts.context contract outer (contextOf tables fixed) state ++ contextOf tables tail) row =
      checkFootprint (contextOf tables (stackOf frames localBase)) row :=
  (CapturedPhaseContracts.context_realizes innerBoundary outerBoundary).trans (plain_prefix_check tables frames localBase row).symm

section Execution
variable {capture fixed base outside : Stack}

theorem focus_joint
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨whole, scope, stackOf frames base⟩, issued, completed⟩, activations⟩ result outgoing bound)
    (source : Source operations policy contract outer inside outsideContext environment whole frames beforePhase finalPhase output row)
    (focus : Focus whole child position) :
    ∃ plain : PlainData, plain.context = position ∧ plain.scope = scope ∧
      let initial : NamedState := ⟨⟨⟨whole, scope, stackOf frames base⟩, issued, completed⟩, activations⟩
      let next := ScopedPortJoint.advanceState initial ⟨child, scope, stackOf (plain :: frames) base⟩ [] []
      NamedAccessStep ambient initial next ∧
      CompletionJoint.Valid declarations policy registry ambient next result outgoing bound ∧
      Source operations policy contract outer inside outsideContext environment child (plain :: frames) beforePhase finalPhase output row := by
  obtain ⟨plain, shape, saved, step, nextValid⟩ := CompletionJoint.focus_preserves valid focus
  exact ⟨plain, shape, saved, step, nextValid, source_focus source (shape ▸ focus)⟩

theorem plug_joint
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨value, scope, stackOf (plain :: frames) base⟩, issued, completed⟩, activations⟩ result outgoing bound)
    (source : Source operations policy contract outer inside outsideContext environment value (plain :: frames)
      beforePhase finalPhase output row)
    (isValue : value.IsValue) :
    let initial : NamedState := ⟨⟨⟨value, scope, stackOf (plain :: frames) base⟩, issued, completed⟩, activations⟩
    let next := ScopedPortJoint.advanceState initial ⟨plain.context.plug value, plain.scope, stackOf frames base⟩ [] []
    NamedAccessStep ambient initial next ∧
      CompletionJoint.Valid declarations policy registry ambient next result outgoing bound ∧
      Source operations policy contract outer inside outsideContext environment (plain.context.plug value) frames
        beforePhase finalPhase output row := by
  obtain ⟨step, nextValid⟩ := CompletionJoint.plug_preserves valid isValue
  exact ⟨step, nextValid, source_plug source (CompletionJoint.current_closed_value valid isValue)⟩

/-- The source certificate describes the same next configuration as the named
    resume rule and the full ownership, closure and runtime type invariant. -/
theorem resume_joint
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.resume contract.header.binder value, scope,
        (stackOf frames .nil).append (.live localOwner operationResult answer capture caller (fixed.append base))⟩,
        issued, completed⟩, activations⟩ result outgoing bound)
    (resolved : scope.resolve contract.header.binder = some localOwner) (isValue : value.IsValue)
    (boundary : PhaseBoundaries.Boundary outer owner contract.sourcePhase base outside ownerAnswer)
    (interface : Interface operations policy registry.joint.usage outer owner tables fixed capture
      (activeTickets (fixed.append base)) contract)
    (source : Source operations policy contract outer (contextOf tables fixed) (contextOf tables outside) environment
      (.resume contract.header.binder value) frames beforePhase finalPhase output row) :
    let before : NamedState := ⟨⟨⟨.resume contract.header.binder value, scope,
      (stackOf frames .nil).append (.live localOwner operationResult answer capture caller (fixed.append base))⟩,
      issued, completed⟩, activations⟩
    let after : Configuration := ⟨value, scope,
      capture.append ((stackOf frames .nil).append (.spent localOwner answer caller (fixed.append base)))⟩
    NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [] [.ticket localOwner]) ∧
    CompletionJoint.Valid declarations policy registry ambient
      (ScopedPortJoint.advanceState before after [] [.ticket localOwner]) result outgoing bound ∧
    ∃ remaining,
      beforePhase = ⟨.available, contract.sourcePhase⟩ ∧ finalPhase.localPhase = .consumed ∧
      row = contract.resumeRow ++ remaining ∧
      OpenPhaseSegments.Source operations policy outer owner tables fixed (contextOf tables outside) scope value
        (capture.append ((stackOf frames .nil).append (.spent localOwner answer caller .nil)))
        contract.sourcePhase finalPhase.outsidePhase output (interface.actualRow ++ remaining) ∧
      ∀ demands, checkFootprint
        (phaseContext outer
          (contextOf tables ((capture.append ((stackOf frames .nil).append (.spent localOwner answer caller .nil))).append fixed))
          contract.sourcePhase ++ contextOf tables outside) demands =
        checkFootprint (contextOf tables after.stack) demands := by
  obtain ⟨step, preserved⟩ := CompletionJoint.resume_preserves valid resolved isValue
  obtain ⟨remaining, starts, spent, same, restored⟩ := restored_source
    (scope := scope) (localOwner := localOwner) (answer := answer) (caller := caller) interface source isValue
  refine ⟨step, preserved, remaining, starts, spent, same, restored, ?_⟩
  intro demands
  simpa only [stack_append_assoc, Stack.append] using
    PhaseBoundaries.boundary_check (tables := tables)
      (front := (capture.append ((stackOf frames .nil).append (.spent localOwner answer caller .nil))).append fixed)
      (row := demands) boundary

end Execution

namespace Examples
open OpenOwnerUses.Examples (operations policy tickets capture localHandler waiting)
open CapturedPhaseContracts.Examples (openContract initial completed request laterBody laterRow entryTail)
open OpenPhaseSegments.Examples (protectedTicket)

/-- The local handler resumes; the outside effect handler may dispose. -/
def tables : Tables := fun handler =>
  if handler.effectInst = .user 71 [] then OwnerPhases.Examples.tables handler else OpenOwnerUses.Examples.tables handler

theorem captured_source : OpenPhaseSegments.Segment operations policy protectedTicket 9 tables .nil capture
    .available .scalar .consumed .scalar [] := by
  have head : ClauseProtectionFrames.ContextDerives operations policy protectedTicket
      (contextOf tables (.push (.handler localHandler) .nil)) CallableProtection.Environment.empty
      waiting.context .available .scalar .consumed .scalar [] :=
    CapturedPhaseContracts.Examples.protected_waiting_source
  exact .push (.plain head (by intro _ _; rfl)) (.push .handler .nil)

def interface : Interface operations policy tickets protectedTicket 9 tables .nil capture [9] openContract :=
  ⟨[], captured_source, EffectBounds.covers_refl [], OpenOwnerUses.Examples.interface, by decide, rfl,
    .outsideObligation (by decide)⟩

def later : PlainData := ⟨.bind 6 request, .ticket 20 19, .integer, .unit, [], rfl⟩

theorem later_source : Source operations policy openContract protectedTicket [] (contextOf tables OwnerPhases.Examples.tail)
    CallableProtection.Environment.empty laterBody [] initial completed .scalar laterRow :=
  .checked (CapturedPhaseContracts.Examples.later_source _) .nil (by decide)

theorem focused_source : Source operations policy openContract protectedTicket [] (contextOf tables OwnerPhases.Examples.tail)
    CallableProtection.Environment.empty (.resume 20 .unit) [later] initial completed .scalar laterRow :=
  source_focus later_source (.bind (by intro impossible; cases impossible))

def beforeResume : Configuration :=
  ⟨.resume 20 .unit, .ticket 20 19, .push (.plain later) (.live 19 .unit .integer capture (.ticket 10 9) entryTail)⟩
def afterResume : Configuration :=
  ⟨.unit, .ticket 20 19, capture.append (.push (.plain later) (.spent 19 .integer (.ticket 10 9) entryTail))⟩
def restored : Stack := capture.append (.push (.plain later) (.spent 19 .integer (.ticket 10 9) .nil))

theorem actual_resume : RawStep beforeResume afterResume [] [.ticket 19] :=
  .resume 20 19 (.ticket 20 19) (.ticket 10 9) .unit .integer (.push (.plain later) .nil) capture entryTail .unit
    CallableProtection.Examples.unit_closed rfl

theorem actual_restored_shape : afterResume.stack = restored.append entryTail := by
  simp only [afterResume, restored, stack_append_assoc, Stack.append]

theorem restored_source : OpenPhaseSegments.Source operations policy protectedTicket 9 tables .nil
    (contextOf tables OwnerPhases.Examples.tail) (.ticket 20 19) .unit restored .available .consumed .scalar laterRow := by
  obtain ⟨remaining, _, _, same, source⟩ := PhaseResumption.restored_source
    (scope := Execution.Scope.ticket 20 19) (localOwner := 19) (answer := Ty.integer) (caller := Execution.Scope.ticket 10 9)
    interface focused_source trivial
  have equal : laterRow = remaining := same
  subst remaining
  exact source

theorem restored_interpretation (demands : Footprint) :
    checkFootprint (phaseContext protectedTicket (contextOf tables restored) .available ++
      contextOf tables OwnerPhases.Examples.tail) demands = checkFootprint (contextOf tables afterResume.stack) demands := by
  rw [actual_restored_shape]
  exact PhaseBoundaries.boundary_check (PhaseBoundaries.Boundary.live rfl)

theorem before_resume_usage : ConfigurationUsage policy tickets beforeResume := by
  have outsideHandler : StackUsage policy tickets OwnerPhases.Examples.tail [] [] :=
    .push (.handler ⟨_, .none⟩ (.cons (.discard rfl) .nil)) (by simp [frameActiveDemand]) .nil
  have outsideSaved : StackUsage policy tickets OwnerPhases.Examples.capture [] [] :=
    .push (.running ⟨_, .none⟩ (.lambda .unit) .integer) (by simp [frameActiveDemand]) .nil
  have outsideUsage : StackUsage policy tickets entryTail [] [] := by
    change StackUsage policy tickets (.live 9 .unit .integer OwnerPhases.Examples.capture .none OwnerPhases.Examples.tail) [] []
    exact .live rfl ⟨_, .none⟩ outsideSaved outsideHandler
  have captured : StackUsage policy tickets capture (activeTickets entryTail ++ []) [9] :=
    OpenOwnerUses.Examples.captured_usage
  have localUsage : StackUsage policy tickets (.live 19 .unit .integer capture (.ticket 10 9) entryTail) [] [9] :=
    .live rfl ⟨_, .bound rfl⟩ captured outsideUsage
  have control : StackUsage policy tickets beforeResume.stack [] [9] :=
    .push (.plain (.idle (.bound rfl) (.bind .unit (.perform .unit)))) (by simp [frameActiveDemand]) localUsage
  exact ⟨[19], [9], .consume rfl (.resume rfl .unit), control, by decide, List.Perm.refl _, by decide⟩

theorem resume_preserves_usage : ConfigurationUsage policy tickets afterResume :=
  resume_preserves_configuration_usage (front := .push (.plain later) .nil) before_resume_usage rfl trivial

theorem later_demand_accepted : checkFootprint (contextOf tables OwnerPhases.Examples.tail) laterRow = true := by decide

theorem entry_demand_rejected : checkFootprint (contextOf tables entryTail) laterRow = false := by decide

end Examples

end Ash.OneShot.PhaseResumption

#print axioms Ash.OneShot.PhaseResumption.phase_residual_congr
#print axioms Ash.OneShot.PhaseResumption.running_phase_congr
#print axioms Ash.OneShot.PhaseResumption.outer_context_congr
#print axioms Ash.OneShot.PhaseResumption.frame_residual_congr
#print axioms Ash.OneShot.PhaseResumption.segment_residual_congr
#print axioms Ash.OneShot.PhaseResumption.context_plug
#print axioms Ash.OneShot.PhaseResumption.split_export
#print axioms Ash.OneShot.PhaseResumption.stable_context
#print axioms Ash.OneShot.PhaseResumption.focus_decompose
#print axioms Ash.OneShot.PhaseResumption.context_consumed_to_outer
#print axioms Ash.OneShot.PhaseResumption.chain_consumed_segment
#print axioms Ash.OneShot.PhaseResumption.chain_append
#print axioms Ash.OneShot.PhaseResumption.chain_decompose
#print axioms Ash.OneShot.PhaseResumption.chain_plug
#print axioms Ash.OneShot.PhaseResumption.source_reconstruct
#print axioms Ash.OneShot.PhaseResumption.source_focus
#print axioms Ash.OneShot.PhaseResumption.source_return
#print axioms Ash.OneShot.PhaseResumption.source_plug
#print axioms Ash.OneShot.PhaseResumption.source_resume_parts
#print axioms Ash.OneShot.PhaseResumption.saved_at_waiting
#print axioms Ash.OneShot.PhaseResumption.restored_source
#print axioms Ash.OneShot.PhaseResumption.plain_prefix_check
#print axioms Ash.OneShot.PhaseResumption.context_realizes
#print axioms Ash.OneShot.PhaseResumption.focus_joint
#print axioms Ash.OneShot.PhaseResumption.plug_joint
#print axioms Ash.OneShot.PhaseResumption.resume_joint
#print axioms Ash.OneShot.PhaseResumption.Examples.captured_source
#print axioms Ash.OneShot.PhaseResumption.Examples.later_source
#print axioms Ash.OneShot.PhaseResumption.Examples.focused_source
#print axioms Ash.OneShot.PhaseResumption.Examples.actual_resume
#print axioms Ash.OneShot.PhaseResumption.Examples.actual_restored_shape
#print axioms Ash.OneShot.PhaseResumption.Examples.restored_source
#print axioms Ash.OneShot.PhaseResumption.Examples.restored_interpretation
#print axioms Ash.OneShot.PhaseResumption.Examples.before_resume_usage
#print axioms Ash.OneShot.PhaseResumption.Examples.resume_preserves_usage
#print axioms Ash.OneShot.PhaseResumption.Examples.later_demand_accepted
#print axioms Ash.OneShot.PhaseResumption.Examples.entry_demand_rejected
