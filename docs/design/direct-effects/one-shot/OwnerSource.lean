import OwnerPhaseTransitions

/-!
Direct source judgments indexed by a shared owner-phase map. Resume contracts
are annotations whose saved-source and close-plan authentication must accompany
runtime integration. Resource bodies have stable summaries. Handler installation,
resource bodies with owner actions, and a complete phase-aware registry invariant
remain open; this is not complete admission.
-/

namespace Ash.OneShot.OwnerSource
open ScopedExpressions ScopedExecution CallableProtection ProtectionContracts ProtectionResiduals
open OwnerPhaseTransitions (Phases Trace spend project)
open CallableProtectionFrames (Tables)

/-- Rows are exported requirements at the common outside analysis boundary.
    The demand lists include obligations executed by the saved continuation or
    closing plan, not only the clause's explicit ticket syntax. -/
structure ResumeContract where
  input : CallableProtection.Contract
  answer : CallableProtection.Contract
  held : Bool
  resumeDemand : List Nat
  resumeRow : Footprint
  closeDemand : List Nat
  closeRow : Option Footprint
  deriving DecidableEq, Repr

abbrev Contracts := Nat → Option ResumeContract

def exportAt (inside : OwnerPhases.Context) (phases : Phases) (row : Footprint) : Option Footprint :=
  residualize (project inside phases) row

/-- The single direct sequencing syntax threads the shared map. Captured
    transitions and immediate effect interpretation remain distinct premises. -/
inductive Derives (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (inside : OwnerPhases.Context) :
    CallableProtection.Environment → Scope → Phases → Code → Phases → CallableProtection.Contract → List Nat → Footprint → Prop where
  | stable (summary : Summarizes operations environment code result raw)
      (exported : exportAt inside phases raw = some row) :
      Derives operations policy contracts inside environment scope phases code phases result [] row
  | pair (left : Derives operations policy contracts inside environment scope before a middle first leftDemand leftRow)
      (right : Derives operations policy contracts inside environment scope middle b after second rightDemand rightRow) :
      Derives operations policy contracts inside environment scope before (.pair a b) after (.pair first second)
        (leftDemand ++ rightDemand) (leftRow ++ rightRow)
  | app (function : Derives operations policy contracts inside environment scope before f middle (.function input output latent) functionDemand functionRow)
      (argument : Derives operations policy contracts inside environment scope middle a after input argumentDemand argumentRow)
      (exported : exportAt inside after latent = some invocationRow) :
      Derives operations policy contracts inside environment scope before (.app f a) after output
        (functionDemand ++ argumentDemand) (functionRow ++ argumentRow ++ invocationRow)
  | bind (initializer : Derives operations policy contracts inside environment scope before a middle input initializerDemand initializerRow)
      (body : Derives operations policy contracts inside (environment.extend parameter input) scope middle b after output bodyDemand bodyRow) :
      Derives operations policy contracts inside environment scope before (.bind parameter a b) after output
        (initializerDemand ++ bodyDemand) (initializerRow ++ bodyRow)
  | branch (condition : Derives operations policy contracts inside environment scope before test middle .scalar conditionDemand conditionRow)
      (yes : Derives operations policy contracts inside environment scope middle a after output yesDemand yesRow)
      (no : Derives operations policy contracts inside environment scope middle b after output noDemand noRow) :
      Derives operations policy contracts inside environment scope before (.branch test a b) after output
        (conditionDemand ++ yesDemand) (conditionRow ++ yesRow ++ noRow)
  | perform (known : operations effect operation = some (input, output))
      (operand : Derives operations policy contracts inside environment scope before value after input operandDemand operandRow)
      (exported : exportAt inside after [⟨effect, operation, false⟩] = some requestRow) :
      Derives operations policy contracts inside environment scope before (.perform (Instantiation.freezeEffect effect) operation value)
        after output operandDemand (operandRow ++ requestRow)
  | resume (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
      (allowed : (policy binder).resume = true)
      (operand : Derives operations policy contracts inside environment scope before value middle contract.input operandDemand operandRow)
      (transition : Trace middle (owner :: contract.resumeDemand) after) :
      Derives operations policy contracts inside environment scope before (.resume binder value) after contract.answer
        (operandDemand ++ owner :: contract.resumeDemand) (operandRow ++ contract.resumeRow)
  | discard (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
      (allowed : (policy binder).dispose = true) (unprotected : contract.held = false)
      (closable : contract.closeRow = some row) (transition : Trace before (owner :: contract.closeDemand) after) :
      Derives operations policy contracts inside environment scope before (.discard binder) after .scalar
        (owner :: contract.closeDemand) row
  | cleanup (callback : Derives operations policy contracts inside environment scope before action middle (.function .scalar .scalar latent) callbackDemand callbackRow)
      (body : Derives operations policy contracts inside environment scope middle code after output bodyDemand bodyRow)
      (exported : residualize (.barrier true :: project inside after) latent = some executionRow) :
      Derives operations policy contracts inside environment scope before (.cleanup action code) after output
        (callbackDemand ++ bodyDemand) (callbackRow ++ bodyRow ++ executionRow)
  | resource {world : List Nat} {bodyRow : Nat → Footprint}
      (initializer : Derives operations policy contracts inside environment scope before initial after .scalar demand initialRow)
      (body : ∀ identity, identity ∉ world → Summarizes operations environment
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output (bodyRow identity))
      (outward : ∀ identity, identity ∉ world → outsideCell identity (bodyRow identity) = raw)
      (exported : exportAt inside after raw = some row) :
      Derives operations policy contracts inside environment scope before (.resource binder initial code) after output demand (initialRow ++ row)

theorem source_trace (source : Derives operations policy contracts inside environment scope before code after result demand row) :
    Trace before demand after := by
  induction source with
  | stable => exact .nil
  | pair left right ihLeft ihRight | app left right exported ihLeft ihRight | bind left right ihLeft ihRight =>
      exact OwnerPhaseTransitions.trace_append ihLeft ihRight
  | branch condition yes no ihCondition ihYes ihNo => exact OwnerPhaseTransitions.trace_append ihCondition ihYes
  | perform known operand exported ih => exact ih
  | resume known resolved allowed operand transition ih => exact OwnerPhaseTransitions.trace_append ih transition
  | discard known resolved allowed unprotected closable transition => exact transition
  | cleanup callback body exported ihCallback ihBody => exact OwnerPhaseTransitions.trace_append ihCallback ihBody
  | resource initializer body outward exported ih => exact ih

theorem source_monotone (source : Derives operations policy contracts inside environment scope before code after result demand row)
    (spent : before owner = .consumed) : after owner = .consumed := OwnerPhaseTransitions.trace_monotone (source_trace source) spent

theorem source_no_repeated_owner (source : Derives operations policy contracts inside environment scope before code after result demand row) :
    demand.Nodup := OwnerPhaseTransitions.trace_nodup (source_trace source)

theorem value_summary
    (source : Derives operations policy contracts inside environment scope before value after result demand row)
    (isValue : value.IsValue) :
    Summarizes operations environment value result [] ∧ before = after ∧ demand = [] ∧ row = [] := by
  induction source with
  | stable summary exported =>
      have noEffects := value_has_no_immediate_demands summary isValue
      rw [noEffects, exportAt, residual_empty] at exported
      cases Option.some.inj exported
      exact ⟨noEffects ▸ summary, rfl, rfl, rfl⟩
  | pair left right ihLeft ihRight =>
      obtain ⟨a, first, leftDemand, leftRow⟩ := ihLeft isValue.1
      obtain ⟨b, second, rightDemand, rightRow⟩ := ihRight isValue.2
      exact ⟨.pair a b, first.trans second, by simp [leftDemand, rightDemand], by simp [leftRow, rightRow]⟩
  | app | bind | branch | perform | resume | discard | cleanup | resource => cases isValue

theorem substitution
    (source : Derives operations policy contracts inside (environment.extend name input) scope before code after result demand row)
    (replacement : Summarizes operations environment value input []) (closed : ClosedValue value) :
    Derives operations policy contracts inside environment scope before (code.subst name value) after result demand row := by
  cases source with
  | stable summary exported => exact .stable (CallableProtection.substitution summary replacement closed) exported
  | pair left right => exact .pair (substitution left replacement closed) (substitution right replacement closed)
  | app function argument exported => exact .app (substitution function replacement closed) (substitution argument replacement closed) exported
  | bind initializer body =>
      rename_i a middle domain initializerDemand initializerRow parameter b bodyDemand bodyRow
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
  | resume known resolved allowed operand transition => exact .resume known resolved allowed (substitution operand replacement closed) transition
  | discard known resolved allowed unprotected closable transition => exact .discard known resolved allowed unprotected closable transition
  | cleanup callback body exported => exact .cleanup (substitution callback replacement closed) (substitution body replacement closed) exported
  | resource initializer body outward exported =>
      apply Derives.resource (substitution initializer replacement closed) _ outward exported
      intro identity fresh
      rw [Code.instantiation_subst _ name value _ closed.2.1]
      exact CallableProtection.substitution (body identity fresh) replacement closed
termination_by code.nodes
decreasing_by all_goals subst_vars; all_goals simp only [Code.nodes]; all_goals omega

theorem bind_summary
    (source : Derives operations policy contracts inside environment scope before (.bind parameter value body) after result demand row)
    (closed : ClosedValue value) :
    Derives operations policy contracts inside environment scope before (body.subst parameter value) after result demand row := by
  cases source with
  | stable summary exported => exact .stable (CallableProtection.bind_summary summary closed) exported
  | bind initializer body =>
      obtain ⟨replacement, same, emptyDemand, emptyRow⟩ := value_summary initializer closed.1
      subst_vars
      simpa only [List.nil_append] using substitution body replacement closed

theorem beta_summary
    (source : Derives operations policy contracts inside environment scope before (.app (.lambda parameter body) value) after result demand row)
    (closed : ClosedValue value) :
    Derives operations policy contracts inside environment .none before (body.subst parameter value) after result demand row := by
  cases source with
  | stable summary exported => exact .stable (CallableProtection.beta_summary summary closed) exported
  | app function argument exported =>
      obtain ⟨functionSummary, functionPhase, functionDemand, functionRow⟩ := value_summary function trivial
      obtain ⟨argumentSummary, argumentPhase, argumentDemand, argumentRow⟩ := value_summary argument closed.1
      subst_vars
      cases functionSummary with
      | lambda body =>
          simpa only [List.nil_append] using Derives.stable (policy := policy) (contracts := contracts) (scope := Execution.Scope.none)
            (CallableProtection.substitution body argumentSummary closed) exported

theorem resume_consumed_rejected
    (source : Derives operations policy contracts inside environment scope before (.resume binder value) after result demand row)
    (resolved : scope.resolve binder = some owner) (spent : before owner = .consumed) : False := by
  cases source with
  | stable summary exported => cases summary
  | resume known actual allowed operand transition =>
      have same := Option.some.inj (actual.symm.trans resolved)
      subst_vars
      have consumed := source_monotone operand spent
      have ready := OwnerPhaseTransitions.trace_available transition _ List.mem_cons_self
      rw [consumed] at ready
      cases ready

theorem source_inside_congr
    (source : Derives operations policy contracts first environment scope before code after result demand row)
    (same : ∀ phases raw, exportAt first phases raw = exportAt second phases raw) :
    Derives operations policy contracts second environment scope before code after result demand row := by
  induction source with
  | stable summary exported => exact .stable summary ((same _ _).symm.trans exported)
  | pair left right ihLeft ihRight => exact .pair ihLeft ihRight
  | app function argument exported ihFunction ihArgument => exact .app ihFunction ihArgument ((same _ _).symm.trans exported)
  | bind initializer body ihInit ihBody => exact .bind ihInit ihBody
  | branch condition yes no ihCondition ihYes ihNo => exact .branch ihCondition ihYes ihNo
  | perform known operand exported ih => exact .perform known ih ((same _ _).symm.trans exported)
  | resume known resolved allowed operand transition ih => exact .resume known resolved allowed ih transition
  | discard known resolved allowed unprotected closable transition => exact .discard known resolved allowed unprotected closable transition
  | cleanup callback body exported ihCallback ihBody =>
      apply Derives.cleanup ihCallback ihBody
      simp only [residualize, DisposalProtection.through_barrier] at exported ⊢
      exact (same _ _).symm.trans exported
  | resource initializer body outward exported ih => exact .resource ih body outward ((same _ _).symm.trans exported)

theorem trace_member_iff_changes (trace : Trace before demand after) : owner ∈ demand ↔ before owner ≠ after owner := by
  constructor
  · intro member same
    have ready := OwnerPhaseTransitions.trace_available trace owner member
    have done := OwnerPhaseTransitions.trace_consumed trace member
    rw [← same, ready] at done
    cases done
  · intro different
    by_cases member : owner ∈ demand
    · exact member
    · exact False.elim (different (OwnerPhaseTransitions.trace_unchanged trace member).symm)

/-- Alternative branches may consume the same owners in different orders.
    Equality of their shared endpoints determines the same consumption set. -/
theorem trace_same_endpoints (first : Trace before left after) (second : Trace before right after) : left.Perm right := by
  apply (List.perm_ext_iff_of_nodup (OwnerPhaseTransitions.trace_nodup first) (OwnerPhaseTransitions.trace_nodup second)).mpr
  intro owner
  exact (trace_member_iff_changes first).trans (trace_member_iff_changes second).symm

theorem branch_demands_agree
    (yes : Derives operations policy contracts inside environment scope before a after result left leftRow)
    (no : Derives operations policy contracts inside environment scope before b after result right rightRow) : left.Perm right :=
  trace_same_endpoints (source_trace yes) (source_trace no)

inductive ContextDerives (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (inside : OwnerPhases.Context) (environment : CallableProtection.Environment) (scope : Scope) :
    ScopedExecution.Context → Phases → CallableProtection.Contract → Phases → CallableProtection.Contract → List Nat → Footprint → Prop where
  | pairLeft (right : Derives operations policy contracts inside environment scope middle code after output demand row) :
      ContextDerives operations policy contracts inside environment scope (.pairLeft code) middle input after (.pair input output) demand row
  | pairRight (left : Summarizes operations environment code input []) :
      ContextDerives operations policy contracts inside environment scope (.pairRight code) phases output phases (.pair input output) [] []
  | appFunction (argument : Derives operations policy contracts inside environment scope middle code after input demand argumentRow)
      (exported : exportAt inside after latent = some invocationRow) :
      ContextDerives operations policy contracts inside environment scope (.appFunction code) middle (.function input output latent)
        after output demand (argumentRow ++ invocationRow)
  | appArgument (function : Summarizes operations environment code (.function input output latent) [])
      (exported : exportAt inside phases latent = some invocationRow) :
      ContextDerives operations policy contracts inside environment scope (.appArgument code) phases input phases output [] invocationRow
  | bind (body : Derives operations policy contracts inside (environment.extend name input) scope middle code after output demand row) :
      ContextDerives operations policy contracts inside environment scope (.bind name code) middle input after output demand row
  | branch (yes : Derives operations policy contracts inside environment scope middle a after output yesDemand yesRow)
      (no : Derives operations policy contracts inside environment scope middle b after output noDemand noRow) :
      ContextDerives operations policy contracts inside environment scope (.branch a b) middle .scalar after output yesDemand (yesRow ++ noRow)
  | perform (known : operations effect operation = some (input, output))
      (exported : exportAt inside phases [⟨effect, operation, false⟩] = some row) :
      ContextDerives operations policy contracts inside environment scope (.perform (Instantiation.freezeEffect effect) operation)
        phases input phases output [] row
  | resume (known : contracts owner = some contract) (resolved : scope.resolve binder = some owner)
      (allowed : (policy binder).resume = true) (transition : Trace before (owner :: contract.resumeDemand) after) :
      ContextDerives operations policy contracts inside environment scope (.resume binder)
        before contract.input after contract.answer (owner :: contract.resumeDemand) contract.resumeRow
  | cleanup (body : Derives operations policy contracts inside environment scope middle code after output demand bodyRow)
      (exported : residualize (.barrier true :: project inside after) latent = some invocationRow) :
      ContextDerives operations policy contracts inside environment scope (.cleanup code) middle (.function .scalar .scalar latent)
        after output demand (bodyRow ++ invocationRow)
  | resource {world : List Nat} {bodyRow : Nat → Footprint}
      (body : ∀ identity, identity ∉ world → Summarizes operations environment
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output (bodyRow identity))
      (outward : ∀ identity, identity ∉ world → outsideCell identity (bodyRow identity) = raw)
      (exported : exportAt inside phases raw = some row) :
      ContextDerives operations policy contracts inside environment scope (.resource binder code) phases .scalar phases output [] row

theorem context_plug
    (context : ContextDerives operations policy contracts inside environment scope position middle input after output remaining restRow)
    (child : Derives operations policy contracts inside environment scope before code middle input demand row) :
    Derives operations policy contracts inside environment scope before (position.plug code) after output
      (demand ++ remaining) (row ++ restRow) := by
  cases context with
  | pairLeft right => exact .pair child right
  | pairRight left =>
      simpa only [ScopedExecution.Context.plug, List.nil_append, List.append_nil] using Derives.pair
        (Derives.stable (row := []) left (by simp [exportAt, residual_empty])) child
  | appFunction argument exported => simpa only [ScopedExecution.Context.plug, List.append_assoc] using Derives.app child argument exported
  | appArgument function exported =>
      simpa only [ScopedExecution.Context.plug, List.nil_append, List.append_nil] using Derives.app
        (Derives.stable (row := []) function (by simp [exportAt, residual_empty])) child exported
  | bind body => exact .bind child body
  | branch yes no => simpa only [ScopedExecution.Context.plug, List.append_assoc] using Derives.branch child yes no
  | perform known exported => simpa only [ScopedExecution.Context.plug, List.append_nil] using Derives.perform known child exported
  | resume known resolved allowed transition => exact .resume known resolved allowed child transition
  | cleanup body exported => simpa only [ScopedExecution.Context.plug, List.append_assoc] using Derives.cleanup child body exported
  | resource body outward exported => simpa only [ScopedExecution.Context.plug, List.append_nil] using Derives.resource child body outward exported

theorem context_trace
    (source : ContextDerives operations policy contracts inside environment scope position before input after output demand row) :
    Trace before demand after := by
  cases source with
  | pairLeft right | appFunction right exported | bind right | branch right no | cleanup right exported => exact source_trace right
  | pairRight | appArgument | perform | resource => exact .nil
  | resume known resolved allowed transition => exact transition

theorem context_inside_congr
    (source : ContextDerives operations policy contracts first environment scope position before input after output demand row)
    (same : ∀ phases raw, exportAt first phases raw = exportAt second phases raw) :
    ContextDerives operations policy contracts second environment scope position before input after output demand row := by
  cases source with
  | pairLeft right => exact .pairLeft (source_inside_congr right same)
  | pairRight left => exact .pairRight left
  | appFunction argument exported => exact .appFunction (source_inside_congr argument same) ((same _ _).symm.trans exported)
  | appArgument function exported => exact .appArgument function ((same _ _).symm.trans exported)
  | bind body => exact .bind (source_inside_congr body same)
  | branch yes no => exact .branch (source_inside_congr yes same) (source_inside_congr no same)
  | perform known exported => exact .perform known ((same _ _).symm.trans exported)
  | resume known resolved allowed transition => exact .resume known resolved allowed transition
  | cleanup body exported =>
      apply ContextDerives.cleanup (source_inside_congr body same)
      simp only [residualize, DisposalProtection.through_barrier] at exported ⊢
      exact (same _ _).symm.trans exported
  | resource body outward exported => exact .resource body outward ((same _ _).symm.trans exported)

inductive FrameSource (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (inside : OwnerPhases.Context) : ExecFrame → Phases → CallableProtection.Contract → Phases → CallableProtection.Contract → List Nat → Footprint → Prop where
  | plain (source : ContextDerives operations policy contracts inside environment plain.scope plain.context before input after output demand row) :
      FrameSource operations policy contracts inside (.plain plain) before input after output demand row
  | handler : FrameSource operations policy contracts inside (.handler handler) phases contract phases contract [] []
  | cell : FrameSource operations policy contracts inside (.cell identity payload scope answer) phases contract phases contract [] []
  | armed (callback : Summarizes operations environment action.action (.function .scalar .scalar latent) [])
      (exported : exportAt inside phases (qualify true latent) = some row) :
      FrameSource operations policy contracts inside (.armed action) phases contract phases contract [] row
  | running (saved : Summarizes operations environment value contract []) :
      FrameSource operations policy contracts inside (.running action value closed) phases .scalar phases contract [] []
  | closing : FrameSource operations policy contracts inside (.closing identity scope) phases .scalar phases .scalar [] []
  | retiring (transition : Trace before [owner] after) :
      FrameSource operations policy contracts inside (.retiring owner) before .scalar after .scalar [owner] []

theorem frame_trace (source : FrameSource operations policy contracts inside frame before input after output demand row) :
    Trace before demand after := by
  cases source with
  | plain source => exact context_trace source
  | handler | cell | armed | running | closing => exact .nil
  | retiring transition => exact transition

theorem frame_inside_congr
    (source : FrameSource operations policy contracts first frame before input after output demand row)
    (same : ∀ phases raw, exportAt first phases raw = exportAt second phases raw) :
    FrameSource operations policy contracts second frame before input after output demand row := by
  cases source with
  | plain source => exact .plain (context_inside_congr source same)
  | handler => exact .handler
  | cell => exact .cell
  | armed callback exported => exact .armed callback ((same _ _).symm.trans exported)
  | running saved => exact .running saved
  | closing => exact .closing
  | retiring transition => exact .retiring transition

/-- A retained live boundary is reached only after preceding code consumes its
    owner. Its saved contract is an annotation; recursive source/plan agreement
    with every registry record remains a separate integration obligation. -/
inductive Segment (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : Tables) (fixed : Stack) : Stack → Phases → CallableProtection.Contract → Phases → CallableProtection.Contract → List Nat → Footprint → Prop where
  | nil : Segment operations policy contracts tables fixed .nil phases contract phases contract [] []
  | push (head : FrameSource operations policy contracts (OwnerPhases.ofStack tables (rest.append fixed))
        frame before input middle intermediate headDemand headRow)
      (tail : Segment operations policy contracts tables fixed rest middle intermediate after output tailDemand tailRow) :
      Segment operations policy contracts tables fixed (.push frame rest) before input after output
        (headDemand ++ tailDemand) (headRow ++ tailRow)
  | live (known : contracts owner = some contract) (held : contract.held = ProtectionContexts.protectedMode capture.erase)
      (consumed : phases owner = .consumed)
      (tail : Segment operations policy contracts tables fixed rest phases contract.answer after output demand row) :
      Segment operations policy contracts tables fixed (.live owner inputType answerType capture caller rest)
        phases contract.answer after output demand row
  | spent (known : contracts owner = some contract) (consumed : phases owner = .consumed)
      (tail : Segment operations policy contracts tables fixed rest phases contract.answer after output demand row) :
      Segment operations policy contracts tables fixed (.spent owner answerType caller rest)
        phases contract.answer after output demand row

theorem segment_trace (source : Segment operations policy contracts tables fixed segment before input after output demand row) :
    Trace before demand after := by
  induction source with
  | nil => exact .nil
  | push head tail ih => exact OwnerPhaseTransitions.trace_append (frame_trace head) ih
  | live known held consumed tail ih | spent known consumed tail ih => exact ih

theorem segment_monotone (source : Segment operations policy contracts tables fixed segment before input after output demand row)
    (spent : before owner = .consumed) : after owner = .consumed := OwnerPhaseTransitions.trace_monotone (segment_trace source) spent

theorem segment_no_repeated_owner (source : Segment operations policy contracts tables fixed segment before input after output demand row) :
    demand.Nodup := OwnerPhaseTransitions.trace_nodup (segment_trace source)

section Composition
variable {front middle fixed : Stack}

theorem segment_append
    (first : Segment operations policy contracts tables (middle.append fixed) front before input phases intermediate firstDemand firstRow)
    (second : Segment operations policy contracts tables fixed middle phases intermediate after output secondDemand secondRow) :
    Segment operations policy contracts tables fixed (front.append middle) before input after output
      (firstDemand ++ secondDemand) (firstRow ++ secondRow) := by
  induction first with
  | nil => exact second
  | push head tail ih =>
      simpa only [Stack.append, List.append_assoc] using Segment.push
        (by simpa only [stack_append_assoc] using head) (ih second)
  | live known held consumed tail ih => exact .live known held consumed (ih second)
  | spent known consumed tail ih => exact .spent known consumed (ih second)

theorem segment_decompose
    (source : Segment operations policy contracts tables fixed (front.append middle) before input after output demand row) :
    ∃ phases intermediate firstDemand secondDemand firstRow secondRow,
      Segment operations policy contracts tables (middle.append fixed) front before input phases intermediate firstDemand firstRow ∧
      Segment operations policy contracts tables fixed middle phases intermediate after output secondDemand secondRow ∧
      demand = firstDemand ++ secondDemand ∧ row = firstRow ++ secondRow := by
  induction front generalizing before input demand row with
  | nil => exact ⟨_, _, [], demand, [], row, .nil, source, rfl, rfl⟩
  | push frame rest ih => cases source with
      | push head tail =>
          obtain ⟨phases, intermediate, firstDemand, secondDemand, firstRow, secondRow, first, second, names, effects⟩ := ih tail
          exact ⟨phases, intermediate, _, secondDemand, _, secondRow,
            .push (by simpa only [stack_append_assoc] using head) first, second,
            by simp only [names, List.append_assoc], by simp only [effects, List.append_assoc]⟩
  | live owner inputType answerType capture caller rest ihCapture ihRest => cases source with
      | live known held consumed tail =>
          obtain ⟨phases, intermediate, firstDemand, secondDemand, firstRow, secondRow, first, second, names, effects⟩ := ihRest tail
          exact ⟨phases, intermediate, firstDemand, secondDemand, firstRow, secondRow,
            .live known held consumed first, second, names, effects⟩
  | spent owner answer caller rest ih => cases source with
      | spent known consumed tail =>
          obtain ⟨phases, intermediate, firstDemand, secondDemand, firstRow, secondRow, first, second, names, effects⟩ := ih tail
          exact ⟨phases, intermediate, firstDemand, secondDemand, firstRow, secondRow,
            .spent known consumed first, second, names, effects⟩

theorem capture_segment (cut : HandlerCut requested whole capture tail handler)
    (source : Segment operations policy contracts tables fixed whole before input after output demand row) :
    ∃ phases intermediate firstDemand secondDemand firstRow secondRow,
      Segment operations policy contracts tables (tail.append fixed) capture before input phases intermediate firstDemand firstRow ∧
      Segment operations policy contracts tables fixed tail phases intermediate after output secondDemand secondRow ∧
      demand = firstDemand ++ secondDemand ∧ row = firstRow ++ secondRow := by
  rw [handler_cut_reconstructs cut] at source
  exact segment_decompose source

end Composition

theorem split_export (exported : exportAt inside phases (first ++ second) = some row) :
    ∃ firstRow secondRow, exportAt inside phases first = some firstRow ∧ exportAt inside phases second = some secondRow ∧
      row = firstRow ++ secondRow := by
  unfold exportAt at *
  rw [residual_rows_append] at exported
  cases firstExport : residualize (project inside phases) first with
  | none => simp [firstExport, merge] at exported
  | some firstRow =>
      cases secondExport : residualize (project inside phases) second with
      | none => simp [firstExport, secondExport, merge] at exported
      | some secondRow =>
          exact ⟨firstRow, secondRow, rfl, rfl, by simpa [firstExport, secondExport, merge] using exported.symm⟩

theorem stable_context
    (context : CallableProtectionFrames.ContextSummarizes operations environment position input output raw)
    (exported : exportAt inside phases raw = some row) :
    ContextDerives operations policy contracts inside environment scope position phases input phases output [] row := by
  cases context with
  | pairLeft right => exact .pairLeft (.stable right exported)
  | pairRight left =>
      have empty : row = [] := by simpa [exportAt, residual_empty] using exported.symm
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
    (source : Derives operations policy contracts inside environment scope before whole after output demand row)
    (focus : Focus whole child position) :
    ∃ middle input childDemand remaining childRow restRow,
      Derives operations policy contracts inside environment scope before child middle input childDemand childRow ∧
      ContextDerives operations policy contracts inside environment scope position middle input after output remaining restRow ∧
      demand = childDemand ++ remaining ∧ row = childRow ++ restRow := by
  cases source with
  | stable summary exported =>
      obtain ⟨input, childRaw, restRaw, childSource, context, same⟩ := CallableProtectionFrames.focus_decompose summary focus
      rw [same] at exported
      obtain ⟨childRow, restRow, childExport, restExport, same⟩ := split_export exported
      exact ⟨_, input, [], [], childRow, restRow, .stable childSource childExport, stable_context context restExport, rfl, same⟩
  | pair left right => cases focus with
      | pairLeft => exact ⟨_, _, _, _, _, _, left, .pairLeft right, rfl, rfl⟩
      | pairRight isValue =>
          obtain ⟨summary, same, emptyDemand, emptyRow⟩ := value_summary left isValue
          subst_vars
          exact ⟨_, _, _, _, _, _, right, .pairRight summary, by simp, by simp⟩
  | app function argument exported => cases focus with
      | appFunction => exact ⟨_, _, _, _, _, _, function, .appFunction argument exported, rfl, List.append_assoc ..⟩
      | appArgument isValue =>
          obtain ⟨summary, same, emptyDemand, emptyRow⟩ := value_summary function isValue
          subst_vars
          exact ⟨_, _, _, _, _, _, argument, .appArgument summary exported, by simp, by simp⟩
  | bind initializer body => cases focus with
      | bind => exact ⟨_, _, _, _, _, _, initializer, .bind body, rfl, rfl⟩
  | branch condition yes no => cases focus with
      | branch => exact ⟨_, _, _, _, _, _, condition, .branch yes no, rfl, List.append_assoc ..⟩
  | perform known operand exported => cases focus with
      | perform => exact ⟨_, _, _, [], _, _, operand, .perform known exported, by simp, rfl⟩
  | resume known resolved allowed operand transition => cases focus with
      | resume => exact ⟨_, _, _, _, _, _, operand, .resume known resolved allowed transition, rfl, rfl⟩
  | discard => cases focus
  | cleanup callback body exported => cases focus with
      | cleanup => exact ⟨_, _, _, _, _, _, callback, .cleanup body exported, rfl, List.append_assoc ..⟩
  | resource initializer body outward exported => cases focus with
      | resource notValue => exact ⟨_, _, _, [], _, _, initializer, .resource body outward exported, by simp, rfl⟩

/-- Current code and every retained frame agree on shared phases and full
    contracts. The rows are exported beyond the same fixed analysis suffix. -/
inductive Source (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : Tables) (fixed : Stack) (outside : ProtectionContracts.Context) :
    Scope → Code → Stack → Phases → Phases → CallableProtection.Contract → List Nat → Footprint → Prop where
  | checked (current : Derives operations policy contracts (OwnerPhases.ofStack tables (segment.append fixed))
        environment scope before code middle input currentDemand currentRow)
      (pending : Segment operations policy contracts tables fixed segment middle input after output remaining restRow)
      (accepted : checkFootprint outside (currentRow ++ restRow) = true) :
      Source operations policy contracts tables fixed outside scope code segment before after output
        (currentDemand ++ remaining) (currentRow ++ restRow)

theorem source_configuration_trace
    (source : Source operations policy contracts tables fixed outside scope code segment before after output demand row) :
    Trace before demand after := by
  cases source with
  | checked current pending accepted => exact OwnerPhaseTransitions.trace_append (source_trace current) (segment_trace pending)

theorem plain_export (inside : OwnerPhases.Context) (phases : Phases) (raw : Footprint) :
    exportAt (.ordinary (.barrier false) :: inside) phases raw = exportAt inside phases raw := by
  simp [exportAt, project, residualize, DisposalProtection.through_barrier, qualify]

theorem source_focus
    (source : Source operations policy contracts tables fixed outside scope whole segment before after output demand row)
    (focus : Focus whole child plain.context) (saved : plain.scope = scope) :
    Source operations policy contracts tables fixed outside scope child (.push (.plain plain) segment) before after output demand row := by
  cases source with
  | checked current pending accepted =>
      obtain ⟨middle, input, childDemand, restDemand, childRow, restRow, childSource, context, names, effects⟩ := focus_decompose current focus
      rw [effects, List.append_assoc] at accepted
      simp only [names, effects, List.append_assoc]
      refine .checked (source_inside_congr childSource ?_) (.push (.plain (saved ▸ context)) pending) accepted
      intro phases raw
      exact (plain_export _ phases raw).symm

theorem source_plug
    (source : Source operations policy contracts tables fixed outside scope value (.push (.plain plain) segment)
      before after output demand row) (closed : ClosedValue value) :
    Source operations policy contracts tables fixed outside plain.scope (plain.context.plug value) segment before after output demand row := by
  cases source with
  | checked current pending accepted =>
      obtain ⟨summary, same, emptyDemand, emptyRow⟩ := value_summary current closed.1
      subst_vars
      cases pending with
      | push head rest => cases head with
          | @plain environment _ _ _ _ _ _ _ context =>
              have returned (phases : Phases) : Derives operations policy contracts (OwnerPhases.ofStack tables (segment.append fixed))
                  environment plain.scope phases value phases _ [] [] :=
                .stable (closed_value_environment summary closed environment) (by simp [exportAt, residual_empty])
              have plugged := context_plug context (returned _)
              simpa only [List.nil_append] using Source.checked plugged rest accepted

/-- With the actual current ownership map, a value cannot be stuck at a live
    boundary: source admission required that owner to have been consumed. -/
theorem value_cannot_reach_live
    (source : Source operations policy contracts tables fixed outside scope value
      (.live owner inputType answerType capture caller rest)
      (OwnerPhaseTransitions.available (ownedTickets ((Stack.live owner inputType answerType capture caller rest).append fixed)))
      after output demand row) (isValue : value.IsValue) : False := by
  cases source with
  | checked current pending accepted =>
      obtain ⟨_, same, _, _⟩ := value_summary current isValue
      cases same
      cases pending with
      | live known held consumed tail => simp [OwnerPhaseTransitions.available, ownedTickets, Stack.append] at consumed

theorem source_bind
    (source : Source operations policy contracts tables fixed outside scope (.bind parameter value body) segment
      before after output demand row) (closed : ClosedValue value) :
    Source operations policy contracts tables fixed outside scope (body.subst parameter value) segment before after output demand row := by
  cases source with
  | checked current pending accepted => exact .checked (bind_summary current closed) pending accepted

theorem source_beta
    (source : Source operations policy contracts tables fixed outside scope (.app (.lambda parameter body) value) segment
      before after output demand row) (closed : ClosedValue value) :
    Source operations policy contracts tables fixed outside .none (body.subst parameter value) segment before after output demand row := by
  cases source with
  | checked current pending accepted => exact .checked (beta_summary current closed) pending accepted

theorem selected_branch
    (source : Derives operations policy contracts inside environment scope before (.branch (.boolean choice) yes no) after result demand row)
    (accepted : checkFootprint outside row = true) :
    ∃ selectedDemand selectedRow,
      Derives operations policy contracts inside environment scope before (if choice then yes else no) after result selectedDemand selectedRow ∧
      checkFootprint outside selectedRow = true ∧ demand.Perm selectedDemand := by
  have choiceSource : ∃ selectedDemand selectedRow,
      Derives operations policy contracts inside environment scope before (if choice then yes else no) after result selectedDemand selectedRow ∧
      checkFootprint outside selectedRow = true := by
    cases source with
    | stable summary exported => cases summary with
        | branch condition yesSource noSource =>
            cases condition
            simp only [List.nil_append] at exported
            obtain ⟨yesRow, noRow, yesExport, noExport, same⟩ := split_export exported
            rw [same, check_footprint_append, Bool.and_eq_true_iff] at accepted
            cases choice with
            | false => exact ⟨[], noRow, .stable noSource noExport, accepted.2⟩
            | true => exact ⟨[], yesRow, .stable yesSource yesExport, accepted.1⟩
    | branch condition yesSource noSource =>
        obtain ⟨_, same, noDemand, noRow⟩ := value_summary condition trivial
        subst_vars
        simp only [List.nil_append, check_footprint_append, Bool.and_eq_true_iff] at accepted
        cases choice with
        | false => exact ⟨_, _, noSource, accepted.2⟩
        | true => exact ⟨_, _, yesSource, accepted.1⟩
  obtain ⟨selectedDemand, selectedRow, selected, admitted⟩ := choiceSource
  exact ⟨selectedDemand, selectedRow, selected, admitted, trace_same_endpoints (source_trace source) (source_trace selected)⟩

theorem source_branch
    (source : Source operations policy contracts tables fixed outside scope (.branch (.boolean choice) yes no) segment
      before after output demand row) :
    ∃ selectedDemand selectedRow,
      Source operations policy contracts tables fixed outside scope (if choice then yes else no) segment before after output selectedDemand selectedRow ∧
      demand.Perm selectedDemand := by
  cases source with
  | checked current pending accepted =>
      rw [check_footprint_append, Bool.and_eq_true_iff] at accepted
      obtain ⟨selectedDemand, selectedRow, selected, admitted, same⟩ := selected_branch current accepted.1
      exact ⟨_, _, .checked selected pending (by simp only [check_footprint_append, admitted, accepted.2, Bool.and_self]), same.append_right _⟩

theorem request_summary
    (source : Derives operations policy contracts inside environment scope before (.perform effect operation operand) after result demand row)
    (isValue : operand.IsValue) :
    ∃ raw, Summarizes operations environment (.perform effect operation operand) result raw ∧
      before = after ∧ demand = [] ∧ exportAt inside before raw = some row := by
  cases source with
  | stable summary exported => exact ⟨_, summary, rfl, rfl, exported⟩
  | perform known operand exported =>
      obtain ⟨summary, same, emptyDemand, emptyRow⟩ := value_summary operand isValue
      subst_vars
      exact ⟨_, .perform known summary, rfl, rfl, exported⟩

/-- Immediate request checking is realized at the actual current stack. Future
    source phase changes are not flattened into the request's entry context. -/
theorem source_current_request_checked
    (source : Source operations policy contracts tables fixed outside scope (.perform effect operation operand) segment
      (OwnerPhaseTransitions.available (ownedTickets (segment.append fixed))) after output demand row)
    (isValue : operand.IsValue) :
    ∃ environment input, CheckedAt operations environment
      (CallableProtectionFrames.contextOf tables (segment.append fixed) ++ outside) (.perform effect operation operand) input := by
  cases source with
  | checked current pending accepted =>
      obtain ⟨raw, summary, same, empty, exported⟩ := request_summary current isValue
      rw [check_footprint_append, Bool.and_eq_true_iff] at accepted
      refine ⟨_, _, raw, summary, ?_⟩
      rw [exportAt, OwnerPhaseTransitions.project_actual] at exported
      rw [← residual_check, exported]
      exact accepted.1

section Execution
variable {segment fixed : Stack} {issued completed : List Owner}

theorem focus_joint
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨whole, scope, segment.append fixed⟩, issued, completed⟩, activations⟩ result outgoing bound)
    (source : Source operations policy contracts tables fixed outside scope whole segment before after output demand row)
    (focus : Focus whole child position) :
    ∃ plain : PlainData, plain.context = position ∧ plain.scope = scope ∧
      let initial : NamedState := ⟨⟨⟨whole, scope, segment.append fixed⟩, issued, completed⟩, activations⟩
      let next := ScopedPortJoint.advanceState initial ⟨child, scope, (Stack.push (.plain plain) segment).append fixed⟩ [] []
      NamedAccessStep ambient initial next ∧
      CompletionJoint.Valid declarations policy registry ambient next result outgoing bound ∧
      Source operations policy contracts tables fixed outside scope child (.push (.plain plain) segment) before after output demand row := by
  obtain ⟨plain, shape, saved, step, preserved⟩ := CompletionJoint.focus_preserves valid focus
  exact ⟨plain, shape, saved, step, preserved, source_focus source (shape ▸ focus) saved⟩

theorem plug_joint
    (valid : CompletionJoint.Valid declarations policy registry ambient
      ⟨⟨⟨value, scope, (Stack.push (.plain plain) segment).append fixed⟩, issued, completed⟩, activations⟩ result outgoing bound)
    (source : Source operations policy contracts tables fixed outside scope value (.push (.plain plain) segment)
      before after output demand row) (isValue : value.IsValue) :
    let initial : NamedState := ⟨⟨⟨value, scope, (Stack.push (.plain plain) segment).append fixed⟩, issued, completed⟩, activations⟩
    let next := ScopedPortJoint.advanceState initial ⟨plain.context.plug value, plain.scope, segment.append fixed⟩ [] []
    NamedAccessStep ambient initial next ∧
      CompletionJoint.Valid declarations policy registry ambient next result outgoing bound ∧
      Source operations policy contracts tables fixed outside plain.scope (plain.context.plug value) segment before after output demand row := by
  obtain ⟨step, preserved⟩ := CompletionJoint.plug_preserves valid isValue
  exact ⟨step, preserved, source_plug source (CompletionJoint.current_closed_value valid isValue)⟩

end Execution

namespace Examples
open OpenOwnerUses.Examples (operations policy tickets tables tail localHandler waiting)
open OwnerPhaseTransitions.Examples (innerWaiting capture whole)

def neutral : ResumeContract := ⟨.scalar, .scalar, false, [], [], [], some []⟩
def captured : ResumeContract := ⟨.scalar, .scalar, false, [29, 9], [], [29], none⟩
def contracts : Contracts := fun owner =>
  if owner = 19 then some captured else if owner = 29 ∨ owner = 9 then some neutral else none

def initial : Phases := OwnerPhaseTransitions.available [29, 9]
def after29 : Phases := spend initial 29

theorem consume29 : Trace initial [29] after29 := .cons rfl .nil

theorem consume9 : Trace after29 [9] OwnerPhaseTransitions.empty := by
  have both : Trace initial [29, 9] OwnerPhaseTransitions.empty :=
    OwnerPhaseTransitions.trace_all_owned (List.Perm.refl _) (by decide)
  cases both with
  | cons ready rest => exact rest

theorem unit_source (inside : OwnerPhases.Context) (environment : CallableProtection.Environment) (scope : Scope) (phases : Phases) :
    Derives operations policy contracts inside environment scope phases .unit phases .scalar [] [] :=
  .stable .unit (by simp [exportAt, residual_empty])

theorem resume29_source (inside : OwnerPhases.Context) (environment : CallableProtection.Environment) :
    Derives operations policy contracts inside environment (.ticket 30 29) initial (.resume 30 .unit) after29 .scalar [29] [] :=
  .resume (contract := neutral) rfl rfl rfl (unit_source _ _ _ _) consume29

theorem resume9_source (inside : OwnerPhases.Context) (environment : CallableProtection.Environment) :
    Derives operations policy contracts inside environment (.ticket 10 9) after29 (.resume 10 .unit)
      OwnerPhaseTransitions.empty .scalar [9] [] :=
  .resume (contract := neutral) rfl rfl rfl (unit_source _ _ _ _) consume9

/-- The exact interior-owner stack excluded by the preceding source judgment
    now has a source derivation, not just an ownership trace. -/
theorem captured_source (fixed : Stack) : Segment operations policy contracts tables fixed capture
    initial .scalar OwnerPhaseTransitions.empty .scalar [29, 9] [] := by
  have outerHead : ContextDerives operations policy contracts
      (OwnerPhases.ofStack tables ((Stack.push (.handler localHandler) .nil).append fixed))
      CallableProtection.Environment.empty waiting.scope waiting.context after29 .scalar OwnerPhaseTransitions.empty .scalar [9] [] :=
    .bind (resume9_source _ _)
  have remaining : Segment operations policy contracts tables fixed OpenOwnerUses.Examples.capture
      after29 .scalar OwnerPhaseTransitions.empty .scalar [9] [] := .push (.plain outerHead) (.push .handler .nil)
  have innerHead : ContextDerives operations policy contracts
      (OwnerPhases.ofStack tables ((Stack.live 29 .unit .unit .nil (.ticket 10 9) OpenOwnerUses.Examples.capture).append fixed))
      CallableProtection.Environment.empty innerWaiting.scope innerWaiting.context initial .scalar after29 .scalar [29] [] :=
    .bind (resume29_source _ _)
  exact .push (.plain innerHead) (.live (contract := neutral) rfl rfl rfl remaining)

theorem tail_source : Segment operations policy contracts tables .nil tail
    OwnerPhaseTransitions.empty .scalar OwnerPhaseTransitions.empty .scalar [] [] := .live (contract := neutral) rfl rfl rfl .nil

theorem whole_source : Segment operations policy contracts tables .nil whole
    initial .scalar OwnerPhaseTransitions.empty .scalar [29, 9] [] :=
  segment_append (front := capture) (firstDemand := [29, 9]) (firstRow := []) (captured_source tail) tail_source

theorem request_source : Source operations policy contracts tables .nil [] (.ticket 30 29)
    OpenOwnerUses.Examples.request whole initial OwnerPhaseTransitions.empty .scalar [29, 9] [] := by
  have current : Derives operations policy contracts (OwnerPhases.ofStack tables (whole.append .nil))
      CallableProtection.Environment.empty (.ticket 30 29) initial OpenOwnerUses.Examples.request initial .scalar [] [] :=
    .perform (requestRow := []) rfl (unit_source _ _ _ _) (by decide)
  exact .checked current whole_source rfl

theorem request_checked_at_actual_stack :
    ∃ environment input, CheckedAt operations environment
      (CallableProtectionFrames.contextOf tables (whole.append .nil) ++ []) OpenOwnerUses.Examples.request input :=
  source_current_request_checked request_source trivial

theorem before_resume_source : Source operations policy contracts tables .nil [] (.ticket 20 19) (.resume 20 .unit)
    OwnerPhaseTransitions.Examples.beforeResume.stack
    (OwnerPhaseTransitions.available (ownedTickets OwnerPhaseTransitions.Examples.beforeResume.stack))
    OwnerPhaseTransitions.empty .scalar [19, 29, 9] [] := by
  have current : Derives operations policy contracts
      (OwnerPhases.ofStack tables (OwnerPhaseTransitions.Examples.beforeResume.stack.append .nil))
      CallableProtection.Environment.empty (.ticket 20 19)
      (OwnerPhaseTransitions.available (ownedTickets OwnerPhaseTransitions.Examples.beforeResume.stack))
      (.resume 20 .unit) OwnerPhaseTransitions.empty .scalar [19, 29, 9] [] :=
    .resume (contract := captured) rfl rfl rfl (unit_source _ _ _ _)
      (OwnerPhaseTransitions.trace_all_owned (List.Perm.refl _) (by decide))
  have pending : Segment operations policy contracts tables .nil OwnerPhaseTransitions.Examples.beforeResume.stack
      OwnerPhaseTransitions.empty .scalar OwnerPhaseTransitions.empty .scalar [] [] :=
    .live (contract := captured) rfl rfl rfl tail_source
  exact .checked current pending rfl

theorem actual_cut_source :
    ∃ phases intermediate firstDemand secondDemand firstRow secondRow,
      Segment operations policy contracts tables (tail.append .nil) capture initial .scalar phases intermediate firstDemand firstRow ∧
      Segment operations policy contracts tables .nil tail phases intermediate OwnerPhaseTransitions.empty .scalar secondDemand secondRow ∧
      [29, 9] = firstDemand ++ secondDemand ∧ [] = firstRow ++ secondRow :=
  capture_segment OwnerPhaseTransitions.Examples.selected_cut whole_source

theorem contract_captured_source : captured.resumeDemand = OwnerPhaseTransitions.Examples.interface.demand ∧
    captured.held = ProtectionContexts.protectedMode capture.erase ∧
    Segment operations policy contracts tables tail capture initial captured.input OwnerPhaseTransitions.empty captured.answer
      captured.resumeDemand captured.resumeRow := ⟨rfl, rfl, captured_source tail⟩

def restored : Stack := capture.append (.spent 19 .integer (.ticket 10 9) .nil)

theorem restored_source : Source operations policy contracts tables tail [] (.ticket 20 19) .unit restored
    initial OwnerPhaseTransitions.empty .scalar [29, 9] [] := by
  have waiting : Segment operations policy contracts tables tail (.spent 19 .integer (.ticket 10 9) .nil)
      OwnerPhaseTransitions.empty .scalar OwnerPhaseTransitions.empty .scalar [] [] :=
    .spent (contract := captured) rfl rfl .nil
  have saved := captured_source ((Stack.spent 19 .integer (.ticket 10 9) .nil).append tail)
  have restoredSegment := segment_append saved waiting
  exact .checked (unit_source _ CallableProtection.Environment.empty _ _) restoredSegment rfl

theorem actual_restored_shape : OwnerPhaseTransitions.Examples.afterResume.stack = restored.append tail := by
  simp only [OwnerPhaseTransitions.Examples.afterResume, restored, stack_append_assoc, Stack.append]

theorem restoration_evidence :
    RawStep OwnerPhaseTransitions.Examples.beforeResume OwnerPhaseTransitions.Examples.afterResume [] [.ticket 19] ∧
    ConfigurationUsage policy tickets OwnerPhaseTransitions.Examples.afterResume ∧
    Source operations policy contracts tables tail [] (.ticket 20 19) .unit restored
      initial OwnerPhaseTransitions.empty .scalar [29, 9] [] :=
  ⟨OwnerPhaseTransitions.Examples.actual_resume, OwnerPhaseTransitions.Examples.after_resume_usage, restored_source⟩

theorem neutral_discard_source : Derives operations policy contracts inside environment (.ticket 30 29) initial (.discard 30)
    after29 .scalar [29] [] := .discard (contract := neutral) rfl rfl rfl rfl rfl consume29

theorem spent_resume_rejected : ¬ Derives operations policy contracts inside environment (.ticket 30 29) after29
    (.resume 30 .unit) after result demand row := fun source => resume_consumed_rejected source rfl rfl

theorem captured_discard_rejected : ¬ Derives operations policy contracts inside environment (.ticket 20 19) before
    (.discard 20) after result demand row := by
  intro source
  cases source with
  | stable summary exported => cases summary
  | discard known resolved allowed unprotected closable transition =>
      have ownerEq : _ = 19 := Option.some.inj (resolved.symm.trans rfl)
      subst_vars
      have contractEq := Option.some.inj (known.symm.trans (show contracts 19 = some captured from rfl))
      subst_vars
      cases closable

theorem restoration_source_trace :
    Trace (OwnerPhaseTransitions.available (ownedTickets OwnerPhaseTransitions.Examples.beforeResume.stack)) [19, 29, 9]
      OwnerPhaseTransitions.empty := source_configuration_trace before_resume_source

end Examples

end Ash.OneShot.OwnerSource

#print axioms Ash.OneShot.OwnerSource.source_trace
#print axioms Ash.OneShot.OwnerSource.source_monotone
#print axioms Ash.OneShot.OwnerSource.source_no_repeated_owner
#print axioms Ash.OneShot.OwnerSource.value_summary
#print axioms Ash.OneShot.OwnerSource.substitution
#print axioms Ash.OneShot.OwnerSource.bind_summary
#print axioms Ash.OneShot.OwnerSource.beta_summary
#print axioms Ash.OneShot.OwnerSource.resume_consumed_rejected
#print axioms Ash.OneShot.OwnerSource.source_inside_congr
#print axioms Ash.OneShot.OwnerSource.trace_member_iff_changes
#print axioms Ash.OneShot.OwnerSource.trace_same_endpoints
#print axioms Ash.OneShot.OwnerSource.branch_demands_agree
#print axioms Ash.OneShot.OwnerSource.context_plug
#print axioms Ash.OneShot.OwnerSource.context_trace
#print axioms Ash.OneShot.OwnerSource.context_inside_congr
#print axioms Ash.OneShot.OwnerSource.frame_trace
#print axioms Ash.OneShot.OwnerSource.frame_inside_congr
#print axioms Ash.OneShot.OwnerSource.segment_trace
#print axioms Ash.OneShot.OwnerSource.segment_monotone
#print axioms Ash.OneShot.OwnerSource.segment_no_repeated_owner
#print axioms Ash.OneShot.OwnerSource.segment_append
#print axioms Ash.OneShot.OwnerSource.segment_decompose
#print axioms Ash.OneShot.OwnerSource.capture_segment
#print axioms Ash.OneShot.OwnerSource.split_export
#print axioms Ash.OneShot.OwnerSource.stable_context
#print axioms Ash.OneShot.OwnerSource.focus_decompose
#print axioms Ash.OneShot.OwnerSource.source_configuration_trace
#print axioms Ash.OneShot.OwnerSource.plain_export
#print axioms Ash.OneShot.OwnerSource.source_focus
#print axioms Ash.OneShot.OwnerSource.source_plug
#print axioms Ash.OneShot.OwnerSource.value_cannot_reach_live
#print axioms Ash.OneShot.OwnerSource.source_bind
#print axioms Ash.OneShot.OwnerSource.source_beta
#print axioms Ash.OneShot.OwnerSource.selected_branch
#print axioms Ash.OneShot.OwnerSource.source_branch
#print axioms Ash.OneShot.OwnerSource.request_summary
#print axioms Ash.OneShot.OwnerSource.source_current_request_checked
#print axioms Ash.OneShot.OwnerSource.focus_joint
#print axioms Ash.OneShot.OwnerSource.plug_joint
#print axioms Ash.OneShot.OwnerSource.Examples.consume29
#print axioms Ash.OneShot.OwnerSource.Examples.consume9
#print axioms Ash.OneShot.OwnerSource.Examples.unit_source
#print axioms Ash.OneShot.OwnerSource.Examples.resume29_source
#print axioms Ash.OneShot.OwnerSource.Examples.resume9_source
#print axioms Ash.OneShot.OwnerSource.Examples.captured_source
#print axioms Ash.OneShot.OwnerSource.Examples.tail_source
#print axioms Ash.OneShot.OwnerSource.Examples.whole_source
#print axioms Ash.OneShot.OwnerSource.Examples.request_source
#print axioms Ash.OneShot.OwnerSource.Examples.request_checked_at_actual_stack
#print axioms Ash.OneShot.OwnerSource.Examples.before_resume_source
#print axioms Ash.OneShot.OwnerSource.Examples.actual_cut_source
#print axioms Ash.OneShot.OwnerSource.Examples.contract_captured_source
#print axioms Ash.OneShot.OwnerSource.Examples.restored_source
#print axioms Ash.OneShot.OwnerSource.Examples.actual_restored_shape
#print axioms Ash.OneShot.OwnerSource.Examples.restoration_evidence
#print axioms Ash.OneShot.OwnerSource.Examples.neutral_discard_source
#print axioms Ash.OneShot.OwnerSource.Examples.spent_resume_rejected
#print axioms Ash.OneShot.OwnerSource.Examples.captured_discard_rejected
#print axioms Ash.OneShot.OwnerSource.Examples.restoration_source_trace
