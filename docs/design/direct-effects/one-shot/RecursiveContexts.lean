import RecursiveExpressions
import CallableContexts

/-!
Evaluation-context decomposition and recomposition for recursive requirements.
Ordinary pending frames add a neutral interpretation layer; they do not add an
owner or change the template store. Runtime annotations come from shared types.
-/

namespace Ash.OneShot.RecursiveContexts
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals CoherentSourceTypes
open SourceTemplates (Expression)
open RecursiveRequirements (Requirements Checked evaluate)
open OwnerPhaseTransitions (Phases spendAll)

theorem selection_congr
    (same : (OwnerPhases.consume owner first).isSome = (OwnerPhases.consume owner second).isSome)
    (selected : OwnerPhases.Consumes owner first waiting) :
    ∃ next, OwnerPhases.Consumes owner second next := by
  rw [OwnerPhases.consumes_sound selected] at same
  cases found : OwnerPhases.consume owner second with
  | none => simp [found] at same
  | some next => exact ⟨next, OwnerPhases.consumes_complete found⟩

theorem checked_context_congr
    (checked : Checked store receiving before requirements row)
    (interpret : ∀ nearer phases raw, OwnerSource.exportAt (nearer ++ receiving) phases raw =
      OwnerSource.exportAt (nearer ++ other) phases raw)
    (select : ∀ nearer owner, (OwnerPhases.consume owner (nearer ++ receiving)).isSome =
      (OwnerPhases.consume owner (nearer ++ other)).isSome) :
    Checked store other before requirements row := by
  induction checked generalizing other with
  | request exported => exact .request ((interpret _ _ _).symm.trans exported)
  | retire ready => exact .retire ready
  | spent consumed => exact .spent consumed
  | invoke known ready selection body ih =>
      obtain ⟨waiting, selected⟩ := selection_congr (select _ _) selection
      apply Checked.invoke known ready selected
      apply ih
      · intro frontNearer phases raw
        simpa only [List.append_assoc] using interpret (frontNearer ++ _) phases raw
      · intro frontNearer owner
        simpa only [List.append_assoc] using select (frontNearer ++ _) owner
  | sequence first second ihFirst ihSecond => exact .sequence (ihFirst interpret select) (ihSecond interpret select)
  | emitAfter body exported ih => exact .emitAfter (ih interpret select) ((interpret _ _ _).symm.trans exported)
  | choice first second ihFirst ihSecond => exact .choice (ihFirst interpret select) (ihSecond interpret select)

theorem plain_export_middle (nearer receiving : OwnerPhases.Context) (before : Phases) (raw : Footprint) :
    OwnerSource.exportAt (nearer ++ .ordinary (.barrier false) :: receiving) before raw =
      OwnerSource.exportAt (nearer ++ receiving) before raw := by
  simp only [OwnerSource.exportAt, OwnerPhaseTransitions.project_append, residual_append]
  cases first : residualize (OwnerPhaseTransitions.project nearer before) raw with
  | none => rfl
  | some next => exact OwnerSource.plain_export receiving before next

theorem plain_consume_middle (nearer receiving : OwnerPhases.Context) (owner : Nat) :
    (OwnerPhases.consume owner (nearer ++ .ordinary (.barrier false) :: receiving)).isSome =
      (OwnerPhases.consume owner (nearer ++ receiving)).isSome :=
  ResourceRequirements.ordinary_consume_middle nearer receiving owner (.barrier false)

theorem checked_plain_iff :
    Checked store (.ordinary (.barrier false) :: receiving) before requirements row ↔
      Checked store receiving before requirements row := by
  constructor
  · intro checked
    exact checked_context_congr checked (fun _ _ _ => plain_export_middle _ _ _ _) (fun _ _ => plain_consume_middle _ _ _)
  · intro checked
    exact checked_context_congr checked (fun _ _ _ => (plain_export_middle _ _ _ _).symm)
      (fun _ _ => (plain_consume_middle _ _ _).symm)

theorem evaluate_plain : evaluate store (.ordinary (.barrier false) :: receiving) before requirements =
    evaluate store receiving before requirements := by
  cases original : evaluate store receiving before requirements with
  | some row =>
      exact RecursiveRequirements.checked_complete
        (checked_plain_iff.mpr (RecursiveRequirements.evaluate_sound original))
  | none =>
      cases extended : evaluate store (.ordinary (.barrier false) :: receiving) before requirements with
      | none => rfl
      | some row =>
          have rejected := RecursiveRequirements.checked_complete
            (checked_plain_iff.mp (RecursiveRequirements.evaluate_sound extended))
          simp [original] at rejected

theorem evaluate_request : evaluate store receiving before (.request [] raw) = OwnerSource.exportAt receiving before raw := by
  simp only [evaluate, RecursiveRequirements.evaluateFuel, List.nil_append]

theorem export_rows : OwnerSource.exportAt receiving before (first ++ second) =
    merge (OwnerSource.exportAt receiving before first) (OwnerSource.exportAt receiving before second) :=
  residual_rows_append _ _ _

theorem stable_context
    (source : ContextSummary operations world environment allowed position input output raw) :
    ∃ requirements : Requirements [],
      SourceTemplates.Context operations policy contracts world environment allowed scope position input output [] requirements ∧
      ∀ store receiving before, evaluate store receiving before requirements = OwnerSource.exportAt receiving before raw := by
  cases source with
  | pairLeft right => exact ⟨_, .pairLeft (.stable right), fun _ _ _ => evaluate_request⟩
  | pairRight left => exact ⟨_, .pairRight (.stable left), fun _ _ _ => evaluate_request⟩
  | appFunction argument admitted =>
      refine ⟨_, .appFunction (.stable argument) admitted, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, evaluate_request, spendAll, List.nil_append, export_rows]
  | appArgument function admitted => exact ⟨_, .appArgument (.stable function) admitted, fun _ _ _ => evaluate_request⟩
  | bind body => exact ⟨_, .bind (.stable body), fun _ _ _ => evaluate_request⟩
  | branch yes no =>
      refine ⟨_, .branch (.stable yes) (.stable no) (.refl _), ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_choice, evaluate_request, export_rows]
  | perform known admitted formed => exact ⟨_, .perform known admitted formed, fun _ _ _ => evaluate_request⟩
  | resource body formed effectsBound admitted outward =>
      exact ⟨_, .resource (fun identity fresh => CallableSources.from_legacy (body identity fresh)
        (fun _ _ _ _ _ _ checked => .stable checked)) formed effectsBound admitted outward, fun _ _ _ => evaluate_request⟩
  | cleanup body admitted =>
      refine ⟨_, .cleanup (.stable body) admitted, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, evaluate_request, spendAll, List.nil_append, export_rows]

theorem callable_context
    (source : CallableContexts.ContextSummary operations
      (fun world environment requests code value demand requirements =>
        Expression operations policy contracts world requests .none environment code value demand requirements)
      world environment allowed position input output raw) :
    ∃ requirements : Requirements [],
      SourceTemplates.Context operations policy contracts world environment allowed scope position input output [] requirements ∧
      ∀ store receiving before, evaluate store receiving before requirements = OwnerSource.exportAt receiving before raw := by
  cases source with
  | pairLeft right => exact ⟨_, .pairLeft (.callable right), fun _ _ _ => evaluate_request⟩
  | pairRight left => exact ⟨_, .pairRight (.callable left), fun _ _ _ => evaluate_request⟩
  | appFunction argument admitted =>
      refine ⟨_, .appFunction (.callable argument) admitted, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, evaluate_request, spendAll, List.nil_append, export_rows]
  | appArgument function admitted => exact ⟨_, .appArgument (.callable function) admitted, fun _ _ _ => evaluate_request⟩
  | bind body => exact ⟨_, .bind (.callable body), fun _ _ _ => evaluate_request⟩
  | branch yes no =>
      refine ⟨_, .branch (.callable yes) (.callable no) (.refl _), ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_choice, evaluate_request, export_rows]
  | perform known admitted formed => exact ⟨_, .perform known admitted formed, fun _ _ _ => evaluate_request⟩
  | resource body formed effectsBound admitted outward =>
      exact ⟨_, .resource body formed effectsBound admitted outward, fun _ _ _ => evaluate_request⟩
  | cleanup body admitted =>
      refine ⟨_, .cleanup (.callable body) admitted, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, evaluate_request, spendAll, List.nil_append, export_rows]

theorem context_plug
    (context : SourceTemplates.Context operations policy contracts world environment allowed scope position input output restDemand rest)
    (child : Expression operations policy contracts world allowed scope environment code input childDemand current) :
    ∃ combined : Requirements (childDemand ++ restDemand),
      Expression operations policy contracts world allowed scope environment (position.plug code) output
        (childDemand ++ restDemand) combined ∧
      ∀ store receiving before, evaluate store receiving before combined =
        merge (evaluate store receiving before current) (evaluate store receiving (spendAll before childDemand) rest) := by
  cases context with
  | pairLeft right => exact ⟨_, .pair child right, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
  | pairRight left =>
      rw [List.append_nil]
      refine ⟨_, .pair (left.expression _) child, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty, spendAll,
        RecursiveRecomposition.merge_empty_left, RecursiveRecomposition.merge_empty_right]
  | appFunction argument admitted =>
      refine ⟨_, .app child argument admitted, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence, PhaseRechecking.spendAll_append, merge_assoc]
  | appArgument function admitted =>
      rw [List.append_nil]
      refine ⟨_, .app (function.expression _) child admitted, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty,
        spendAll, List.nil_append, RecursiveRecomposition.merge_empty_left, evaluate_request]
  | bind body => exact ⟨_, .bind child body, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
  | branch yes no same => exact ⟨_, .branch child yes no same, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
  | perform known admitted formed =>
      rw [List.append_nil]
      refine ⟨_, .perform known admitted child formed, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, evaluate_request, List.nil_append]
  | resource body formed effectsBound admitted outward =>
      rw [List.append_nil]
      refine ⟨_, .resource child body formed effectsBound admitted outward, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, evaluate_request, List.nil_append]
  | scopedResource body formed effectsBound admitted hidden =>
      exact ⟨_, .scopedResource child body formed effectsBound admitted hidden,
        fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
  | resume known resolved permission admitted formed =>
      exact ⟨_, .resume known resolved permission child admitted formed, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
  | cleanup body admitted =>
      refine ⟨_, .cleanup child body admitted, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence, PhaseRechecking.spendAll_append, merge_assoc]

theorem focus_decompose
    (source : Expression operations policy contracts world allowed scope environment whole output demand requirements)
    (focus : Focus whole child position) :
    ∃ (input : Value) (childDemand restDemand : List Nat) (current : Requirements childDemand) (rest : Requirements restDemand),
      Expression operations policy contracts world allowed scope environment child input childDemand current ∧
      SourceTemplates.Context operations policy contracts world environment allowed scope position input output restDemand rest ∧
      demand = childDemand ++ restDemand ∧
      ∀ store receiving before, evaluate store receiving before requirements =
        merge (evaluate store receiving before current) (evaluate store receiving (spendAll before childDemand) rest) := by
  cases source with
  | handler => cases focus
  | stable summary =>
      obtain ⟨input, childRaw, restRaw, childSource, context, same⟩ := CoherentSourceTypes.focus_decompose focus summary
      obtain ⟨rest, restSource, evaluation⟩ := stable_context context
      refine ⟨input, [], [], .request [] childRaw, rest, .stable childSource, restSource, rfl, ?_⟩
      intro store receiving before
      simp only [evaluate_request, same, export_rows, evaluation, spendAll]
  | callable summary =>
      obtain ⟨input, childRaw, restRaw, childSource, context, same⟩ := CallableContexts.focus_decompose focus summary
      obtain ⟨rest, restSource, evaluation⟩ := callable_context context
      refine ⟨input, [], [], .request [] childRaw, rest, .callable childSource, restSource, rfl, ?_⟩
      intro store receiving before
      simp only [evaluate_request, same, export_rows, evaluation, spendAll]
  | lambda => cases focus
  | purePair left right => cases focus with
    | pairLeft =>
        refine ⟨_, [], [], _, _, left, .pairLeft right, rfl, ?_⟩
        intro store receiving before
        simp only [RecursiveRecomposition.evaluate_empty, merge, List.nil_append]
    | pairRight isValue notValue =>
        refine ⟨_, [], [], _, _, right, .pairRight (RecursiveRecomposition.value_summary left isValue), rfl, ?_⟩
        intro store receiving before
        simp only [RecursiveRecomposition.evaluate_empty, merge, List.nil_append]
  | pair left right => cases focus with
    | pairLeft => exact ⟨_, _, _, _, _, left, .pairLeft right, rfl, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
    | pairRight isValue notValue =>
        have empty := SourceTemplates.expression_value_demand left isValue
        subst_vars
        refine ⟨_, _, [], _, _, right, .pairRight (RecursiveRecomposition.value_summary left isValue), by simp, ?_⟩
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.value_evaluation left isValue,
          RecursiveRecomposition.evaluate_empty, spendAll, RecursiveRecomposition.merge_empty_left, RecursiveRecomposition.merge_empty_right]
  | app function argument admitted => cases focus with
    | appFunction =>
        refine ⟨_, _, _, _, _, function, .appFunction argument admitted, rfl, ?_⟩
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence, PhaseRechecking.spendAll_append, merge_assoc]
    | appArgument isValue notValue =>
        have empty := SourceTemplates.expression_value_demand function isValue
        subst_vars
        refine ⟨_, _, [], _, _, argument, .appArgument (RecursiveRecomposition.value_summary function isValue) admitted, by simp, ?_⟩
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence,
          RecursiveRecomposition.value_evaluation function isValue, spendAll, List.nil_append,
          RecursiveRecomposition.merge_empty_left, evaluate_request]
  | bind initializer body => cases focus with
    | bind => exact ⟨_, _, _, _, _, initializer, .bind body, rfl, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
  | branch condition yes no same => cases focus with
    | branch => exact ⟨_, _, _, _, _, condition, .branch yes no same, rfl, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
  | perform known admitted operand formed => cases focus with
    | perform =>
        refine ⟨_, _, [], _, _, operand, .perform known admitted formed, by simp, ?_⟩
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_emit, evaluate_request, List.nil_append]
  | resource initializer body formed effectsBound admitted outward => cases focus with
    | resource notValue =>
        refine ⟨_, _, [], _, _, initializer, .resource body formed effectsBound admitted outward, by simp, ?_⟩
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_emit, evaluate_request, List.nil_append]
  | scopedResource initializer body formed effectsBound admitted hidden => cases focus with
    | resource notValue =>
        exact ⟨_, _, _, _, _, initializer, .scopedResource body formed effectsBound admitted hidden,
          rfl, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
  | resume known resolved permission operand admitted formed => cases focus with
    | resume => exact ⟨_, _, _, _, _, operand, .resume known resolved permission admitted formed, rfl,
        fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
  | discard => cases focus
  | cleanup callback body admitted => cases focus with
    | cleanup =>
        refine ⟨_, _, _, _, _, callback, .cleanup body admitted, rfl, ?_⟩
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence, PhaseRechecking.spendAll_append, merge_assoc]

theorem prepare_plain
    (source : Expression operations policy contracts world allowed scope environment whole output demand requirements)
    (focus : Focus whole child position) (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket)
    (input : Value) :
    ∃ plain : PlainData, plain.context = position ∧ plain.scope = scope ∧
      input.port = ScopedPorts.eraseType plain.input ∧ output.port = ScopedPorts.eraseType plain.output := by
  have typed := SourceTemplates.expression_ports source scopeTyped
  have contextBound : ScopedPorts.LexicallyBound environment.ports ticket position.dependencies := by
    apply ScopedPorts.lexical_subset (ScopedPorts.typed_lexical_dependencies typed)
    intro dependency member
    rw [← focus_reconstructs focus]
    exact (context_dependency_membership position child dependency).mpr (Or.inl member)
  obtain ⟨pending, translated⟩ := ScopedPorts.lexical_translation_total contextBound
    (ScopedPorts.scope_typed_names_match (ScopedPorts.effect_scope_has_types scopeTyped))
  exact ⟨⟨position, scope, ScopedPorts.embedPort input.port, ScopedPorts.embedPort output.port, pending, translated⟩,
    rfl, rfl, by simp, by simp⟩

theorem plain_context (plain : PlainData) : OwnerPhases.ofStack tables (.push (.plain plain) stack) =
    .ordinary (.barrier false) :: OwnerPhases.ofStack tables stack := rfl

theorem plain_owners (plain : PlainData) : ownedTickets (.push (.plain plain) stack) = ownedTickets stack := rfl

theorem focus_preserves
    (source : SourceTemplates.CheckedConfiguration operations policy contracts tables world outside scope whole stack output demand row)
    (focus : Focus whole child position) :
    ∃ plain : PlainData,
      RawStep ⟨whole, scope, stack⟩ ⟨child, scope, .push (.plain plain) stack⟩ [] [] ∧
      SourceTemplates.CheckedConfiguration operations policy contracts tables world outside scope child
        (.push (.plain plain) stack) output demand row ∧
      plain.context = position ∧ plain.scope = scope ∧
      OwnerPhaseTransitions.Trace (OwnerPhaseTransitions.available (ownedTickets stack)) []
        (OwnerPhaseTransitions.available (ownedTickets (.push (.plain plain) stack))) := by
  cases source with
  | checked source unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        obtain ⟨input, childDemand, restDemand, currentReq, restReq, childSource, context, sameDemand, evaluation⟩ :=
          focus_decompose current focus
        obtain ⟨plain, contextSame, scopeSame, inputAnnotation, outputAnnotation⟩ := prepare_plain current focus scopeTyped input
        have frame : SourceTemplates.Frame operations policy contracts world (.plain plain) input _ restDemand restReq :=
          .plain (by simpa only [contextSame, scopeSame] using context)
            (by simpa only [scopeSame] using scopeTyped) inputAnnotation outputAnnotation
        have step : RawStep ⟨whole, scope, stack⟩ ⟨child, scope, .push (.plain plain) stack⟩ [] [] := by
          simpa only [scopeSame] using RawStep.focus plain (by simpa only [contextSame] using focus) stack
        refine ⟨plain, step, ?_, contextSame, scopeSame, .nil⟩
        rw [sameDemand, List.append_assoc]
        apply SourceTemplates.check_configuration (.checked childSource scopeTyped (.push frame pending)) unique _ accepted
        have oldEvaluation := RecursiveRequirements.checked_complete checked
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, evaluation] at oldEvaluation
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, plain_context,
          plain_owners, List.cons_append, evaluate_plain]
        simpa only [sameDemand, PhaseRechecking.spendAll_append, merge_assoc] using oldEvaluation

theorem plug_preserves
    (source : SourceTemplates.CheckedConfiguration operations policy contracts tables world outside scope value
      (.push (.plain plain) stack) output demand row)
    (closed : ClosedValue value) :
    SourceTemplates.CheckedConfiguration operations policy contracts tables world outside plain.scope (plain.context.plug value)
      stack output demand row := by
  cases source with
  | checked source unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        have empty := SourceTemplates.expression_value_demand current closed.1
        subst_vars
        cases pending with
        | push frame pending => cases frame with
          | plain context frameScope inputAnnotation outputAnnotation =>
              obtain ⟨combined, combinedSource, evaluation⟩ := context_plug context
                (((RecursiveRecomposition.value_summary current closed.1).change_allowed closed.1 _).expression _)
              apply SourceTemplates.check_configuration (.checked combinedSource frameScope pending) unique _ accepted
              have oldEvaluation := RecursiveRequirements.checked_complete checked
              simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend,
                RecursiveRecomposition.value_evaluation current closed.1, RecursiveRecomposition.merge_empty_left,
                spendAll, plain_owners] at oldEvaluation
              simp only [RecursiveRequirements.evaluate_sequence, RecursiveRequirements.evaluate_prepend, evaluation,
                RecursiveRecomposition.evaluate_empty, RecursiveRecomposition.merge_empty_left, spendAll]
              exact oldEvaluation

theorem value_closed
    (source : SourceTemplates.CheckedConfiguration operations policy contracts tables world outside scope value stack output demand row)
    (isValue : value.IsValue) : ClosedValue value := by
  cases source with
  | checked source unique checked accepted => cases source with
    | checked current scopeTyped pending =>
        exact ScopedPorts.typed_value_closed (SourceTemplates.expression_ports current scopeTyped) isValue

theorem plug_progress
    (source : SourceTemplates.CheckedConfiguration operations policy contracts tables world outside scope value
      (.push (.plain plain) stack) output demand row)
    (isValue : value.IsValue) :
    RawStep ⟨value, scope, .push (.plain plain) stack⟩ ⟨plain.context.plug value, plain.scope, stack⟩ [] [] ∧
      SourceTemplates.CheckedConfiguration operations policy contracts tables world outside plain.scope (plain.context.plug value)
        stack output demand row ∧
      OwnerPhaseTransitions.Trace (OwnerPhaseTransitions.available (ownedTickets (.push (.plain plain) stack))) []
        (OwnerPhaseTransitions.available (ownedTickets stack)) := by
  have closed := value_closed source isValue
  exact ⟨.plug plain value closed scope stack, plug_preserves source closed, .nil⟩

namespace Examples
open SharedResumption.NestedExamples (contracts outer_known outerBoundary)
open SharedResumption.Examples (operations policy tables outside raw effect)
open SourceTemplates.Examples (records currentRequirements requirements current_source outer_boundary_source recursive_check)

def operand : Code := .bind 99 .unit (.variable 99)

theorem operand_summary : Summary operations [] Environment.empty [effect] operand .unit [] :=
  .bind .unit (.variable rfl (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]))

theorem request_source : Expression operations policy contracts [] [effect] (.ticket 7 19) Environment.empty
    (.resume 7 operand) .unit [19, 29] currentRequirements :=
  .resume outer_known rfl rfl (.stable operand_summary) (fun _ member => member)
    (by simp [SharedResumption.NestedExamples.outer, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])

theorem request_checked : SourceTemplates.CheckedConfiguration operations policy contracts tables [] outside (.ticket 7 19)
    (.resume 7 operand) outerBoundary .unit [19, 29] raw :=
  .checked (.checked request_source (.bound (Owners.ports_lookup outer_known)) outer_boundary_source)
    (by decide) recursive_check (by decide)

theorem operand_bind_step (scope : Execution.Scope) (stack : Stack) :
    RawStep ⟨operand, scope, stack⟩ ⟨.unit, scope, stack⟩ [] [] :=
  .bind 99 .unit (.variable 99) scope stack CallableProtection.Examples.unit_closed (by
    intro name member
    simpa [Code.dependencies] using member)

theorem focus_bind_plug : ∃ plain : PlainData,
    RawStep ⟨.resume 7 operand, .ticket 7 19, outerBoundary⟩
      ⟨operand, .ticket 7 19, .push (.plain plain) outerBoundary⟩ [] [] ∧
    SourceTemplates.CheckedConfiguration operations policy contracts tables [] outside (.ticket 7 19)
      operand (.push (.plain plain) outerBoundary) .unit [19, 29] raw ∧
    RawStep ⟨operand, .ticket 7 19, .push (.plain plain) outerBoundary⟩
      ⟨.unit, .ticket 7 19, .push (.plain plain) outerBoundary⟩ [] [] ∧
    SourceTemplates.CheckedConfiguration operations policy contracts tables [] outside (.ticket 7 19)
      .unit (.push (.plain plain) outerBoundary) .unit [19, 29] raw ∧
    RawStep ⟨.unit, .ticket 7 19, .push (.plain plain) outerBoundary⟩
      ⟨.resume 7 .unit, .ticket 7 19, outerBoundary⟩ [] [] ∧
    SourceTemplates.CheckedConfiguration operations policy contracts tables [] outside (.ticket 7 19)
      (.resume 7 .unit) outerBoundary .unit [19, 29] raw := by
  obtain ⟨plain, step, focused, position, scope, trace⟩ :=
    focus_preserves request_checked (Focus.resume (by simp [operand, Code.IsValue]))
  have bound := RecursiveExpressions.bind_preserves focused CallableProtection.Examples.unit_closed
  obtain ⟨plugStep, plugged, plugTrace⟩ := plug_progress bound trivial
  refine ⟨plain, step, focused, operand_bind_step _ _, bound, ?_, ?_⟩
  · simpa only [position, scope, ScopedExecution.Context.plug, Code.subst, if_true] using plugStep
  · simpa only [position, scope, ScopedExecution.Context.plug, Code.subst, if_true] using plugged

theorem operand_then_nested_resume : ∃ restored remaining,
    RawStep ⟨.resume 7 .unit, .ticket 7 19, outerBoundary⟩ ⟨.unit, .ticket 7 19, restored⟩ [] [.ticket 19] ∧
    SourceTemplates.CheckedConfiguration operations policy contracts tables [] outside (.ticket 7 19)
      .unit restored .unit remaining raw ∧ remaining = [29] := by
  obtain ⟨plain, focusStep, focused, bindStep, bound, plugStep, plugged⟩ := focus_bind_plug
  obtain ⟨owner, restored, remaining, step, checked, same, trace⟩ :=
    RecursiveRecomposition.resume_preserves plugged CallableProtection.Examples.unit_closed
  obtain ⟨sameOwner, sameRemaining⟩ := List.cons.inj same
  subst owner
  exact ⟨restored, remaining, step, checked, sameRemaining.symm⟩

end Examples

end Ash.OneShot.RecursiveContexts

#print axioms Ash.OneShot.RecursiveContexts.selection_congr
#print axioms Ash.OneShot.RecursiveContexts.checked_context_congr
#print axioms Ash.OneShot.RecursiveContexts.plain_export_middle
#print axioms Ash.OneShot.RecursiveContexts.plain_consume_middle
#print axioms Ash.OneShot.RecursiveContexts.checked_plain_iff
#print axioms Ash.OneShot.RecursiveContexts.evaluate_plain
#print axioms Ash.OneShot.RecursiveContexts.evaluate_request
#print axioms Ash.OneShot.RecursiveContexts.export_rows
#print axioms Ash.OneShot.RecursiveContexts.stable_context
#print axioms Ash.OneShot.RecursiveContexts.context_plug
#print axioms Ash.OneShot.RecursiveContexts.focus_decompose
#print axioms Ash.OneShot.RecursiveContexts.prepare_plain
#print axioms Ash.OneShot.RecursiveContexts.plain_context
#print axioms Ash.OneShot.RecursiveContexts.plain_owners
#print axioms Ash.OneShot.RecursiveContexts.focus_preserves
#print axioms Ash.OneShot.RecursiveContexts.plug_preserves
#print axioms Ash.OneShot.RecursiveContexts.value_closed
#print axioms Ash.OneShot.RecursiveContexts.plug_progress
#print axioms Ash.OneShot.RecursiveContexts.Examples.operand_summary
#print axioms Ash.OneShot.RecursiveContexts.Examples.request_source
#print axioms Ash.OneShot.RecursiveContexts.Examples.request_checked
#print axioms Ash.OneShot.RecursiveContexts.Examples.operand_bind_step
#print axioms Ash.OneShot.RecursiveContexts.Examples.focus_bind_plug
#print axioms Ash.OneShot.RecursiveContexts.Examples.operand_then_nested_resume

#print axioms Ash.OneShot.RecursiveContexts.callable_context
