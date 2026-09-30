import DeclaredSourceFrames
import RecursiveContexts

/-! Context decomposition and recomposition retaining hereditary declarations.
The structural cases follow RecursiveContexts; callable decomposition and all
requirement evaluation laws are reused from the established proofs. -/
namespace Ash.OneShot.DeclaredSourceContexts
open ScopedExpressions ScopedExecution ProtectionContracts ProtectionResiduals CoherentSourceTypes
open DeclaredSources (Expression)
open RecursiveRequirements (Requirements Checked evaluate)
open OwnerPhaseTransitions (Phases spendAll)
open RecursiveContexts (evaluate_request export_rows)

theorem stable_context
    (source : ContextSummary operations world environment allowed position input output raw) :
    ∃ requirements : Requirements [],
      DeclaredSourceFrames.Context operations policy contracts world environment allowed scope position input output [] requirements ∧
      ∀ store receiving before, evaluate store receiving before requirements = OwnerSource.exportAt receiving before raw := by
  cases source with
  | pairLeft right => exact ⟨_, .pairLeft (.stable right), fun _ _ _ => evaluate_request⟩
  | pairRight left => exact ⟨_, .pairRight (DeclaredSourceValues.from_legacy left), fun _ _ _ => evaluate_request⟩
  | appFunction argument admitted =>
      refine ⟨_, .appFunction (.stable argument) admitted, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, evaluate_request, spendAll, List.nil_append, export_rows]
  | appArgument function admitted => exact ⟨_, .appArgument (DeclaredSourceValues.from_legacy function) admitted, fun _ _ _ => evaluate_request⟩
  | bind body => exact ⟨_, .bind (.stable body), fun _ _ _ => evaluate_request⟩
  | branch yes no =>
      refine ⟨_, .branch (.stable yes) (.stable no) (.refl _), ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_choice, evaluate_request, export_rows]
  | perform known admitted formed => exact ⟨_, .perform known admitted formed, fun _ _ _ => evaluate_request⟩
  | resource body formed effectsBound admitted outward =>
      exact ⟨_, .resource (fun identity fresh => DeclaredSources.Callable.from_generic (CallableSources.from_legacy (body identity fresh)
        (fun _ _ _ _ _ _ checked => .stable checked))) formed effectsBound admitted outward, fun _ _ _ => evaluate_request⟩
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
      DeclaredSourceFrames.Context operations policy contracts world environment allowed scope position input output [] requirements ∧
      ∀ store receiving before, evaluate store receiving before requirements = OwnerSource.exportAt receiving before raw := by
  cases source with
  | pairLeft right => exact ⟨_, .pairLeft (.callable (DeclaredSources.Callable.from_generic right)), fun _ _ _ => evaluate_request⟩
  | pairRight left => exact ⟨_, .pairRight (DeclaredSources.Callable.from_generic left), fun _ _ _ => evaluate_request⟩
  | appFunction argument admitted =>
      refine ⟨_, .appFunction (.callable (DeclaredSources.Callable.from_generic argument)) admitted, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, evaluate_request, spendAll, List.nil_append, export_rows]
  | appArgument function admitted => exact ⟨_, .appArgument (DeclaredSources.Callable.from_generic function) admitted, fun _ _ _ => evaluate_request⟩
  | bind body => exact ⟨_, .bind (.callable (DeclaredSources.Callable.from_generic body)), fun _ _ _ => evaluate_request⟩
  | branch yes no =>
      refine ⟨_, .branch (.callable (DeclaredSources.Callable.from_generic yes)) (.callable (DeclaredSources.Callable.from_generic no)) (.refl _), ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_choice, evaluate_request, export_rows]
  | perform known admitted formed => exact ⟨_, .perform known admitted formed, fun _ _ _ => evaluate_request⟩
  | resource body formed effectsBound admitted outward =>
      exact ⟨_, .resource (fun identity fresh => DeclaredSources.Callable.from_generic (body identity fresh)) formed effectsBound admitted outward, fun _ _ _ => evaluate_request⟩
  | cleanup body admitted =>
      refine ⟨_, .cleanup (.callable (DeclaredSources.Callable.from_generic body)) admitted, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, evaluate_request, spendAll, List.nil_append, export_rows]

theorem context_plug
    (context : DeclaredSourceFrames.Context operations policy contracts world environment allowed scope position input output restDemand rest)
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
      refine ⟨_, .pair (DeclaredSourceValues.expression left _) child, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty, spendAll,
        RecursiveRecomposition.merge_empty_left, RecursiveRecomposition.merge_empty_right]
  | appFunction argument admitted =>
      refine ⟨_, .app child argument admitted, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence, PhaseRechecking.spendAll_append, merge_assoc]
  | appArgument function admitted =>
      rw [List.append_nil]
      refine ⟨_, .app (DeclaredSourceValues.expression function _) child admitted, ?_⟩
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
      DeclaredSourceFrames.Context operations policy contracts world environment allowed scope position input output restDemand rest ∧
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
      obtain ⟨input, childRaw, restRaw, childSource, context, same⟩ := CallableContexts.focus_decompose focus summary.to_generic
      obtain ⟨rest, restSource, evaluation⟩ := callable_context context
      refine ⟨input, [], [], .request [] childRaw, rest, .callable (DeclaredSources.Callable.from_generic childSource), restSource, rfl, ?_⟩
      intro store receiving before
      simp only [evaluate_request, same, export_rows, evaluation, spendAll]
  | lambda => cases focus
  | purePair left right => cases focus with
    | pairLeft =>
        refine ⟨_, [], [], _, _, left, .pairLeft right, rfl, ?_⟩
        intro store receiving before
        simp only [RecursiveRecomposition.evaluate_empty, merge, List.nil_append]
    | pairRight isValue notValue =>
        refine ⟨_, [], [], _, _, right, .pairRight (DeclaredSourceValues.value_summary left isValue), rfl, ?_⟩
        intro store receiving before
        simp only [RecursiveRecomposition.evaluate_empty, merge, List.nil_append]
  | pair left right => cases focus with
    | pairLeft => exact ⟨_, _, _, _, _, left, .pairLeft right, rfl, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
    | pairRight isValue notValue =>
        have empty := SourceTemplates.expression_value_demand (DeclaredSources.expression_erase left) isValue
        subst_vars
        refine ⟨_, _, [], _, _, right, .pairRight (DeclaredSourceValues.value_summary left isValue), by simp, ?_⟩
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase left) isValue,
          RecursiveRecomposition.evaluate_empty, spendAll, RecursiveRecomposition.merge_empty_left, RecursiveRecomposition.merge_empty_right]
  | app function argument admitted => cases focus with
    | appFunction =>
        refine ⟨_, _, _, _, _, function, .appFunction argument admitted, rfl, ?_⟩
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence, PhaseRechecking.spendAll_append, merge_assoc]
    | appArgument isValue notValue =>
        have empty := SourceTemplates.expression_value_demand (DeclaredSources.expression_erase function) isValue
        subst_vars
        refine ⟨_, _, [], _, _, argument, .appArgument (DeclaredSourceValues.value_summary function isValue) admitted, by simp, ?_⟩
        intro store receiving before
        simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence,
          RecursiveRecomposition.value_evaluation (DeclaredSources.expression_erase function) isValue, spendAll, List.nil_append,
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


end Ash.OneShot.DeclaredSourceContexts

#print axioms Ash.OneShot.DeclaredSourceContexts.stable_context
#print axioms Ash.OneShot.DeclaredSourceContexts.callable_context
#print axioms Ash.OneShot.DeclaredSourceContexts.context_plug
#print axioms Ash.OneShot.DeclaredSourceContexts.focus_decompose
