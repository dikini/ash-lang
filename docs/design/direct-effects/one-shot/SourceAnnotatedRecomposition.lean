import SourceAnnotatedReduction

/-! Finite context closure and source recomposition preserve the retained
annotations. Requirement evaluation and owner accounting reuse the existing
context-plug laws; contexts carry no future-success premise. -/
namespace Ash.OneShot.SourceAnnotatedCode

def Context.ResourceClosed (context : Context) : Prop :=
  (context.plug (.unit .unit)).ResourceClosed

def Context.checkClosed (context : Context) : Bool :=
  (context.plug (.unit .unit)).checkClosed

theorem Context.check_closed_iff {context : Context} : context.checkClosed = true ↔ context.ResourceClosed :=
  Term.check_closed_iff

/-- A context is closed precisely when its fixed metadata and siblings are
closed. Resource binders still scope only their saved body, not the hole. -/
theorem Context.plug_closed_iff (context : Context) (child : Term) :
    (context.plug child).ResourceClosed ↔ context.ResourceClosed ∧ child.ResourceClosed := by
  cases context <;> simp [Context.ResourceClosed, Context.plug, Term.ResourceClosed,
    Term.freeNames, hintNames, and_assoc, and_left_comm, and_comm]

theorem Focus.context_closed (focus : Focus whole child context) (closed : whole.ResourceClosed) :
    context.ResourceClosed := by
  apply (context.plug_closed_iff child).mp ?_ |>.1
  simpa only [focus.reconstructs] using closed

end Ash.OneShot.SourceAnnotatedCode

namespace Ash.OneShot.SourceAnnotatedSources
open ScopedExecution ProtectionContracts ProtectionResiduals
open RecursiveRequirements (Requirements evaluate)
open OwnerPhaseTransitions (spendAll)
open RecursiveContexts (evaluate_request)
open SourcePlannedTyping (Value Environment Operations Contract Contracts)
open SourcePlanSignatures (Signature)

theorem context_plug_node
    (context : Context operations policy contracts world environment allowed scope position input output restDemand rest checking)
    (child : Expression operations policy contracts world allowed scope environment code input childDemand current childChecking) :
    ∃ (combined : Requirements (childDemand ++ restDemand)) (dependencies : SourceDependencyAnnotations.Dependencies)
      (resultChecking : Signature dependencies),
      Node operations policy contracts world allowed scope environment (position.plug code) output
        (childDemand ++ restDemand) combined resultChecking ∧
      ∀ store receiving before, evaluate store receiving before combined =
        merge (evaluate store receiving before current)
          (evaluate store receiving (OwnerPhaseTransitions.spendAll before childDemand) rest) := by
  cases context with
  | pairLeft right => exact ⟨_, _, _, .pair child right, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
  | pairRight left isValue =>
      rw [List.append_nil]
      refine ⟨_, _, _, .pair (Values.change_context (Values.summary left isValue) isValue _ _) child, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty, spendAll,
        RecursiveRecomposition.merge_empty_left, RecursiveRecomposition.merge_empty_right]
  | appFunction argument admitted =>
      refine ⟨_, _, _, .app child argument admitted, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence, PhaseRechecking.spendAll_append, merge_assoc]
  | appArgument function isValue admitted =>
      rw [List.append_nil]
      refine ⟨_, _, _, .app (Values.change_context (Values.summary function isValue) isValue _ _) child admitted, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence, RecursiveRecomposition.evaluate_empty,
        spendAll, List.nil_append, RecursiveRecomposition.merge_empty_left, evaluate_request]
  | bind body => exact ⟨_, _, _, .bind child body, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
  | branch yes no same => exact ⟨_, _, _, .branch child yes no same, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
  | perform known admitted formed =>
      rw [List.append_nil]
      refine ⟨_, _, _, .perform known admitted child formed, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, evaluate_request, List.nil_append]
  | resource body formed effectsBound admitted hidden =>
      exact ⟨_, _, _, .resource child body formed effectsBound admitted hidden,
        fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
  | resume known resolved permission admitted formed =>
      exact ⟨_, _, _, .resume known resolved permission child admitted formed, fun _ _ _ => RecursiveRequirements.evaluate_sequence⟩
  | cleanup body admitted =>
      refine ⟨_, _, _, .cleanup child body admitted, ?_⟩
      intro store receiving before
      simp only [RecursiveRequirements.evaluate_emit, RecursiveRequirements.evaluate_sequence, PhaseRechecking.spendAll_append, merge_assoc]


/-- Finite retained metadata and the structural context suffice for plugging
any checked child of the same rich input type. -/
theorem context_plug
    (context : Context operations policy contracts world environment allowed scope position input output restDemand rest checking)
    (hint : SourceFocusHints.checkSource Instantiation.Environment.empty position.hint output = true)
    (closed : position.ResourceClosed)
    (child : Expression operations policy contracts world allowed scope environment code input childDemand current childChecking) :
    ∃ (combined : Requirements (childDemand ++ restDemand)) (dependencies : SourceDependencyAnnotations.Dependencies)
      (resultChecking : Signature dependencies),
      Expression operations policy contracts world allowed scope environment (position.plug code) output
        (childDemand ++ restDemand) combined resultChecking ∧
      ∀ store receiving before, evaluate store receiving before combined =
        merge (evaluate store receiving before current)
          (evaluate store receiving (spendAll before childDemand) rest) := by
  obtain ⟨combined, dependencies, resultChecking, node, evaluation⟩ := context_plug_node context child
  refine ⟨combined, dependencies, resultChecking, .checked ?_ ?_ node, evaluation⟩
  · simpa only [SourceAnnotatedCode.Context.plug_hint] using hint
  · exact SourceAnnotatedCode.Term.check_closed_iff.mpr
      ((position.plug_closed_iff code).mpr ⟨closed, child.resource_closed⟩)

end Ash.OneShot.SourceAnnotatedSources

#print axioms Ash.OneShot.SourceAnnotatedCode.Context.check_closed_iff
#print axioms Ash.OneShot.SourceAnnotatedCode.Context.plug_closed_iff
#print axioms Ash.OneShot.SourceAnnotatedCode.Focus.context_closed
#print axioms Ash.OneShot.SourceAnnotatedSources.context_plug_node
#print axioms Ash.OneShot.SourceAnnotatedSources.context_plug
