import DeclaredSourceTransport

/-! Value evidence reuses hereditary callable summaries with an empty outward
    row. The IsValue/ClosedValue premises remain separate, as in the existing
    shared source interface. No additional runtime value form is introduced. -/
namespace Ash.OneShot.DeclaredSourceValues
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts
open DeclaredSources (Expression Callable)
open RecursiveRequirements (Requirements)

abbrev ValueSummary operations policy contracts world environment allowed code value :=
  Callable operations policy contracts world environment allowed code value []

theorem from_legacy (source : Summary operations world environment allowed code value row) :
    Callable operations policy contracts world environment allowed code value row :=
  DeclaredSources.Callable.from_generic (CallableSources.from_legacy source (fun _ _ _ _ _ _ body => .stable body))

/-- A constructor projection, not an interpretation or cached effect row. -/
def bareRow : {demand : List Nat} → Requirements demand → Option Footprint
  | _, .request [] row => some row
  | _, _ => none

theorem prepend_not_empty_request (requirements : Requirements demand)
    (nonempty : prefixContext ≠ []) : bareRow (requirements.prepend prefixContext) = none := by
  cases requirements <;> try rfl
  case request nearer raw =>
    cases nearer <;> cases prefixContext <;> simp_all [bareRow, Requirements.prepend]

/-- A bare request certificate comes from the existing callable rules. A
    handler's nonempty interpretation prefix cannot disappear from this index. -/
theorem request_callable
    (source : Expression operations policy contracts world allowed scope environment code result demand requirements) :
    ∀ row, bareRow requirements = some row →
      Callable operations policy contracts world environment allowed code result row := by
  induction source using Expression.rec
      (motive_2 := fun _ _ _ _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_5 := fun _ _ _ _ _ _ _ _ _ => True)
  case stable summary => intro row same; cases Option.some.inj same; exact from_legacy summary
  case callable summary ih => intro row same; cases Option.some.inj same; exact summary
  case lambda body outward formed ih => intro row same; cases Option.some.inj same; exact .summaryLambda body outward formed
  case purePair left right ihLeft ihRight =>
    intro row same
    cases Option.some.inj same
    exact .summaryPair (ihLeft [] rfl) (ihRight [] rfl)
  case handler =>
    intro row same
    rw [prepend_not_empty_request _ (by simp)] at same
    cases same
  case pair => intro row same; cases same
  case app => intro row same; cases same
  case bind => intro row same; cases same
  case branch => intro row same; cases same
  case perform => intro row same; cases same
  case resume => intro row same; cases same
  case discard => intro row same; cases same
  case cleanup => intro row same; cases same
  case resource => intro row same; cases same
  case scopedResource => intro row same; cases same
  all_goals trivial

theorem value_summary
    (source : Expression operations policy contracts world allowed scope environment code result demand requirements)
    (isValue : code.IsValue) : ValueSummary operations policy contracts world environment allowed code result := by
  induction source using Expression.rec
      (motive_2 := fun _ _ _ _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_5 := fun _ _ _ _ _ _ _ _ _ => True)
  case stable summary => exact from_legacy (CoherentSourceTypes.value_row summary isValue ▸ summary)
  case callable summary ih =>
    have same := CallableSources.value_row summary.to_generic isValue
    rw [same] at summary
    exact summary
  case lambda body outward formed ih => exact .summaryLambda body outward formed
  case pair left right ihLeft ihRight => exact .summaryPair (ihLeft isValue.1) (ihRight isValue.2)
  case purePair left right ihLeft ihRight => exact .summaryPair (ihLeft isValue.1) (ihRight isValue.2)
  case app => cases isValue
  case bind => cases isValue
  case branch => cases isValue
  case perform => cases isValue
  case handler => cases isValue
  case resume => cases isValue
  case discard => cases isValue
  case cleanup => cases isValue
  case resource => cases isValue
  case scopedResource => cases isValue
  all_goals trivial

theorem expression (source : ValueSummary operations policy contracts world environment allowed code value)
    (scope : Execution.Scope) :
    Expression operations policy contracts world allowed scope environment code value [] (.request [] []) :=
  .callable source

theorem erase (source : ValueSummary operations policy contracts world environment allowed code value) :
    SourceTemplates.ValueSummary operations policy contracts world environment allowed code value :=
  .callable source.erase

theorem change_allowed (source : ValueSummary operations policy contracts world environment allowed code value)
    (isValue : code.IsValue) (next : List Instance) :
    ValueSummary operations policy contracts world environment next code value :=
  DeclaredSources.Callable.from_generic (CallableSources.value_allowed source.to_generic isValue next)

theorem closed_environment (source : ValueSummary operations policy contracts world environment allowed code value)
    (closed : ClosedValue code) (destination : Environment) :
    ValueSummary operations policy contracts world destination allowed code value :=
  DeclaredSourceTransport.callable_environment_congr source
    (fun _ member => False.elim (ScopedTyping.closedValue_no_variable closed member))

theorem world_weaken (source : ValueSummary operations policy contracts world environment allowed code value)
    (larger : world ⊆ next) : ValueSummary operations policy contracts next environment allowed code value :=
  DeclaredSourceTransport.callable_world_weaken source larger

theorem extension (source : ValueSummary operations policy contracts world environment allowed code value)
    (grows : contracts.Extends next) : ValueSummary operations policy next world environment allowed code value :=
  DeclaredSourceTransport.callable_extension source grows

end Ash.OneShot.DeclaredSourceValues
#print axioms Ash.OneShot.DeclaredSourceValues.from_legacy
#print axioms Ash.OneShot.DeclaredSourceValues.prepend_not_empty_request
#print axioms Ash.OneShot.DeclaredSourceValues.request_callable
#print axioms Ash.OneShot.DeclaredSourceValues.value_summary
#print axioms Ash.OneShot.DeclaredSourceValues.expression
#print axioms Ash.OneShot.DeclaredSourceValues.erase
#print axioms Ash.OneShot.DeclaredSourceValues.change_allowed
#print axioms Ash.OneShot.DeclaredSourceValues.closed_environment
#print axioms Ash.OneShot.DeclaredSourceValues.world_weaken
#print axioms Ash.OneShot.DeclaredSourceValues.extension
