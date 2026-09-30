import SourceAnnotatedTransport

/-! Annotated values retain the existing pure source summaries and transport
rules. Only the finite checked wrapper is new; latent typing stays intact. -/
namespace Ash.OneShot.SourceAnnotatedSources
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Value Environment Operations Contract Contracts)

abbrev ValueSummary operations policy contracts world environment allowed code value :=
  Expression operations policy contracts world allowed .none environment code value [] (.request [] []) .pure

theorem value_pure
    (source : Expression operations policy contracts world allowed scope environment code value demand requirements checking)
    (isValue : code.erase.IsValue) : Expression operations policy contracts world allowed scope environment code value [] (.request [] []) .pure := by
  induction source using Expression.rec
    (motive_2 := fun contracts world allowed scope environment code value demand requirements _ checking _ =>
      code.erase.IsValue → Node operations policy contracts world allowed scope environment code value [] (.request [] []) .pure)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ _ _ _ _ _ => True) with
  | checked hint closed node ih => exact .checked hint closed (ih isValue)
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | lambda body outward formed latentBound ih => exact .lambda body outward formed latentBound
  | purePair left right ihLeft ihRight | pair left right ihLeft ihRight =>
      rename_i isValue
      exact .purePair (ihLeft isValue.1) (ihRight isValue.2)
  | «variable» | app | bind | branch | perform | handler | resume | discard | cleanup | resource => rename_i isValue; cases isValue
  | typed | unavailable | available | nil | cons => trivial

namespace Values

theorem change_context
    (source : Expression operations policy contracts world allowed scope environment code value demand requirements dependencies)
    (isValue : code.erase.IsValue) (nextAllowed : List Instance) (nextScope : Execution.Scope) :
    Expression operations policy contracts world nextAllowed nextScope environment code value demand requirements dependencies := by
  induction source using Expression.rec
      (motive_2 := fun contracts world allowed scope environment code value demand requirements _ checking _ =>
        code.erase.IsValue → Node operations policy contracts world nextAllowed nextScope environment code value demand requirements checking)
      (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_5 := fun _ _ _ _ _ _ _ _ _ _ _ => True) with
  | checked hint closed node ih => exact .checked hint closed (ih isValue)
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | lambda body outward formed latentBound ih => exact .lambda body outward formed latentBound
  | purePair left right ihLeft ihRight =>
      rename_i isValue
      exact .purePair (ihLeft isValue.1) (ihRight isValue.2)
  | pair left right ihLeft ihRight =>
      rename_i isValue
      exact .pair (ihLeft isValue.1) (ihRight isValue.2)
  | «variable» | app | bind | branch | perform | handler | resume | discard | cleanup | resource => rename_i isValue; cases isValue
  | typed | unavailable | available | nil | cons => trivial

/-- Normalize only a value's immediate checking nodes. Its latent function
annotations and the ordinary value type remain exactly the same. -/
theorem summary
    (source : Expression operations policy contracts world allowed scope environment code value demand requirements dependencies)
    (isValue : code.erase.IsValue) : ValueSummary operations policy contracts world environment allowed code value :=
  change_context (value_pure source isValue) isValue allowed .none

theorem change_allowed (source : ValueSummary operations policy contracts world environment allowed code value)
    (isValue : code.erase.IsValue) (next : List Instance) :
    ValueSummary operations policy contracts world environment next code value := change_context source isValue next .none

theorem closed_environment (source : ValueSummary operations policy contracts world environment allowed code value)
    (closed : ClosedValue code.erase) (destination : Environment) :
    ValueSummary operations policy contracts world destination allowed code value :=
  expression_environment_congr source (fun _ member => False.elim (ScopedTyping.closedValue_no_variable closed member))

theorem world_weaken (source : ValueSummary operations policy contracts world environment allowed code value)
    (larger : world ⊆ next) : ValueSummary operations policy contracts next environment allowed code value :=
  expression_world_weaken source larger

theorem extension (source : ValueSummary operations policy contracts world environment allowed code value)
    (grows : contracts.Extends next) : ValueSummary operations policy next world environment allowed code value :=
  expression_extension source grows

/-- Reuse the existing port and usage projections for substituted values. -/
theorem erase (source : ValueSummary operations policy contracts world environment allowed code value)
    (isValue : code.erase.IsValue) :
    SourceTemplates.ValueSummary operations.erase.erase policy contracts.erase.erase world environment.erase.erase allowed code.erase value.erase.erase :=
  SourcePlannedSources.Values.erase source.erase isValue

end Values

end Ash.OneShot.SourceAnnotatedSources
#print axioms Ash.OneShot.SourceAnnotatedSources.value_pure
#print axioms Ash.OneShot.SourceAnnotatedSources.Values.change_context
#print axioms Ash.OneShot.SourceAnnotatedSources.Values.summary
#print axioms Ash.OneShot.SourceAnnotatedSources.Values.change_allowed
#print axioms Ash.OneShot.SourceAnnotatedSources.Values.closed_environment
#print axioms Ash.OneShot.SourceAnnotatedSources.Values.world_weaken
#print axioms Ash.OneShot.SourceAnnotatedSources.Values.extension
#print axioms Ash.OneShot.SourceAnnotatedSources.Values.erase
