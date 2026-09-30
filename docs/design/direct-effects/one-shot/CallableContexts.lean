import CallableSources

/-! Ordinary context decomposition retaining full callable body evidence. -/
namespace Ash.OneShot.CallableContexts
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts

inductive ContextSummary (operations : Operations) (Body : CallableSources.BodyJudgment) (world : List Nat) (environment : Environment) (allowed : List Instance) :
    ScopedExecution.Context → Value → Value → Footprint → Prop where
  | pairLeft (right : CallableSources.Summary operations Body world environment allowed code output row) :
      ContextSummary operations Body world environment allowed (.pairLeft code) input (.pair input output) row
  | pairRight (left : CallableSources.Summary operations Body world environment allowed code input []) :
      ContextSummary operations Body world environment allowed (.pairRight code) output (.pair input output) []
  | appFunction (argument : CallableSources.Summary operations Body world environment allowed code input row) (admitted : requests ⊆ allowed) :
      ContextSummary operations Body world environment allowed (.appFunction code) (.function input output requests latent) output (row ++ latent)
  | appArgument (function : CallableSources.Summary operations Body world environment allowed code (.function input output requests latent) [])
      (admitted : requests ⊆ allowed) :
      ContextSummary operations Body world environment allowed (.appArgument code) input output latent
  | bind (body : CallableSources.Summary operations Body world (environment.extend parameter input) allowed code output row) :
      ContextSummary operations Body world environment allowed (.bind parameter code) input output row
  | branch (yes : CallableSources.Summary operations Body world environment allowed a output yesRow)
      (no : CallableSources.Summary operations Body world environment allowed b output noRow) :
      ContextSummary operations Body world environment allowed (.branch a b) .boolean output (yesRow ++ noRow)
  | perform (known : operations effect operation = some (input, output)) (admitted : effect ∈ allowed)
      (formed : ScopedPorts.InWorld world output.port) :
      ContextSummary operations Body world environment allowed (.perform (Instantiation.freezeEffect effect) operation) input output [⟨effect, operation, false⟩]
  | cleanup (body : CallableSources.Summary operations Body world environment allowed code output row) (admitted : requests ⊆ allowed) :
      ContextSummary operations Body world environment allowed (.cleanup code) (.function .unit .unit requests latent) output (row ++ qualify true latent)
  | resource {bodyRow : Nat → Footprint}
      (body : ∀ identity, identity ∉ world → CallableSources.Summary operations Body (world ++ [identity]) environment (.cell identity :: residual)
        (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output (bodyRow identity))
      (formed : ScopedPorts.InWorld world output.port)
      (effectsBound : residual.flatMap Instance.resources ⊆ world) (admitted : residual ⊆ allowed)
      (outward : ∀ identity, identity ∉ world → CallableProtection.outsideCell identity (bodyRow identity) = row) :
      ContextSummary operations Body world environment allowed (.resource binder code) .integer output row

theorem focus_decompose (focus : Focus whole child position)
    (source : CallableSources.Summary operations Body world environment allowed whole output row) :
    ∃ input childRow restRow, CallableSources.Summary operations Body world environment allowed child input childRow ∧
      ContextSummary operations Body world environment allowed position input output restRow ∧ row = childRow ++ restRow := by
  cases source with
  | summaryUnit | summaryBoolean | summaryInteger | summaryReference | summaryVariable | summaryLambda => cases focus
  | summaryPair left right => cases focus with
      | pairLeft => exact ⟨_, _, _, left, .pairLeft right, rfl⟩
      | pairRight isValue =>
          have empty := CallableSources.value_row left isValue
          subst_vars
          exact ⟨_, _, _, right, .pairRight left, by simp⟩
  | summaryApp function argument admitted => cases focus with
      | appFunction => exact ⟨_, _, _, function, .appFunction argument admitted, List.append_assoc ..⟩
      | appArgument isValue =>
          have empty := CallableSources.value_row function isValue
          subst_vars
          exact ⟨_, _, _, argument, .appArgument function admitted, by simp⟩
  | summaryBind initializer body => cases focus with
      | bind => exact ⟨_, _, _, initializer, .bind body, rfl⟩
  | summaryBranch condition yes no => cases focus with
      | branch => exact ⟨_, _, _, condition, .branch yes no, List.append_assoc ..⟩
  | summaryPerform known admitted operand formed => cases focus with
      | perform => exact ⟨_, _, _, operand, .perform known admitted formed, rfl⟩
  | summaryCleanup callback body admitted => cases focus with
      | cleanup => exact ⟨_, _, _, callback, .cleanup body admitted, List.append_assoc ..⟩
  | summaryResource initializer body formed effectsBound admitted outward => cases focus with
      | resource notValue => exact ⟨_, _, _, initializer, .resource body formed effectsBound admitted outward, rfl⟩

end Ash.OneShot.CallableContexts
#print axioms Ash.OneShot.CallableContexts.focus_decompose
