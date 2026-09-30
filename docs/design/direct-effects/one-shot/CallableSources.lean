import RecursiveOutwardCore

/-!
Callable source summaries parameterized by the body typing judgment. The
runtime syntax remains Code. A lambda retains a full body derivation and its
proved outward row; other rules retain the existing stable summary equations.
-/
namespace Ash.OneShot.CallableSources
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts
open RecursiveRequirements (Requirements)

abbrev BodyJudgment := List Nat → Environment → List Instance → Code → Value →
  (demand : List Nat) → Requirements demand → Prop

inductive Summary (operations : Operations) (Body : BodyJudgment) :
    List Nat → Environment → List Instance → Code → Value → Footprint → Prop where
  | summaryUnit : Summary operations Body world environment allowed .unit .unit []
  | summaryBoolean : Summary operations Body world environment allowed (.boolean value) .boolean []
  | summaryInteger : Summary operations Body world environment allowed (.integer value) .integer []
  | summaryReference (issued : identity ∈ world) :
      Summary operations Body world environment allowed (.resourceRef (.activation identity)) (.reference identity) []
  | summaryVariable (known : environment name = some value) (formed : ScopedPorts.InWorld world value.port) :
      Summary operations Body world environment allowed (.variable name) value []
  | summaryPair (left : Summary operations Body world environment allowed a first leftRow)
      (right : Summary operations Body world environment allowed b second rightRow) :
      Summary operations Body world environment allowed (.pair a b) (.pair first second) (leftRow ++ rightRow)
  | summaryLambda (body : Body world (environment.extend parameter input) latentRequests code output bodyDemand bodyRequirements)
      (outward : RecursiveOutward.Outward bodyRequirements (some latentRow))
      (formed : ScopedPorts.InWorld world (Value.function input output latentRequests latentRow).port) :
      Summary operations Body world environment allowed (.lambda parameter code) (.function input output latentRequests latentRow) []
  | summaryApp (function : Summary operations Body world environment allowed f (.function input output latentRequests latentRow) functionRow)
      (argument : Summary operations Body world environment allowed a input argumentRow) (admitted : latentRequests ⊆ allowed) :
      Summary operations Body world environment allowed (.app f a) output (functionRow ++ argumentRow ++ latentRow)
  | summaryBind (initializer : Summary operations Body world environment allowed a input initializerRow)
      (body : Summary operations Body world (environment.extend parameter input) allowed b output bodyRow) :
      Summary operations Body world environment allowed (.bind parameter a b) output (initializerRow ++ bodyRow)
  | summaryBranch (condition : Summary operations Body world environment allowed test .boolean conditionRow)
      (yes : Summary operations Body world environment allowed a output yesRow)
      (no : Summary operations Body world environment allowed b output noRow) :
      Summary operations Body world environment allowed (.branch test a b) output (conditionRow ++ yesRow ++ noRow)
  | summaryPerform (known : operations effect operation = some (input, output)) (admitted : effect ∈ allowed)
      (operand : Summary operations Body world environment allowed value input operandRow) (formed : ScopedPorts.InWorld world output.port) :
      Summary operations Body world environment allowed (.perform (Instantiation.freezeEffect effect) operation value) output
        (operandRow ++ [⟨effect, operation, false⟩])
  | summaryCleanup (callback : Summary operations Body world environment allowed action (.function .unit .unit latentRequests latentRow) callbackRow)
      (body : Summary operations Body world environment allowed code output bodyRow) (admitted : latentRequests ⊆ allowed) :
      Summary operations Body world environment allowed (.cleanup action code) output (callbackRow ++ bodyRow ++ qualify true latentRow)
  | summaryResource {bodyRow : Nat → Footprint}
      (initializer : Summary operations Body world environment allowed initial .integer initialRow)
      (body : ∀ identity, identity ∉ world →
        Summary operations Body (world ++ [identity]) environment (.cell identity :: residual)
          (code.instantiate (Instantiation.Environment.empty.bind binder identity)) output (bodyRow identity))
      (formed : ScopedPorts.InWorld world output.port)
      (effectsBound : residual.flatMap Instance.resources ⊆ world) (admitted : residual ⊆ allowed)
      (outward : ∀ identity, identity ∉ world → CallableProtection.outsideCell identity (bodyRow identity) = row) :
      Summary operations Body world environment allowed (.resource binder initial code) output (initialRow ++ row)


theorem from_legacy
    (source : CoherentSourceTypes.Summary operations world environment allowed code value row)
    (embed : ∀ world environment allowed code value row,
      CoherentSourceTypes.Summary operations world environment allowed code value row →
        Body world environment allowed code value [] (.request [] row)) :
    Summary operations Body world environment allowed code value row := by
  induction source with
  | unit => exact .summaryUnit
  | boolean => exact .summaryBoolean
  | integer => exact .summaryInteger
  | reference issued => exact .summaryReference issued
  | «variable» known formed => exact .summaryVariable known formed
  | pair left right ihLeft ihRight => exact .summaryPair ihLeft ihRight
  | lambda body formed ih => exact .summaryLambda (embed _ _ _ _ _ _ body) (.request (layers := [])) formed
  | app function argument admitted ihFunction ihArgument => exact .summaryApp ihFunction ihArgument admitted
  | bind initializer body ihInit ihBody => exact .summaryBind ihInit ihBody
  | branch condition yes no ihCondition ihYes ihNo => exact .summaryBranch ihCondition ihYes ihNo
  | perform known admitted operand formed ih => exact .summaryPerform known admitted ih formed
  | cleanup callback body admitted ihCallback ihBody => exact .summaryCleanup ihCallback ihBody admitted
  | resource initializer body formed effectsBound admitted outward ihInit ihBody =>
      exact .summaryResource ihInit ihBody formed effectsBound admitted outward

theorem value_row (source : Summary operations Body world environment allowed code value row)
    (isValue : code.IsValue) : row = [] := by
  induction source with
  | summaryUnit | summaryBoolean | summaryInteger | summaryReference | summaryLambda => rfl
  | summaryVariable => cases isValue
  | summaryPair left right ihLeft ihRight => simp only [ihLeft isValue.1, ihRight isValue.2, List.nil_append]
  | summaryApp | summaryBind | summaryBranch | summaryPerform | summaryCleanup | summaryResource => cases isValue

theorem port_typing (source : Summary operations Body world environment allowed code value row)
    (bodyPorts : ∀ world environment allowed code value demand requirements,
      Body world environment allowed code value demand requirements →
        ScopedPorts.Typed operations.ports world environment.ports .none allowed code value.port)
    (ticket : ScopedPorts.Ticket) :
    ScopedPorts.Typed operations.ports world environment.ports ticket allowed code value.port := by
  induction source generalizing ticket with
  | summaryUnit => exact .unit
  | summaryBoolean => exact .boolean
  | summaryInteger => exact .integer
  | summaryReference issued => exact .reference issued
  | summaryVariable known formed => exact .variable (by simp [Environment.ports, known]) formed
  | summaryPair left right ihLeft ihRight => exact .pair (ihLeft ticket) (ihRight ticket)
  | summaryLambda body outward formed => exact .lambda (by simpa only [ports_extend] using bodyPorts _ _ _ _ _ _ _ body) formed
  | summaryApp function argument admitted ihFunction ihArgument => exact .app (ihFunction ticket) (ihArgument ticket) admitted
  | summaryBind initializer body ihInit ihBody => exact .bind (ihInit ticket) (by simpa only [ports_extend] using ihBody ticket)
  | summaryBranch condition yes no ihCondition ihYes ihNo => exact .branch (ihCondition ticket) (ihYes ticket) (ihNo ticket)
  | summaryPerform known admitted operand formed ih => exact .perform (port_lookup known) admitted (ih ticket) formed
  | summaryCleanup callback body admitted ihCallback ihBody => exact .cleanup (ihCallback ticket) (ihBody ticket) admitted
  | summaryResource initializer body formed effectsBound admitted outward ihInit ihBody =>
      exact .resource (ihInit ticket) (fun identity fresh => ihBody identity fresh ticket) formed effectsBound admitted

theorem summary_world_weaken (source : Summary operations Body world environment allowed code value row)
    (bodyWeaken : ∀ world next environment allowed code value demand requirements,
      Body world environment allowed code value demand requirements → world ⊆ next →
        Body next environment allowed code value demand requirements)
    (larger : world ⊆ next) : Summary operations Body next environment allowed code value row := by
  induction source generalizing next with
  | summaryUnit => exact .summaryUnit
  | summaryBoolean => exact .summaryBoolean
  | summaryInteger => exact .summaryInteger
  | summaryReference issued => exact .summaryReference (larger issued)
  | summaryVariable known formed => exact .summaryVariable known (ScopedPorts.in_world_mono formed larger)
  | summaryPair left right ihLeft ihRight => exact .summaryPair (ihLeft larger) (ihRight larger)
  | summaryLambda body outward formed => exact .summaryLambda (bodyWeaken _ _ _ _ _ _ _ _ body larger) outward (ScopedPorts.in_world_mono formed larger)
  | summaryApp function argument admitted ihFunction ihArgument => exact .summaryApp (ihFunction larger) (ihArgument larger) admitted
  | summaryBind initializer body ihInit ihBody => exact .summaryBind (ihInit larger) (ihBody larger)
  | summaryBranch condition yes no ihCondition ihYes ihNo => exact .summaryBranch (ihCondition larger) (ihYes larger) (ihNo larger)
  | summaryPerform known admitted operand formed ih => exact .summaryPerform known admitted (ih larger) (ScopedPorts.in_world_mono formed larger)
  | summaryCleanup callback body admitted ihCallback ihBody => exact .summaryCleanup (ihCallback larger) (ihBody larger) admitted
  | summaryResource initializer body formed effectsBound admitted outward ihInit ihBody =>
      exact .summaryResource (ihInit larger)
        (fun identity fresh => ihBody identity (fun member => fresh (larger member))
          (ScopedExpressions.append_subset larger (List.Subset.refl _)))
        (ScopedPorts.in_world_mono formed larger) (effectsBound.trans larger) admitted
        (fun identity fresh => outward identity (fun member => fresh (larger member)))

theorem value_allowed (source : Summary operations Body world environment allowed code value row)
    (isValue : code.IsValue) (next : List Instance) : Summary operations Body world environment next code value row := by
  induction source with
  | summaryUnit => exact .summaryUnit
  | summaryBoolean => exact .summaryBoolean
  | summaryInteger => exact .summaryInteger
  | summaryReference issued => exact .summaryReference issued
  | summaryVariable => cases isValue
  | summaryPair left right ihLeft ihRight => exact .summaryPair (ihLeft isValue.1) (ihRight isValue.2)
  | summaryLambda body outward formed => exact .summaryLambda body outward formed
  | summaryApp | summaryBind | summaryBranch | summaryPerform | summaryCleanup | summaryResource => cases isValue

theorem map_body (source : Summary operations Body world environment allowed code value row)
    (change : ∀ world environment allowed code value demand requirements,
      Body world environment allowed code value demand requirements →
        Next world environment allowed code value demand requirements) :
    Summary operations Next world environment allowed code value row := by
  induction source with
  | summaryUnit => exact .summaryUnit
  | summaryBoolean => exact .summaryBoolean
  | summaryInteger => exact .summaryInteger
  | summaryReference issued => exact .summaryReference issued
  | summaryVariable known formed => exact .summaryVariable known formed
  | summaryPair left right ihLeft ihRight => exact .summaryPair ihLeft ihRight
  | summaryLambda body outward formed => exact .summaryLambda (change _ _ _ _ _ _ _ body) outward formed
  | summaryApp function argument admitted ihFunction ihArgument => exact .summaryApp ihFunction ihArgument admitted
  | summaryBind initializer body ihInit ihBody => exact .summaryBind ihInit ihBody
  | summaryBranch condition yes no ihCondition ihYes ihNo => exact .summaryBranch ihCondition ihYes ihNo
  | summaryPerform known admitted operand formed ih => exact .summaryPerform known admitted ih formed
  | summaryCleanup callback body admitted ihCallback ihBody => exact .summaryCleanup ihCallback ihBody admitted
  | summaryResource initializer body formed effectsBound admitted outward ihInit ihBody =>
      exact .summaryResource ihInit ihBody formed effectsBound admitted outward

theorem environment_congr (source : Summary operations Body world environment allowed code value row)
    (bodyCongr : ∀ world environment destination allowed code value demand requirements,
      Body world environment allowed code value demand requirements → AgreeOn environment destination code.dependencies →
        Body world destination allowed code value demand requirements)
    (agree : AgreeOn environment destination code.dependencies) :
    Summary operations Body world destination allowed code value row := by
  induction source generalizing destination with
  | summaryUnit => exact .summaryUnit
  | summaryBoolean => exact .summaryBoolean
  | summaryInteger => exact .summaryInteger
  | summaryReference issued => exact .summaryReference issued
  | summaryVariable known formed => exact .summaryVariable ((agree _ List.mem_cons_self).symm.trans known) formed
  | summaryPair left right ihLeft ihRight => exact .summaryPair (ihLeft (agree_left agree)) (ihRight (agree_right agree))
  | summaryLambda body outward formed => exact .summaryLambda (bodyCongr _ _ _ _ _ _ _ _ body (agree_extend agree)) outward formed
  | summaryApp function argument admitted ihFunction ihArgument =>
      exact .summaryApp (ihFunction (agree_left agree)) (ihArgument (agree_right agree)) admitted
  | summaryBind initializer body ihInit ihBody => exact .summaryBind (ihInit (agree_left agree)) (ihBody (agree_extend (agree_right agree)))
  | summaryBranch condition yes no ihCondition ihYes ihNo =>
      exact .summaryBranch (ihCondition (agree_left (agree_left agree))) (ihYes (agree_right (agree_left agree))) (ihNo (agree_right agree))
  | summaryPerform known admitted operand formed ih => exact .summaryPerform known admitted (ih (agree_right agree)) formed
  | summaryCleanup callback body admitted ihCallback ihBody =>
      exact .summaryCleanup (ihCallback (agree_left agree)) (ihBody (agree_right agree)) admitted
  | summaryResource initializer body formed effectsBound admitted outward ihInit ihBody =>
      apply Summary.summaryResource (ihInit (agree_left agree)) _ formed effectsBound admitted outward
      intro identity fresh
      apply ihBody identity fresh
      intro name member
      rcases List.mem_append.mp (ScopedExpressions.acquisition_dependency_bound _ identity _ member) with original | introduced
      · exact agree_right agree name original
      · simp at introduced

theorem allowed_mono (source : Summary operations Body world environment allowed code value row)
    (more : allowed ⊆ destination) : Summary operations Body world environment destination code value row := by
  induction source generalizing destination with
  | summaryUnit => exact .summaryUnit
  | summaryBoolean => exact .summaryBoolean
  | summaryInteger => exact .summaryInteger
  | summaryReference issued => exact .summaryReference issued
  | summaryVariable known formed => exact .summaryVariable known formed
  | summaryPair left right ihLeft ihRight => exact .summaryPair (ihLeft more) (ihRight more)
  | summaryLambda body outward formed => exact .summaryLambda body outward formed
  | summaryApp function argument admitted ihFunction ihArgument => exact .summaryApp (ihFunction more) (ihArgument more) (admitted.trans more)
  | summaryBind initializer body ihInit ihBody => exact .summaryBind (ihInit more) (ihBody more)
  | summaryBranch condition yes no ihCondition ihYes ihNo => exact .summaryBranch (ihCondition more) (ihYes more) (ihNo more)
  | summaryPerform known admitted operand formed ih => exact .summaryPerform known (more admitted) (ih more) formed
  | summaryCleanup callback body admitted ihCallback ihBody => exact .summaryCleanup (ihCallback more) (ihBody more) (admitted.trans more)
  | summaryResource initializer body formed effectsBound admitted outward ihInit ihBody =>
      exact .summaryResource (ihInit more) body formed effectsBound (admitted.trans more) outward

end Ash.OneShot.CallableSources
#print axioms Ash.OneShot.CallableSources.from_legacy
#print axioms Ash.OneShot.CallableSources.value_row
#print axioms Ash.OneShot.CallableSources.port_typing

#print axioms Ash.OneShot.CallableSources.summary_world_weaken
#print axioms Ash.OneShot.CallableSources.value_allowed
#print axioms Ash.OneShot.CallableSources.map_body

#print axioms Ash.OneShot.CallableSources.environment_congr

#print axioms Ash.OneShot.CallableSources.allowed_mono
