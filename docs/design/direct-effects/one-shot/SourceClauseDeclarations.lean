import SourceCallableSubstitution
import SourceCallableExamples

/-! The source-typing part of clause declarations uses the existing Expression
    judgment. A body is typed parametrically over a fresh captured contract with
    the declared full value and effect types. This does not certify advertised
    footprint bounds or establish preserved declaration admission. -/
namespace Ash.OneShot.SourceClauseDeclarations
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts
open RecursiveRequirements (Requirements)
open SourceTemplates (Expression)

/-- Capture-specific demands and rows remain abstract. The balance premise is
    supplied by the existing capture/closing ownership theorem. -/
def Body (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Owners.Contracts)
    (world : List Nat) (environment : Environment) (allowed : List Instance)
    (parameter binder : Nat) (argument input answer : Value)
    (resumeEffects closeEffects : List Instance) (held : Bool) (code : Code) : Prop :=
  ∀ owner (contract : Owners.Contract), contracts owner = none →
    contract.input = input → contract.answer = answer →
    contract.resumeEffects = resumeEffects → contract.closeEffects = closeEffects →
    contract.held = held → contract.closeDemand.Perm contract.resumeDemand →
    ∃ demand, ∃ requirements : Requirements demand,
      Expression operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
        (environment.extend parameter argument) code answer demand requirements

/-- An available table entry must have its source family. The row itself is
    still an annotation here; this judgment proves no effect bound for it. -/
inductive SourceOffer (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Owners.Contracts)
    (world : List Nat) (environment : Environment) (allowed : List Instance)
    (parameter binder : Nat) (argument input answer : Value)
    (resumeEffects closeEffects : List Instance) (code : Code) : Bool → Option Footprint → Prop where
  | unavailable : SourceOffer operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held none
  | available (source : Body operations policy contracts world environment allowed parameter binder argument input answer
        resumeEffects closeEffects held code) :
      SourceOffer operations policy contracts world environment allowed parameter binder argument input answer
        resumeEffects closeEffects code held (some row)

inductive SourceClauses (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Owners.Contracts)
    (world : List Nat) (environment : Environment) (allowed : List Instance)
    (requested : Instance) (answer : Value) : Clauses → List (Nat × ClauseContract) → Prop where
  | nil : SourceClauses operations policy contracts world environment allowed requested answer .nil []
  | cons (known : operations requested operation = some (argument, input))
      (ordinary : SourceOffer operations policy contracts world environment allowed parameter binder argument input answer
        resumeEffects closeEffects body false ordinaryRow)
      (protectedMode : SourceOffer operations policy contracts world environment allowed parameter binder argument input answer
        resumeEffects closeEffects body true protectedRow)
      (rest : SourceClauses operations policy contracts world environment allowed requested answer clauses table) :
      SourceClauses operations policy contracts world environment allowed requested answer
        (.cons operation parameter binder body clauses)
        ((operation, ⟨dispose, ordinaryRow, protectedRow⟩) :: table)

theorem offered_source
    (offered : SourceOffer operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held (some row)) :
    Body operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects held code := by
  cases offered with
  | available source => exact source

/-- Follow the existing exact clause selection; do not search another table
    entry when the selected operation or mode has no source witness. -/
theorem selected_family
    (source : SourceClauses operations policy contracts world environment allowed requested answer clauses table)
    (selected : ClauseAt operation clauses parameter binder code)
    (found : ProtectionContracts.lookup operation table = some offered)
    (available : offered.row held = some row) :
    ∃ argument input resumeEffects closeEffects,
      operations requested operation = some (argument, input) ∧
      Body operations policy contracts world environment allowed parameter binder argument input answer
        resumeEffects closeEffects held code := by
  induction selected generalizing table with
  | hit => cases source with
    | cons known ordinary protectedMode rest =>
        simp only [ProtectionContracts.lookup, if_true] at found
        cases Option.some.inj found
        cases held with
        | false =>
            simp [ClauseContract.row] at available
            exact ⟨_, _, _, _, known, offered_source (available ▸ ordinary)⟩
        | true =>
            simp [ClauseContract.row] at available
            exact ⟨_, _, _, _, known, offered_source (available ▸ protectedMode)⟩
  | pass different next ih => cases source with
    | cons known ordinary protectedMode rest =>
        exact ih rest (by simpa only [ProtectionContracts.lookup, if_neg different] using found)

theorem instantiate
    (source : Body operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects held code)
    (fresh : contracts owner = none)
    (inputSame : contract.input = input) (answerSame : contract.answer = answer)
    (resumeSame : contract.resumeEffects = resumeEffects) (closeSame : contract.closeEffects = closeEffects)
    (heldSame : contract.held = held) (balance : contract.closeDemand.Perm contract.resumeDemand) :
    ∃ demand, ∃ requirements : Requirements demand,
      Expression operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
        (environment.extend parameter argument) code contract.answer demand requirements := by
  obtain ⟨demand, requirements, body⟩ := source owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
  exact ⟨demand, requirements, answerSame.symm ▸ body⟩

/-- Payload binding uses the already established shared closed substitution
    theorem, including function values whose bodies contain handlers. -/
theorem instantiate_payload
    (source : Body operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects held code)
    (fresh : contracts owner = none)
    (inputSame : contract.input = input) (answerSame : contract.answer = answer)
    (resumeSame : contract.resumeEffects = resumeEffects) (closeSame : contract.closeEffects = closeEffects)
    (heldSame : contract.held = held) (balance : contract.closeDemand.Perm contract.resumeDemand)
    (payload : SourceTemplates.ValueSummary operations policy contracts world environment allowed value argument)
    (closed : ClosedValue value) :
    ∃ demand, ∃ requirements : Requirements demand,
      Expression operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
        environment (code.subst parameter value) contract.answer demand requirements := by
  obtain ⟨demand, requirements, body⟩ := instantiate source fresh inputSame answerSame resumeSame closeSame heldSame balance
  exact ⟨demand, requirements, SourceCallableSubstitution.substitution body
    (payload.extension (Owners.insert_extends contracts fresh)) closed⟩

theorem Body.world_weaken
    (source : Body operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects held code) (larger : world ⊆ next) :
    Body operations policy contracts next environment allowed parameter binder argument input answer
      resumeEffects closeEffects held code := by
  intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
  obtain ⟨demand, requirements, typed⟩ := source owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
  exact ⟨demand, requirements, SourceTemplates.expression_world_weaken typed larger⟩

theorem extension_fresh {contracts next : Owners.Contracts}
    (extension : contracts.Extends next) (fresh : next owner = none) :
    contracts owner = none := by
  cases known : contracts owner with
  | none => rfl
  | some previous => have impossible := extension owner previous known; rw [fresh] at impossible; cases impossible

theorem insert_extension {contracts next : Owners.Contracts} (extension : contracts.Extends next) :
    (contracts.insert owner contract).Extends (next.insert owner contract) := by
  intro other previous known
  by_cases same : other = owner
  · simpa only [Owners.Contracts.insert, if_pos same] using known
  · simp only [Owners.Contracts.insert, if_neg same] at known ⊢
    exact extension other previous known

theorem Body.extension
    (source : Body operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects held code) (extension : contracts.Extends next) :
    Body operations policy next world environment allowed parameter binder argument input answer
      resumeEffects closeEffects held code := by
  intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
  have oldFresh := extension_fresh extension fresh
  have inserted := insert_extension (owner := owner) (contract := contract) extension
  obtain ⟨demand, requirements, typed⟩ := source owner contract oldFresh inputSame answerSame resumeSame closeSame heldSame balance
  exact ⟨demand, requirements, SourceTemplates.expression_extension typed inserted⟩

theorem SourceOffer.world_weaken
    (source : SourceOffer operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held row) (larger : world ⊆ next) :
    SourceOffer operations policy contracts next environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held row := by
  cases source with
  | unavailable => exact .unavailable
  | available body => exact .available (body.world_weaken larger)

theorem SourceOffer.extension
    (source : SourceOffer operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held row) (extension : contracts.Extends next) :
    SourceOffer operations policy next world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held row := by
  cases source with
  | unavailable => exact .unavailable
  | available body => exact .available (body.extension extension)

theorem SourceClauses.world_weaken
    (source : SourceClauses operations policy contracts world environment allowed requested answer clauses table)
    (larger : world ⊆ next) :
    SourceClauses operations policy contracts next environment allowed requested answer clauses table := by
  induction source with
  | nil => exact .nil
  | cons known ordinary protectedMode rest ih =>
      exact .cons known (ordinary.world_weaken larger) (protectedMode.world_weaken larger) ih

theorem SourceClauses.extension
    (source : SourceClauses operations policy contracts world environment allowed requested answer clauses table)
    (extension : contracts.Extends next) :
    SourceClauses operations policy next world environment allowed requested answer clauses table := by
  induction source with
  | nil => exact .nil
  | cons known ordinary protectedMode rest ih =>
      exact .cons known (ordinary.extension extension) (protectedMode.extension extension) ih

/-- Ordinary binding substitution respects the clause parameter's shadowing.
    The body proof reuses shared closed substitution after contract extension. -/
theorem Body.substitution
    (source : Body operations policy contracts world (environment.extend name valueType) allowed
      parameter binder argument input answer resumeEffects closeEffects held code)
    (replacement : SourceTemplates.ValueSummary operations policy contracts world environment allowed value valueType)
    (closed : ClosedValue value) :
    Body operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects held (if name = parameter then code else code.subst name value) := by
  intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
  obtain ⟨demand, requirements, typed⟩ := source owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
  by_cases same : name = parameter
  · subst parameter
    exact ⟨demand, requirements, by simpa only [if_true, Environment.extend_shadow] using typed⟩
  · rw [Environment.extend_commute environment name parameter valueType argument same] at typed
    have payload := SourceCallableTransport.closed_value_environment
      (replacement.extension (Owners.insert_extends (contract := contract) contracts fresh)) closed
      (environment.extend parameter argument)
    exact ⟨demand, requirements, by simpa only [if_neg same] using
      SourceCallableSubstitution.substitution typed payload closed⟩

theorem SourceOffer.substitution
    (source : SourceOffer operations policy contracts world (environment.extend name valueType) allowed
      parameter binder argument input answer resumeEffects closeEffects code held row)
    (replacement : SourceTemplates.ValueSummary operations policy contracts world environment allowed value valueType)
    (closed : ClosedValue value) :
    SourceOffer operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects (if name = parameter then code else code.subst name value) held row := by
  cases source with
  | unavailable => exact .unavailable
  | available body => exact .available (body.substitution replacement closed)

theorem SourceClauses.substitution
    (source : SourceClauses operations policy contracts world (environment.extend name valueType) allowed
      requested answer clauses table)
    (replacement : SourceTemplates.ValueSummary operations policy contracts world environment allowed value valueType)
    (closed : ClosedValue value) :
    SourceClauses operations policy contracts world environment allowed requested answer (clauses.subst name value) table := by
  induction source with
  | nil => exact .nil
  | cons known ordinary protectedMode rest ih =>
      exact .cons known (ordinary.substitution replacement closed) (protectedMode.substitution replacement closed) ih

theorem Body.environment_congr
    (source : Body operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects held code)
    (agree : AgreeOn environment destination (Syntax.without (.variable parameter) code.dependencies)) :
    Body operations policy contracts world destination allowed parameter binder argument input answer
      resumeEffects closeEffects held code := by
  intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
  obtain ⟨demand, requirements, typed⟩ := source owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
  exact ⟨demand, requirements, SourceCallableTransport.expression_environment_congr typed (agree_extend agree)⟩

theorem SourceOffer.environment_congr
    (source : SourceOffer operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held row)
    (agree : AgreeOn environment destination (Syntax.without (.variable parameter) code.dependencies)) :
    SourceOffer operations policy contracts world destination allowed parameter binder argument input answer
      resumeEffects closeEffects code held row := by
  cases source with
  | unavailable => exact .unavailable
  | available body => exact .available (body.environment_congr agree)

theorem SourceClauses.environment_congr
    (source : SourceClauses operations policy contracts world environment allowed requested answer clauses table)
    (agree : AgreeOn environment destination clauses.dependencies) :
    SourceClauses operations policy contracts world destination allowed requested answer clauses table := by
  induction source with
  | nil => exact .nil
  | cons known ordinary protectedMode rest ih =>
      have bodyAgree := fun name member => agree_left agree name
        (Syntax.mem_without.mpr ⟨member, by simp⟩)
      exact .cons known (ordinary.environment_congr bodyAgree)
        (protectedMode.environment_congr bodyAgree) (ih (agree_right agree))

namespace Examples
open SourceCallableExamples (operations policy contracts effect function functionType function_value_summary function_source)

def body : Code := .bind 5 (.resume 9 .unit) function

theorem body_family : Body operations policy contracts [] Environment.empty [] 2 9 .unit .unit functionType [] [] held body := by
  intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
  have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
  have operand : Expression operations policy (contracts.insert owner contract) [] [] (.ticket 9 owner)
      (Environment.empty.extend 2 .unit) .unit contract.input [] (.request [] []) := inputSame.symm ▸ .stable .unit
  have resumed := Expression.resume (binder := 9) known (by simp [Execution.Scope.resolve]) (by rfl) operand
    (resumeSame.symm ▸ List.Subset.refl [])
    (answerSame.symm ▸ (by simp [ScopedPorts.InWorld, functionType, Value.port, ScopedPorts.Port.resources]))
  have value := function_value_summary.extension (Owners.insert_extends (contract := contract) contracts fresh)
  have closed := ScopedPorts.typed_value_closed (SourceTemplates.expression_ports function_source .none) trivial
  have returned := SourceCallableTransport.closed_value_environment value closed
    ((Environment.empty.extend 2 .unit).extend 5 contract.answer)
  exact ⟨_, _, Expression.bind resumed (returned.expression _)⟩

def clauses : Clauses := .cons 0 2 9 body .nil
def table : List (Nat × ClauseContract) := [(0, ⟨false, some [], some []⟩)]

theorem source_declaration : SourceClauses operations policy contracts [] Environment.empty [] effect functionType clauses table :=
  .cons SourceCallableExamples.operation_known (.available body_family) (.available body_family) .nil

theorem selected_full_body : ∃ argument input resumeEffects closeEffects,
    operations effect 0 = some (argument, input) ∧
    Body operations policy contracts [] Environment.empty [] 2 9 argument input functionType resumeEffects closeEffects true body := by
  obtain ⟨argument, input, resumeEffects, closeEffects, known, source⟩ :=
    selected_family source_declaration (ClauseAt.hit) (by rfl) (held := true) (row := []) (by rfl)
  exact ⟨argument, input, resumeEffects, closeEffects, known, source⟩

/-- Full answer annotations cannot be replaced by port equality: the latent
    effect row remains part of the declared function result. -/
theorem port_equality_is_insufficient :
    functionType.port = (Value.function .unit .unit [] [⟨effect, 0, false⟩]).port ∧
    functionType ≠ Value.function .unit .unit [] [⟨effect, 0, false⟩] := by decide

end Examples
end Ash.OneShot.SourceClauseDeclarations
#print axioms Ash.OneShot.SourceClauseDeclarations.offered_source
#print axioms Ash.OneShot.SourceClauseDeclarations.selected_family
#print axioms Ash.OneShot.SourceClauseDeclarations.instantiate
#print axioms Ash.OneShot.SourceClauseDeclarations.instantiate_payload
#print axioms Ash.OneShot.SourceClauseDeclarations.Body.world_weaken
#print axioms Ash.OneShot.SourceClauseDeclarations.Body.extension
#print axioms Ash.OneShot.SourceClauseDeclarations.extension_fresh
#print axioms Ash.OneShot.SourceClauseDeclarations.insert_extension
#print axioms Ash.OneShot.SourceClauseDeclarations.SourceOffer.world_weaken
#print axioms Ash.OneShot.SourceClauseDeclarations.SourceOffer.extension
#print axioms Ash.OneShot.SourceClauseDeclarations.SourceClauses.world_weaken
#print axioms Ash.OneShot.SourceClauseDeclarations.SourceClauses.extension
#print axioms Ash.OneShot.SourceClauseDeclarations.Body.substitution
#print axioms Ash.OneShot.SourceClauseDeclarations.SourceOffer.substitution
#print axioms Ash.OneShot.SourceClauseDeclarations.SourceClauses.substitution
#print axioms Ash.OneShot.SourceClauseDeclarations.Body.environment_congr
#print axioms Ash.OneShot.SourceClauseDeclarations.SourceOffer.environment_congr
#print axioms Ash.OneShot.SourceClauseDeclarations.SourceClauses.environment_congr
#print axioms Ash.OneShot.SourceClauseDeclarations.Examples.body_family
#print axioms Ash.OneShot.SourceClauseDeclarations.Examples.source_declaration
#print axioms Ash.OneShot.SourceClauseDeclarations.Examples.selected_full_body
#print axioms Ash.OneShot.SourceClauseDeclarations.Examples.port_equality_is_insufficient
