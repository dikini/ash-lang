import DeclaredSourceEntries
import TemplateSubstitution

/-! Reuse structural stored-result admission with hereditary source states.
The finite template check supplies a resource's return bound; the established
return invariant then supplies the release check for actual returned values.
No new support analysis or execution induction is introduced. -/
namespace Ash.OneShot.DeclaredReturnAdmission
open Syntax ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts
open DeclaredSourceStates (CheckedState)

theorem ports
    (source : CheckedState operations policy contracts tables world outside scope code stack output demand row) :
    ScopedPorts.ConfigurationTyped operations.ports contracts.ports.types world ⟨code, scope, stack⟩ output.port := by
  cases source with
  | checked current closing unique evaluated accepted =>
      exact SourceTemplates.configuration_ports (DeclaredSourceStates.configuration_erase current)

/-- Unknown upper support imposes no constraint. A finite upper bound checks
actual captured resources, independently of the value's function result type. -/
def checkBinding (environment : ResultSummaries.Environment) (name : Nat) (value : Code) : Bool :=
  match (environment name).support with
  | none => true
  | some resources => decide (resourceDependencies value.dependencies ⊆ resources)

theorem check_binding_iff (closed : ScopedExpressions.ClosedValue value) :
    checkBinding environment name value = true ↔
      ReturnSupport.Below (ResultSummaries.analyze environment value) (environment name) := by
  unfold checkBinding ReturnSupport.Below
  rw [ResultSummaries.closed_value_storage_sound closed]
  cases known : (environment name).support with
  | none => simp
  | some resources => simp

/-- One source substitution preserves both the hereditary derivation and the
finite check on the resource body. Existing template substitution supplies the
support proof; no body execution or future-state condition is assumed. -/
theorem resource_substitution
    (source : DeclaredSources.Expression operations policy contracts world allowed scope
      (Environment.empty.extend name input) (.resource binder (.integer payload) body) output demand requirements)
    (scopeTyped : ScopedPorts.EffectScope contracts.ports scope ticket)
    (replacement : DeclaredSourceValues.ValueSummary operations policy contracts world Environment.empty allowed value input)
    (isValue : value.IsValue)
    (templateChecked : TemplateSupport.check environment world body = true)
    (bindingChecked : checkBinding environment name value = true) :
    DeclaredSources.Expression operations policy contracts world allowed scope Environment.empty
      (.resource binder (.integer payload) (body.subst name value)) output demand requirements ∧
    TemplateSupport.check environment world (body.subst name value) = true := by
  have closed := ScopedPorts.typed_value_closed ((DeclaredSourceValues.erase replacement).ports .none) isValue
  have resourceClosed := ScopedPorts.typed_resource_closed
    (SourceTemplates.expression_ports (DeclaredSources.expression_erase source) scopeTyped)
  have binding : TemplateSubstitution.BindingsChecked environment [(name, value)] :=
    .cons closed ((check_binding_iff closed).mp bindingChecked) .nil
  exact ⟨DeclaredSourceSubstitution.substitution source replacement closed,
    TemplateSubstitution.checked_replacements_preserve_check templateChecked resourceClosed binding⟩

/-- A strict source bind reaches the substituted resource with its original
support check preserved. Closedness and suffix readiness come from source port
typing, and ordinary return preservation reuses the established raw-step proof. -/
theorem bind_resource
    (source : CheckedState operations policy contracts tables world outside scope
      (.bind name value (.resource binder (.integer payload) body)) stack output demand row)
    (isValue : value.IsValue)
    (templateChecked : TemplateSupport.check environment world body = true)
    (bindingChecked : checkBinding environment name value = true)
    (returns : ReturnBoundaries.ConfigurationChecked environment
      ⟨.bind name value (.resource binder (.integer payload) body), scope, stack⟩) :
    RawStep ⟨.bind name value (.resource binder (.integer payload) body), scope, stack⟩
      ⟨.resource binder (.integer payload) (body.subst name value), scope, stack⟩ [] [] ∧
    CheckedState operations policy contracts tables world outside scope
      (.resource binder (.integer payload) (body.subst name value)) stack output demand row ∧
    TemplateSupport.check environment world (body.subst name value) = true ∧
    ReturnBoundaries.ConfigurationChecked environment
      ⟨.resource binder (.integer payload) (body.subst name value), scope, stack⟩ := by
  obtain ⟨input, current, pending⟩ := ports source
  cases current with
  | checked scopeKnown typed => cases typed with
    | bind initializer suffix =>
      have closed := ScopedPorts.typed_value_closed initializer isValue
      have resourceClosed := ScopedPorts.typed_resource_closed suffix
      have bindings : TemplateSubstitution.BindingsChecked environment [(name, value)] :=
        .cons closed ((check_binding_iff closed).mp bindingChecked) .nil
      have step := RawStep.bind name value (.resource binder (.integer payload) body) scope stack closed
        (ScopedPorts.typed_suffix_ready suffix)
      exact ⟨step, DeclaredSourceStates.bind_preserves source closed,
        TemplateSubstitution.checked_replacements_preserve_check templateChecked resourceClosed bindings,
        ReturnBoundaries.raw_step_preserves_checked step returns (.none (by simp))⟩

/-- Source entry chooses the same fresh identity for the hereditary state and
its return bound. The existing template checker is sufficient for higher-order
answers too; no first-order restriction is added. -/
theorem resource_entry
    (source : CheckedState operations policy contracts tables world outside scope
      (.resource binder initializer body) stack output demand row)
    (isValue : initializer.IsValue)
    (templateChecked : TemplateSupport.check environment world body = true)
    (returns : ReturnBoundaries.ConfigurationChecked environment ⟨.resource binder initializer body, scope, stack⟩) :
    ∃ identity payload answer,
      identity ∉ world ∧ initializer = .integer payload ∧
      RawStep ⟨.resource binder initializer body, scope, stack⟩
        ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
          .push (.cell identity payload scope answer) stack⟩ [.resource identity] [] ∧
      CheckedState operations policy contracts tables (world ++ [identity]) outside scope
        (body.instantiate (Instantiation.Environment.empty.bind binder identity))
        (.push (.cell identity payload scope answer) stack) output demand row ∧
      ReturnBoundaries.ConfigurationChecked environment
        ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
          .push (.cell identity payload scope answer) stack⟩ := by
  obtain ⟨identity, payload, answer, fresh, same, step, next, phases⟩ :=
    DeclaredSourceEntries.resource_preserves source isValue
  subst initializer
  have closed : (Code.resource binder (.integer payload) body).ResourceClosed := by
    cases source with
    | checked current closing unique evaluated accepted => cases current with
      | checked expression scopeTyped pending =>
          exact ScopedPorts.typed_resource_closed
            (SourceTemplates.expression_ports (DeclaredSources.expression_erase expression) scopeTyped)
  have allocation := TemplateSupport.source_entry_certificate (scope := scope) (answer := answer) (tail := stack)
    (TemplateSupport.check_iff_source_bound.mp templateChecked) closed fresh
  exact ⟨identity, payload, answer, fresh, rfl, step, next,
    ReturnBoundaries.raw_step_preserves_checked step returns allocation⟩

/-- For a current value, release admission follows from the retained support
invariant and existing source-to-port erasure. It is not a supplied safety
premise, and a function's latent effect row is not used as its stored support. -/
theorem value_access
    (source : CheckedState operations policy contracts tables world outside scope value stack output demand row)
    (isValue : value.IsValue)
    (returns : ReturnBoundaries.ConfigurationChecked environment ⟨value, scope, stack⟩) :
    AccessChecks ⟨value, scope, stack⟩ ambient :=
  ReturnBoundaries.value_access_checks (ports source) isValue returns

theorem leave_resource
    (source : CheckedState operations policy contracts tables world outside scope value
      (.push (.cell identity payload caller answer) tail) output demand row)
    (isValue : value.IsValue)
    (returns : ReturnBoundaries.ConfigurationChecked environment
      ⟨value, scope, .push (.cell identity payload caller answer) tail⟩) :
    identity ∉ resourceDependencies value.dependencies ∧
    AccessChecks ⟨value, scope, .push (.cell identity payload caller answer) tail⟩ ambient ∧
    RawStep ⟨value, scope, .push (.cell identity payload caller answer) tail⟩
      ⟨value, caller, tail⟩ [] [.resource identity] ∧
    CheckedState operations policy contracts tables world outside caller value tail output demand row ∧
    ReturnBoundaries.ConfigurationChecked environment ⟨value, caller, tail⟩ := by
  have closed := DeclaredSourceStates.value_closed source isValue
  have step := RawStep.leaveCell identity payload answer caller scope value closed tail
  exact ⟨ReturnBoundaries.typed_cell_return_excludes (ports source) closed returns,
    value_access source isValue returns, step, DeclaredSourceStates.leave_cell source isValue,
    ReturnBoundaries.raw_step_preserves_checked step returns (ReturnBoundaries.value_allocation_return step isValue)⟩

namespace Examples
open ResultSummaries.Examples (retainingConstant)
open ReturnBoundaries.Examples (retainingTemplate)
open TemplateSupport.Examples (unknownEnvironment)

def operations : Operations := fun _ _ => none
def policy : Syntax.TicketPolicy := fun _ => ⟨true, true⟩
def contracts : Owners.Contracts := fun _ => none
def tables : CallableProtectionFrames.Tables := fun _ => []
def functionType : Value := .function .unit .integer [] []
def retainedOuter : Code := .resource 4 (.integer 0) (retainingConstant 8)
def retainedOwn : Code := .resource 4 (.integer 0) retainingTemplate

theorem retaining_source (member : identity ∈ world) :
    Summary operations world environment allowed (retainingConstant identity) functionType [] :=
  .lambda (.bind (.reference member) (.integer))
    (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])

theorem outer_source : Summary operations [8] Environment.empty [] retainedOuter functionType [] := by
  refine .resource (bodyRow := fun _ => []) .integer ?_
    (by simp [functionType, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
    (List.nil_subset _) (List.Subset.refl []) (by intros; rfl)
  intro identity fresh
  exact retaining_source (List.mem_append_left _ List.mem_cons_self)

/-- The existing result port and effect row also admit the retaining template.
The independent support check is necessary even with hereditary source typing. -/
theorem own_source : Summary operations [] Environment.empty [] retainedOwn functionType [] := by
  refine .resource (bodyRow := fun _ => []) .integer ?_
    (by simp [functionType, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
    (List.nil_subset _) (List.Subset.refl []) (by intros; rfl)
  intro identity fresh
  exact retaining_source (world := [identity]) (environment := Environment.empty)
    (allowed := [.cell identity]) List.mem_cons_self

theorem checked_source (summary : Summary operations world Environment.empty [] code functionType []) :
    CheckedState operations policy contracts tables world [] .none code .nil functionType [] [] := by
  exact .checked (.checked (.stable summary) .none .nil) .nil (by decide)
    (RecursiveRequirements.evaluate_sound (by
      simp only [RecursiveRequirements.evaluate, RecursiveRequirements.evaluateFuel,
        RecursiveRequirements.Requirements.prepend]
      decide)) rfl

theorem support_distinction :
    CheckedState operations policy contracts tables [8] [] .none retainedOuter .nil functionType [] [] ∧
    CheckedState operations policy contracts tables [] [] .none retainedOwn .nil functionType [] [] ∧
    TemplateSupport.check unknownEnvironment [8] (retainingConstant 8) = true ∧
    TemplateSupport.check unknownEnvironment [] retainingTemplate = false :=
  ⟨checked_source outer_source, checked_source own_source,
    TemplateSupport.Examples.outer_capture_accepted, TemplateSupport.Examples.own_template_capture_rejected⟩

/-- Reuse the old retaining-outer closure and the same symbolic support check,
now with hereditary source at entry and after the actual inner release. The
available outer resource is represented by world [8]; this does not claim a
complete issuance ledger or ambient-access invariant for the whole run. -/
theorem outer_function_returns :
    ∃ identity answer,
      identity ∉ [8] ∧
      RawStep ⟨retainedOuter, .none, .nil⟩
        ⟨retainingConstant 8, .none, .push (.cell identity 0 .none answer) .nil⟩ [.resource identity] [] ∧
      RawStep ⟨retainingConstant 8, .none, .push (.cell identity 0 .none answer) .nil⟩
        ⟨retainingConstant 8, .none, .nil⟩ [] [.resource identity] ∧
      CheckedState operations policy contracts tables ([8] ++ [identity]) [] .none
        (retainingConstant 8) .nil functionType [] [] ∧
      ReturnBoundaries.ConfigurationChecked unknownEnvironment ⟨retainingConstant 8, .none, .nil⟩ ∧
      AccessChecks ⟨retainingConstant 8, .none, .push (.cell identity 0 .none answer) .nil⟩ [8] := by
  obtain ⟨identity, payload, answer, fresh, same, step, next, returns⟩ :=
    resource_entry (checked_source outer_source) trivial TemplateSupport.Examples.outer_capture_accepted (by trivial)
  have payloadZero : payload = 0 := by simpa using same.symm
  subst payload
  have opened : (retainingConstant 8).instantiate (Instantiation.Environment.empty.bind 4 identity) = retainingConstant 8 := rfl
  rw [opened] at step next returns
  obtain ⟨excluded, access, release, finished, finalReturns⟩ := leave_resource next (by trivial) returns (ambient := [8])
  exact ⟨identity, answer, fresh, step, release, finished, finalReturns, access⟩

/-- Existing source typing and an initially empty return stack do not imply
release safety after acquisition. The failed source template check above is a
necessary admission boundary, not merely an imprecise diagnostic. -/
theorem checked_source_return_gap :
    ∃ identity answer,
      CheckedState operations policy contracts tables [] [] .none retainedOwn .nil functionType [] [] ∧
      ReturnBoundaries.ConfigurationChecked unknownEnvironment ⟨retainedOwn, .none, .nil⟩ ∧
      RawStep ⟨retainedOwn, .none, .nil⟩
        ⟨retainingConstant identity, .none, .push (.cell identity 0 .none answer) .nil⟩ [.resource identity] [] ∧
      CheckedState operations policy contracts tables [identity] [] .none
        (retainingConstant identity) (.push (.cell identity 0 .none answer) .nil) functionType [] [] ∧
      ¬ AccessChecks ⟨retainingConstant identity, .none, .push (.cell identity 0 .none answer) .nil⟩ [] ∧
      ¬ ReturnBoundaries.ConfigurationChecked unknownEnvironment
        ⟨retainingConstant identity, .none, .push (.cell identity 0 .none answer) .nil⟩ := by
  have initial := checked_source own_source
  obtain ⟨identity, payload, answer, fresh, same, step, next, phases⟩ :=
    DeclaredSourceEntries.resource_preserves initial (by trivial)
  have payloadZero : payload = 0 := by simpa using same.symm
  subst payload
  have opened : retainingTemplate.instantiate (Instantiation.Environment.empty.bind 4 identity) = retainingConstant identity := rfl
  rw [opened] at step next
  have denied : ¬ AccessChecks ⟨retainingConstant identity, .none, .push (.cell identity 0 .none answer) .nil⟩ [] := by
    intro admitted
    have excluded := admitted.release identity 0 answer .none .none (retainingConstant identity) .nil rfl
      (DeclaredSourceStates.value_closed next (by trivial))
    exact excluded List.mem_cons_self
  exact ⟨identity, answer, initial, trivial, step, next, denied,
    fun returns => denied (value_access next (by trivial) returns)⟩

def aliasProgram : Code := .bind 3 (.resourceRef (.activation 8))
  (.resource 4 (.integer 0) TemplateSubstitution.Examples.aliasBody)

theorem alias_source : CheckedState operations policy contracts tables [8] [] .none aliasProgram .nil functionType [] [] := by
  apply checked_source
  apply Summary.bind (.reference List.mem_cons_self)
  refine Summary.resource (bodyRow := fun _ => []) .integer ?_
    (by simp [functionType, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
    (List.nil_subset _) (List.Subset.refl []) (by intros; rfl)
  intro identity fresh
  apply Summary.lambda
  · apply Summary.bind (initializerRow := []) (bodyRow := [])
    · apply Summary.variable (value := .reference 8)
      · simp [Environment.extend]
      · simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]
    · exact .integer
  · simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]

theorem finite_binding_checks :
    checkBinding TemplateSubstitution.Examples.outerEnvironment 3 (.resourceRef (.activation 8)) = true ∧
    checkBinding TemplateSubstitution.Examples.outerEnvironment 3 (retainingConstant 8) = true ∧
    checkBinding TemplateSubstitution.Examples.outerEnvironment 3 (retainingConstant 7) = false := by decide

/-- The earlier symbolic alias bound survives the actual bind, then supplies
source-preserving resource entry and release for the resulting closure. -/
theorem alias_returns :
    ∃ identity answer,
      identity ∉ [8] ∧
      RawStep ⟨aliasProgram, .none, .nil⟩ ⟨retainedOuter, .none, .nil⟩ [] [] ∧
      RawStep ⟨retainedOuter, .none, .nil⟩
        ⟨retainingConstant 8, .none, .push (.cell identity 0 .none answer) .nil⟩ [.resource identity] [] ∧
      RawStep ⟨retainingConstant 8, .none, .push (.cell identity 0 .none answer) .nil⟩
        ⟨retainingConstant 8, .none, .nil⟩ [] [.resource identity] ∧
      CheckedState operations policy contracts tables ([8] ++ [identity]) [] .none
        (retainingConstant 8) .nil functionType [] [] ∧
      AccessChecks ⟨retainingConstant 8, .none, .push (.cell identity 0 .none answer) .nil⟩ [8] := by
  obtain ⟨bindStep, next, preservedCheck, preservedReturns⟩ := bind_resource alias_source (by trivial)
    TemplateSubstitution.Examples.alias_template_checked finite_binding_checks.1 (by trivial)
  obtain ⟨identity, payload, answer, fresh, same, entryStep, openedSource, openedReturns⟩ :=
    resource_entry next (by trivial) preservedCheck preservedReturns
  have payloadZero : payload = 0 := by simpa using same.symm
  subst payload
  change CheckedState _ _ _ _ _ _ _ (retainingConstant 8) _ _ _ _ at openedSource
  change ReturnBoundaries.ConfigurationChecked _ ⟨retainingConstant 8, .none, _⟩ at openedReturns
  obtain ⟨excluded, access, releaseStep, finalSource, finalReturns⟩ :=
    leave_resource openedSource (by trivial) openedReturns (ambient := [8])
  exact ⟨identity, answer, fresh, bindStep, entryStep, releaseStep, finalSource, access⟩

end Examples

end Ash.OneShot.DeclaredReturnAdmission

#print axioms Ash.OneShot.DeclaredReturnAdmission.ports
#print axioms Ash.OneShot.DeclaredReturnAdmission.resource_entry
#print axioms Ash.OneShot.DeclaredReturnAdmission.value_access
#print axioms Ash.OneShot.DeclaredReturnAdmission.leave_resource

#print axioms Ash.OneShot.DeclaredReturnAdmission.Examples.retaining_source

#print axioms Ash.OneShot.DeclaredReturnAdmission.Examples.outer_source

#print axioms Ash.OneShot.DeclaredReturnAdmission.Examples.own_source

#print axioms Ash.OneShot.DeclaredReturnAdmission.Examples.checked_source

#print axioms Ash.OneShot.DeclaredReturnAdmission.Examples.support_distinction

#print axioms Ash.OneShot.DeclaredReturnAdmission.Examples.outer_function_returns

#print axioms Ash.OneShot.DeclaredReturnAdmission.Examples.checked_source_return_gap

#print axioms Ash.OneShot.DeclaredReturnAdmission.check_binding_iff
#print axioms Ash.OneShot.DeclaredReturnAdmission.resource_substitution
#print axioms Ash.OneShot.DeclaredReturnAdmission.bind_resource

#print axioms Ash.OneShot.DeclaredReturnAdmission.Examples.alias_source
#print axioms Ash.OneShot.DeclaredReturnAdmission.Examples.finite_binding_checks
#print axioms Ash.OneShot.DeclaredReturnAdmission.Examples.alias_returns
