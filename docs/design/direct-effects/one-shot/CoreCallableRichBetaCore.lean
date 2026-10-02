import CoreCallableRichBetaPreservation
import CoreCallableComposedRuntimeCalls

namespace Ash.OneShot.CoreCallableRichBetaCore
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreSyntax CoreMachine
open CoreCallableGeneratedChronology
open CoreCallableContractAdmission (Globals SubstitutionPolicyStable)
open CoreCallableContractExecution (Site BetaPreserved)
open SourceDependencyChecks.Lexical (ReturnHints)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy)

section
variable [evidence : DeclarationPolicy]

/-- A relation to a CURRENT rich Site. Its producer is a separate obligation;
this is not static metadata for an initial or future endpoint. -/
structure Current {graph : Graph} (endpoint : Endpoint graph)
    (site : Site globals outward world allowed actions phases budget ambient installations
      expression runtimeScope stack result final context root) : Prop where
  machine : endpoint.point.machine = .eval ⟨expression,runtimeScope,stack⟩

/-- The existing beta input computes the current target configuration. -/
theorem beta_current {graph : Graph} {endpoint : Endpoint graph}
    (input : BetaInput endpoint)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.app (.lambda input.parameter input.bodyCode) input.argument) input.scope endpoint.lexical
      output final context root) : Current endpoint site := by
  refine ⟨?_⟩
  simp only [Endpoint.point,input.focus,CoreCleanupRunFrames.attach,Stack.append]

/-- Rich preservation and actual Core execution share one indexed beta input.
Full captured callee data stays in input; the pending caller stays in Site. -/
theorem beta_preserves {graph : Graph} {endpoint : Endpoint graph}
    (stable : SubstitutionPolicyStable (evidence := evidence) outward)
    (input : BetaInput endpoint)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.app (.lambda input.parameter input.bodyCode) input.argument) input.scope endpoint.lexical
      output final context root) :
    ∃ preserved : BetaPreserved site,
      Current (beta_result input).after preserved.next ∧
      CoreMachine.next graph endpoint.state = .stepped (beta_result input).after.state ∧
      Matching graph endpoint (beta_result input).after [] [] ∧
      RawStep ⟨.app (.lambda input.parameter input.bodyCode) input.argument,input.scope,endpoint.lexical⟩
        ⟨input.bodyCode.subst input.parameter input.argument,.none,endpoint.lexical⟩ [] [] := by
  obtain ⟨⟨preserved⟩,raw⟩ := site.beta stable input.operand.closed input.function.closed
  refine ⟨preserved,⟨?_⟩,(Operation.actual (.beta input)).1,(Operation.actual (.beta input)).2,raw⟩
  rfl

omit evidence in
/-- Actual beta enters the captured definition environment with the parameter,
while Site preserves the caller's pending stack and full result contract. -/
theorem beta_callee {graph : Graph} {endpoint : Endpoint graph} (input : BetaInput endpoint) :
    (beta_result input).after.state.control =
      .evaluate input.body (.binding input.parameter input.value input.environment) ∧
    (beta_result input).after.lexical = endpoint.lexical ∧
    (beta_result input).after.history = endpoint.history := ⟨rfl,rfl,rfl⟩

end

namespace OriginalAuthority
open CoreCallableComposedRuntimeCalls.Original ComposedResourceRuntimeOriginProbes
open CoreCallableComposedResourceOrigins CoreCallableComposedResourceOrigins.Probes

/-- This is the existing executed original joint receipt, not a new rich Site.
It retains both private constructor families and the exact lower domain. -/
abbrev Checked := @CheckedCall

theorem retained_domain {resource : Opened} (path : HigherPath resource) :
    path.stored.value 0 =
      .function [] (.function [0,0] (.storage []) (.storage [])) (.storage []) :=
  retained_lower_domain path

/-- The full higher-order argument domain cannot be replaced by scalar storage. -/
theorem retained_domain_not_scalar {resource : Opened} (path : HigherPath resource) :
    path.stored.value 0 ≠ .function [] (.storage []) (.storage []) := by
  rw [retained_domain path]
  intro same
  cases same

/-- The original receipt computes actual beta endpoints, independently of the
still missing CURRENT rich source/domain/private-family provider. -/
theorem endpoints {resource : Opened} {staticReader : ReaderPath resource}
    {readerReceipt : CoreCallableComposedResourceOrigins.Current staticReader.path selection.s8.nextActivation (by simp)}
    {handleReceipt : CoreCallableComposedCapturedHandle.CapturedHandle staticReader.path selection.s8.nextActivation (by simp)}
    {staticHigher : HigherPath resource}
    {higherReceipt : CoreCallableComposedResourceOrigins.Current staticHigher.path selection.s8.nextActivation (by simp)}
    (checked : CheckedCall staticReader readerReceipt handleReceipt staticHigher higherReceipt) :
    CoreMachine.next G e20.state = .stepped e21.state ∧
      CoreMachine.next G e25.state = .stepped e26.state :=
  checked_call_actual checked

end OriginalAuthority

#print axioms Current
#print axioms beta_current
#print axioms beta_preserves
#print axioms beta_callee
#print axioms OriginalAuthority.retained_domain
#print axioms OriginalAuthority.retained_domain_not_scalar
#print axioms OriginalAuthority.endpoints
end Ash.OneShot.CoreCallableRichBetaCore
