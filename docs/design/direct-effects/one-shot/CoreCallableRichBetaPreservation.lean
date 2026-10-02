import CoreCallableAllowedTransport
import CoreCallableCapturedLambdaConstructor

namespace Ash.OneShot.CoreCallableRichBetaPreservation
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractSource (Contract Environment)
open CoreCallableContractAdmission
open CoreCallableReceiverRefinement (LexicalBounds CallBounds ReceiverRefines)
open CoreCallableCapturedLambdaConstructor (Family Origin)
open SourcePlannedChecks (DeclarationPolicy)

section
variable [evidence : DeclarationPolicy]

/-- The selected point uses actual argument dependencies, not its public port. -/
def actualCall (world receiver : List Nat) (value : Code)
    (issued : receiver ⊆ world)
    (received : ScopedPorts.Support.evaluate ScopedPorts.Support.empty value.dependencies ⊆ receiver) : CallBounds world :=
  ⟨world, receiver, ScopedPorts.Support.evaluate ScopedPorts.Support.empty value.dependencies,
    List.Subset.refl _, issued, received⟩

/-- All constructor points remain retained; the successor is computed at this
actual lexical/call point by the existing deterministic substitution. -/
structure Selected
    (functionSource : Source globals outward world allowed scope Environment.empty
      (.lambda parameter body) (.function input output requests latent publicPlan publicRows)
      [] (.request [] []) .pure Rows.pure)
    (lexical : LexicalBounds) (call : CallBounds world) (value : Code) where
  family : Family globals.registry outward globals.owners world Environment.empty
    parameter body input output requests latent publicPlan publicRows
  origin : Origin functionSource family
  authentic : family.Authentic
  known : LexicalBounds.Known lexical (Code.lambda parameter body).dependencies
  refinement : ReceiverRefines publicRows (family.rows lexical call) call.receiver
    (ScopedPorts.Support.evaluate (lexical.extend parameter call.argument).environment body.dependencies)
  nextPlan : Plan (family.dependencies lexical call)
  nextRows : Rows (signature nextPlan)
  current : CoreCallableContractAdmission.Supported globals outward call.world requests .none Environment.empty
    ScopedPorts.Support.empty (body.subst parameter value) output family.demand family.requirements
    nextPlan nextRows call.receiver call.receiver
  exactPlan : nextPlan = CoreCallablePlanSubstitution.plan body (family.plans lexical call) parameter value
  sameSignature : signature nextPlan = signature (family.plans lexical call)
  sameRows : HEq nextRows (family.rows lexical call)

end
end Ash.OneShot.CoreCallableRichBetaPreservation

namespace Ash.OneShot.CoreCallableContractAdmission
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open CoreCallableContractSource (Contract Environment)
open CoreCallableReceiverRefinement (LexicalBounds)
open CoreCallableRichBetaPreservation (Selected actualCall)
open SourcePlannedChecks (DeclarationPolicy)
section
variable [evidence : DeclarationPolicy]

/-- General rich beta at an authenticated original constructor. No successor
source, family or support bound is an input. -/
theorem Supported.beta_at
    (stable : SubstitutionPolicyStable (evidence := evidence) outward)
    (function : Supported globals outward world allowed scope Environment.empty ScopedPorts.Support.empty
      (.lambda parameter body) (.function input output requests latent publicPlan publicRows)
      [] (.request [] []) .pure Rows.pure functionBound receiver)
    (argument : Supported globals outward world allowed scope Environment.empty ScopedPorts.Support.empty
      value input argumentDemand argumentRequirements argumentPlan argumentRows argumentBound receiver)
    (closed : ClosedValue value) :
    ∃ lexical : LexicalBounds, lexical.environment = ScopedPorts.Support.empty ∧
      Nonempty (Selected function.source lexical (actualCall world receiver value function.receiverIssued argument.actual_received) value) := by
  obtain ⟨lexical, sameEnvironment, functionAuth⟩ := function.authentication
  obtain ⟨family, origin, authentic, known⟩ := CoreCallableCapturedLambdaConstructor.extract functionAuth
  let call := actualCall world receiver value function.receiverIssued argument.actual_received
  have functionReceived : ScopedPorts.Support.evaluate lexical.environment
      (Code.lambda parameter body).dependencies ⊆ call.receiver := by
    simpa only [sameEnvironment, call, actualCall] using function.actual_received
  have bodyAuth := authentic.1 lexical call known functionReceived
  have refinement := authentic.2 lexical call known functionReceived
  obtain ⟨argumentLexical, argumentEnvironment, argumentAuth⟩ := argument.authentication
  let replacementSource := IndexedSource.value_allowed (IndexedSource.value_summary argument.source closed.1) closed.1 requests .none
  have replacementAuth : Authenticated globals.registry outward replacementSource lexical receiver := by
    apply ((argumentAuth.value_summary closed.1).value_allowed closed.1 requests .none).value_reauthenticate closed
    simpa only [sameEnvironment] using argument.actual_received
  have replacement : Supported globals outward world requests .none Environment.empty ScopedPorts.Support.empty
      value input [] (.request [] []) .pure Rows.pure call.argument receiver :=
    ⟨replacementSource, SourceSupport.Bounds.canonical _ _,
      call.argumentReceived.trans call.receivingIssued,
      ⟨lexical, sameEnvironment, replacementAuth⟩, call.receivingIssued⟩
  have bodySupported : Supported globals outward world requests .none (Environment.empty.extend parameter input)
      (ScopedPorts.Support.extend ScopedPorts.Support.empty parameter call.argument)
      body output family.demand family.requirements (family.plans lexical call) (family.rows lexical call)
      receiver receiver :=
    ⟨family.body lexical call, by simpa only [LexicalBounds.environment_extend, sameEnvironment, call, actualCall] using bodyAuth.current_support,
      call.receivingIssued, ⟨lexical.extend parameter call.argument,
        by simp only [LexicalBounds.environment_extend, sameEnvironment], bodyAuth⟩, call.receivingIssued⟩
  obtain ⟨nextPlan, nextRows, nextCurrent, exactPlan, sameSignature, sameRows⟩ :=
    bodySupported.substitution_reannotated stable replacement closed
  exact ⟨lexical, sameEnvironment, ⟨⟨family, origin, authentic, known, refinement,
    nextPlan, nextRows, nextCurrent, exactPlan, sameSignature, sameRows⟩⟩⟩

end
end Ash.OneShot.CoreCallableContractAdmission

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open RecursiveRequirements (Requirements)
open SourceDependencyAnnotations (Dependencies)
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open CoreCallableContractSource (Contract Environment sequenceRows)
open CoreCallableContractAdmission (Globals Source IndexedSource Authenticated SubstitutionPolicyStable)
open CoreCallableReceiverRefinement (LexicalBounds)
open CoreCallableRichBetaPreservation (Selected actualCall)
open SourcePlannedChecks (DeclarationPolicy)
section
variable [evidence : DeclarationPolicy]

/-- Output provenance ties the successor's complete private checking rows to
one selected point of the original authenticated constructor family. -/
structure BetaPreserved
    {rootDemand : List Nat} {root : Requirements rootDemand}
    {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.app (.lambda parameter body) value) runtimeScope stack output final context root) where
  input : Contract
  requests : List Instance
  latent : Footprint
  publicDependencies : Dependencies
  publicPlan : Plan publicDependencies
  publicRows : Rows (signature publicPlan)
  functionDemand : List Nat
  functionRequirements : Requirements functionDemand
  functionDependencies : Dependencies
  functionPlan : Plan functionDependencies
  functionRows : Rows (signature functionPlan)
  originalFunction : Source globals outward world allowed runtimeScope Environment.empty
    (.lambda parameter body) (.function input output requests latent publicPlan publicRows)
    functionDemand functionRequirements functionPlan functionRows
  argumentDemand : List Nat
  argumentRequirements : Requirements argumentDemand
  argumentDependencies : Dependencies
  argumentPlan : Plan argumentDependencies
  argumentRows : Rows (signature argumentPlan)
  originalArgument : Source globals outward world allowed runtimeScope Environment.empty value input
    argumentDemand argumentRequirements argumentPlan argumentRows
  admitted : requests ⊆ allowed
  publicCertified : SourcePlannedChecks.Certified outward world publicPlan
  sameApplication : HEq (IndexedSource.app originalFunction originalArgument admitted publicCertified) site.current.source
  functionSource : Source globals outward world allowed runtimeScope Environment.empty
    (.lambda parameter body) (.function input output requests latent publicPlan publicRows)
    [] (.request [] []) .pure Rows.pure
  functionSummary : functionSource = IndexedSource.value_summary originalFunction (by trivial)
  lexical : LexicalBounds
  sameEnvironment : lexical.environment = ScopedPorts.Support.empty
  valueReceived : ScopedPorts.Support.evaluate ScopedPorts.Support.empty value.dependencies ⊆ actualReceiver world receiving ambient
  selected : Selected functionSource lexical
    (actualCall world (actualReceiver world receiving ambient) value actualReceiver.issued valueReceived) value
  nextRoot : Requirements rootDemand
  rootTransport : CoreCallableRootRefinement.RootTransport root nextRoot
  next : Site globals outward world allowed actions phases budget ambient installations
    (body.subst parameter value) .none stack output final context nextRoot
  exactDemand : next.sourceDemand = selected.family.demand
  exactRequirements : HEq next.requirements selected.family.requirements
  exactPlan : HEq next.plan selected.nextPlan
  exactRows : HEq next.rows selected.nextRows

omit evidence in
private theorem transport_beta_rows
    {first second : SourcePlanSignatures.Signature dependencies}
    {firstRows : Rows first} {secondRows : Rows second}
    (same : first = second) (sameRows : HEq firstRows secondRows)
    (certificate : SourceAdmission.Code outward actions budget phases world installations secondRows context)
    (checked : InstallationSupport.CodeChecked ambient outward certificate)
    (run : Accounting.Run world installations secondRows context root) :
    ∃ nextCertificate : SourceAdmission.Code outward actions budget phases world installations firstRows context,
      InstallationSupport.CodeChecked ambient outward nextCertificate ∧
      Accounting.Run world installations firstRows context root := by
  subst second
  cases eq_of_heq sameRows
  exact ⟨certificate, checked, run⟩

/-- Current rich beta preservation. The current Site is a preservation premise;
all selected private checking, successor source and root accounting are outputs. -/
theorem Site.beta {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    (stable : SubstitutionPolicyStable (evidence := evidence) outward)
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.app (.lambda parameter body) value) runtimeScope stack output final context root)
    (closed : ClosedValue value) (closure : ClosedValue (.lambda parameter body)) :
    Nonempty (BetaPreserved site) ∧
      RawStep ⟨.app (.lambda parameter body) value, runtimeScope, stack⟩
        ⟨body.subst parameter value, .none, stack⟩ [] [] := by
  constructor
  · rcases site with ⟨sourceDemand, requirements, dependencies, plan, rows, bound, current, received, certificate, certificateChecked,
      pending, retained, retainedChecked, accounting, annotated, row, annotation, checked, bounded⟩
    obtain ⟨lexical, sameEnvironment, authenticated⟩ := current.authentication
    cases authenticated with
    | checked actualSupport hereditary =>
      cases hereditary with
      | app functionAuth argumentAuth =>
        rename_i input requests latent publicDependencies publicPlan publicRows functionDemand functionRequirements
          functionDependencies functionPlan functionRows argumentDemand argumentRequirements argumentDependencies
          argumentPlan argumentRows publicCertified admitted argumentSource functionSource
        let receiver := actualReceiver world receiving ambient
        let summarySource := IndexedSource.value_summary functionSource closure.1
        have functionSupported : CoreCallableContractAdmission.Supported globals outward world allowed runtimeScope
            Environment.empty ScopedPorts.Support.empty (.lambda parameter body)
            (.function input output requests latent publicPlan publicRows)
            [] (.request [] []) .pure Rows.pure receiver receiver :=
          ⟨summarySource, by simpa only [sameEnvironment] using functionAuth.current_support,
            actualReceiver.issued, ⟨lexical, sameEnvironment, functionAuth.value_summary closure.1⟩, actualReceiver.issued⟩
        have argumentSupported : CoreCallableContractAdmission.Supported globals outward world allowed runtimeScope
            Environment.empty ScopedPorts.Support.empty value input argumentDemand argumentRequirements argumentPlan argumentRows receiver receiver :=
          ⟨argumentSource, by simpa only [sameEnvironment] using argumentAuth.current_support,
            actualReceiver.issued, ⟨lexical, sameEnvironment, argumentAuth⟩, actualReceiver.issued⟩
        obtain ⟨selectedLexical, selectedEnvironment, ⟨selected⟩⟩ :=
          functionSupported.beta_at stable argumentSupported closed
        cases certificate with
        | sequence functionCertificate restCertificate =>
          cases restCertificate with
          | sequence argumentCertificate publicCertificate =>
            cases certificateChecked with
            | sequence functionChecked restChecked =>
              cases restChecked with
              | sequence argumentChecked publicChecked =>
                have publicRun := (Accounting.silent_prefix_iff (Source.value_silent argumentSource closed.1) argumentRows publicRows).mp
                  ((Accounting.silent_prefix_iff (Source.value_silent functionSource closure.1) functionRows
                    (sequenceRows argumentRows publicRows)).mp accounting)
                have modeSame := retained.return_mode
                have selectedRetained : SourceAdmission.Pending outward actions budget phases world installations context .nil
                    .ordinary (hints.returnMode .ordinary) := by
                  simpa only [modeSame] using retained
                have selectedRetainedChecked : InstallationSupport.PendingChecked ambient outward selectedRetained := by
                  simpa only [modeSame] using retainedChecked
                let privateCertificate := selected.refinement.code outward actions budget phases world installations context selectedRetained publicCertificate
                have privateChecked := selected.refinement.checked ambient outward actions budget phases world installations context
                  selectedRetained publicCertificate
                  (SourceSupport.bounds_iff.mp (selected.authentic.1 selectedLexical _ selected.known
                    (by simpa only [selectedEnvironment, actualCall] using functionSupported.actual_received)).current_support)
                  actualReceiver.issued actualReceiver.received selectedRetainedChecked publicChecked
                obtain ⟨nextRoot, privateRun, rootTransport⟩ := selected.refinement.accounting world installations context root publicRun
                obtain ⟨nextCertificate, nextChecked, nextRun⟩ := transport_beta_rows selected.sameSignature selected.sameRows
                  privateCertificate privateChecked privateRun
                obtain ⟨nextAnnotated, nextRow, nextAnnotation, nextRootChecked, nextBounded⟩ :=
                  rootTransport.checked [] [] phases budget annotation checked bounded
                let next : Site globals outward world allowed actions phases budget ambient installations
                    (body.subst parameter value) .none stack output final context nextRoot :=
                  { sourceDemand := selected.family.demand, requirements := selected.family.requirements,
                    dependencies := selected.family.dependencies selectedLexical _, plan := selected.nextPlan, rows := selected.nextRows,
                    bound := receiver, current := selected.current.allowed_weaken admitted, received := actualReceiver.received,
                    certificate := nextCertificate, certificateChecked := nextChecked, pending := pending, retained := retained,
                    retainedChecked := retainedChecked, accounting := nextRun,
                    annotated := nextAnnotated, row := nextRow, annotation := nextAnnotation, checked := nextRootChecked, bounded := nextBounded }
                exact ⟨{
                  input := input, requests := requests, latent := latent, publicDependencies := publicDependencies,
                  publicPlan := publicPlan, publicRows := publicRows,
                  functionDemand := functionDemand, functionRequirements := functionRequirements,
                  functionDependencies := functionDependencies, functionPlan := functionPlan, functionRows := functionRows,
                  originalFunction := functionSource, argumentDemand := argumentDemand,
                  argumentRequirements := argumentRequirements, argumentDependencies := argumentDependencies,
                  argumentPlan := argumentPlan, argumentRows := argumentRows, originalArgument := argumentSource,
                  admitted := admitted, publicCertified := publicCertified, sameApplication := HEq.rfl,
                  functionSource := summarySource, functionSummary := rfl,
                  lexical := selectedLexical, sameEnvironment := selectedEnvironment,
                  valueReceived := argumentSupported.actual_received, selected := selected,
                  nextRoot := nextRoot, rootTransport := rootTransport, next := next,
                  exactDemand := rfl, exactRequirements := HEq.rfl, exactPlan := HEq.rfl, exactRows := HEq.rfl }⟩
  · exact .beta parameter body value runtimeScope stack closed closure

end
end Ash.OneShot.CoreCallableContractExecution

#print axioms Ash.OneShot.CoreCallableRichBetaPreservation.actualCall
#print axioms Ash.OneShot.CoreCallableContractAdmission.Supported.beta_at
#print axioms Ash.OneShot.CoreCallableContractExecution.Site.beta
