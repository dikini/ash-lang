import CoreCallableRichOriginalResultFinish

/-! UNCOMPILED current-input composition for the original-result cleanup path.
The three imported draft foundations must elaborate before this leaf can be
verified. SAME heap and original runtime suffix are retained by the existing
strong carrier; only its demonstrated beta/Boolean transports are composed.
No arbitrary callback grammar, termination or future Unit endpoint is claimed. -/
namespace Ash.OneShot.CoreCallableRichOriginalResultAuthority
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreSyntax CoreMachine CoreCallableGeneratedChronology
open CoreCallableInitialChronology CoreCallableGeneralHistory CoreCallableRunningOccurrence
open CoreCallableGeneratedCleanupCompletion CoreCallableReachableResume
open CoreCallableContractAdmission CoreCallableContractExecution
open CoreCallableContractSource (Contract Environment)
open SourceDeclarationPlans (Plan)
open SourceDependencyAnnotations (Dependencies)
open SourcePlanSignatures (signature)
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (Certified DeclarationPolicy)
open CoreCallableRichNormalCleanupPhases
open CoreCallableInitialAdmission (Program)
open CoreCallableReceiverRefinement (LexicalBounds)
open RecursiveRequirements (Requirements)
open CoreCallableRichBranchCurrentOrigins (DecisionInput decision_result decision_focus)

variable {graph : Graph} {originalEndpoint currentEndpoint : Endpoint graph}
variable [evidence : DeclarationPolicy]
variable {initialGlobals : Globals} {initialActions : Syntax.UsageTickets}
variable {initialBudget : Footprint} {originalCode : Code}
variable {program : Program initialGlobals initialActions initialBudget originalCode}
variable {seed : InitialInput graph originalCode}
variable {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving}
variable {context : Context hints} {callbackDependencies : Dependencies}
variable {callbackSignature : SourcePlanSignatures.Signature callbackDependencies}
variable {callbackRows : Rows callbackSignature}
variable {originalSite : PhaseSite globals outward world allowed actions phases budget
  ambient installations value originalScope (.push (.armed data) stack) originalContract final
  (Context.cleanup (needs := requests) latent callbackRows context) originalRoot}
variable {related : CoreValueRelation.ValueRel graph originalEndpoint.owners
  originalEndpoint.state.heap runtimeValue value}
variable {authority : OriginalResultAuthority originalSite related}
variable {start : RunningStartPast graph cleanupOwners action environment data runtimeValue value
  physical stack}


/-- Pair the explicit SAME original Program and current phase provenance with
the strong original-result carrier at
ONE endpoint and SAME authority/start. The original admission witness is kept
explicitly; equality of this Prop witness never recovers saved source metadata.
The phase stack is a separate index: current.related relates its machine to the
actual endpoint, while carrier retains that endpoint's lexical boundary. -/
structure OriginalResultPhaseCurrent
    (program : Program initialGlobals initialActions initialBudget originalCode)
    (seed : InitialInput graph originalCode)
    (authority : OriginalResultAuthority originalSite related)
    (start : RunningStartPast graph cleanupOwners action environment data runtimeValue value
      physical stack)
    (site : PhaseSite globals outward world requests actions phases budget ambient installations
      expression currentScope phaseStack output final (Context.normal context)
      activeRoot) where
  current : PhaseCurrent program currentEndpoint site
  carrier : StrongOriginalResultCurrent authority start currentEndpoint
  inputSame : current.input = seed

/-- Current armed premises seed the joined receipt from the SAME actual strong
normal-start event, retaining its original InitialInput and both root histories. -/
theorem original_result_phase_start
    (current : PhaseCurrent program originalEndpoint originalSite)
    (origin : ArmedOrigin originalEndpoint data stack)
    (returned : originalEndpoint.state.control = .returned runtimeValue)
    (empty : EmptyFocus originalEndpoint value originalScope) :
    ∃ produced : StrongOriginalResultNormalStartEvent (related := related) current origin,
      Nonempty (OriginalResultPhaseCurrent (currentEndpoint := started produced.event.start)
        program current.input produced.event.authority
        produced.event.start produced.event.authority.next) := by
  obtain ⟨produced⟩ := strong_original_result_normal_start_event (related := related) current origin returned empty
  exact ⟨produced,⟨⟨produced.event.after,produced.carrier,Subsingleton.elim _ _⟩⟩⟩

/-- Consume the current beta input and joined receipt. Both outputs are built
at beta_result input.after, with the same original authority/start and input;
no desired successor phase receipt or carrier is a premise. -/
theorem original_result_phase_beta
    (stable : SubstitutionPolicyStable (evidence := evidence) outward)
    (input : BetaInput currentEndpoint)
    (site : PhaseSite globals outward world requests actions phases budget ambient installations
      (.app (.lambda input.parameter input.bodyCode) input.argument) input.scope
      currentEndpoint.lexical output final (Context.normal context) activeRoot)
    (joined : OriginalResultPhaseCurrent (currentEndpoint := currentEndpoint)
      program seed authority start site) :
    ∃ event : PhaseBetaEvent input site joined.current,
      Nonempty (OriginalResultPhaseCurrent (currentEndpoint := (beta_result input).after)
        program seed authority start event.preserved.next) := by
  obtain ⟨event⟩ := phase_beta_event stable input site joined.current
  exact ⟨event,⟨⟨event.after,joined.carrier.beta input,Subsingleton.elim _ _⟩⟩⟩

/-- Consume the current Boolean input and joined receipt at the actual selected
endpoint. This composes existing decision provenance and strong preservation;
Generated remains unchanged and excludes Boolean. -/
theorem original_result_phase_decision
    (input : DecisionInput currentEndpoint)
    (site : PhaseSite globals outward world requests actions phases budget ambient installations
      (.branch (.boolean input.choice) input.yesCode input.noCode) input.plain.scope
      currentEndpoint.lexical output final (Context.normal context) activeRoot)
    (joined : OriginalResultPhaseCurrent (currentEndpoint := currentEndpoint)
      program seed authority start site) :
    ∃ event : PhaseDecisionEvent input site joined.current,
      Nonempty (OriginalResultPhaseCurrent (currentEndpoint := (decision_result input).after)
        program seed authority start event.preserved.next) := by
  obtain ⟨event⟩ := phase_decision_event input site joined.current
  exact ⟨event,⟨⟨event.after,joined.carrier.decision input,Subsingleton.elim _ _⟩⟩⟩

/-- Observed CURRENT Unit/EmptyFocus consumes the joined receipt and reuses the
existing restoration event. Its saved full contract, ownership and discharge
come from that event; the SAME original admission, root Core prefix and RawTrace
are exported alongside its endpoint accounting. No future completion is input. -/
theorem original_result_phase_finish
    (callback : PhaseSite globals outward world requests actions phases budget ambient installations
      .unit activeScope currentEndpoint.lexical .unit final (Context.normal context) activeRoot)
    (joined : OriginalResultPhaseCurrent (currentEndpoint := currentEndpoint)
      program seed authority start callback)
    (returned : currentEndpoint.state.control = .returned .unit)
    (empty : EmptyFocus currentEndpoint .unit activeScope) :
    ∃ event : OriginalResultFinishEvent joined.carrier callback joined.current,
      event.after.input = seed ∧
      CoreAllocationHistory.Steps graph event.after.coreCount
        (CoreMachine.initial graph) event.runtime.after.state ∧
      SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.RawTrace
        ⟨.eval ⟨originalCode,.none,.nil⟩,[],[]⟩ event.after.eventCount event.after.run ∧
      (Ledger event.after.run.erase ∧ event.after.run.completed.Nodup ∧
        (∀ owner, owner ∈ event.after.run.machine.stack.erase.owners →
          owner ∉ event.after.run.completed)) := by
  obtain ⟨event⟩ := original_result_finish_event joined.carrier callback joined.current returned empty
  exact ⟨event,Subsingleton.elim _ _,event.after.core,event.after.past,
    event.endpoint_accounting⟩

end Ash.OneShot.CoreCallableRichOriginalResultAuthority

#print axioms Ash.OneShot.CoreCallableRichOriginalResultAuthority.original_result_phase_start
#print axioms Ash.OneShot.CoreCallableRichOriginalResultAuthority.original_result_phase_beta
#print axioms Ash.OneShot.CoreCallableRichOriginalResultAuthority.original_result_phase_decision
#print axioms Ash.OneShot.CoreCallableRichOriginalResultAuthority.original_result_phase_finish
