import SourceAnnotatedRuntime

/-! Annotated runtime frames and recursively saved segments retain the same
rich source types and scheduling plans. Their erasure constructs the existing
scheduled frame judgment rather than assuming an independent source proof. -/
namespace Ash.OneShot.SourceAnnotatedRuntimeTyping
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Value Environment Operations Contract Contracts)
open SourceAnnotatedSources (Expression Body Offer Declarations Context ValueSummary)
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlanSignatures (signature)
open SourceContextualHints (Hints)
open SourceScheduledChecks (Local Pending)
open SourceRetainedPlans (Forest)
open SourcePlannedFrames (DependencyScope Families Decoration DeclarationEvidence recipeEvidence)
open RecursiveRequirements (Requirements Store)

abbrev PlanDecoration {layer : DependencyScope → DependencyScope} (decorate : Decoration layer) :=
  {scope : DependencyScope} → {hints : Hints scope} → Forest hints → Forest (decorate hints)

variable [certification : SourcePlannedChecks.DeclarationPolicy]
variable [admission : SourceScheduledChecks.DeclarationPolicy]

inductive Frame [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy] (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : Families) (required : SourceContextualRechecking.Required)
    (outward : List Instance) (actions : Syntax.UsageTickets) (phases : OwnerPhaseTransitions.Phases)
    (world : List Nat) {receivingScope : DependencyScope} {receivingHints : Hints receivingScope} (receiving : Forest receivingHints) :
    SourceAnnotatedRuntime.Frame → Value → Value → (demand : List Nat) → Requirements demand → (layer : DependencyScope → DependencyScope) → (decorate : Decoration layer) → PlanDecoration decorate →
      List Instance → List Instance → (evidence : optParam DeclarationEvidence recipeEvidence) → Prop where
  | plain {plan : Plan dependencies}
      (context : Context operations policy contracts world (fun _ => none) allowed plain.scope plain.context input output demand requirements (signature plan))
      (hint : SourceFocusHints.checkSource Instantiation.Environment.empty plain.context.hint output = true)
      (closed : plain.context.ResourceClosed)
      (scope : ScopedPorts.EffectScope contracts.erase.erase.ports plain.scope ticket)
      (inputAnnotation : input.erase.erase.port = ScopedPorts.eraseType plain.input)
      (outputAnnotation : output.erase.erase.port = ScopedPorts.eraseType plain.output)
      (checked : Local outward actions phases world plan receiving) :
      Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world receiving (.plain plain) input output demand requirements (.plain dependencies) (fun rest => .plain rest) (fun rest => .plain plan rest) allowed allowed
  | handler {plans : ClausePlans handler.clauses.erase (families handler.erase)}
      (scope : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports handler.scope)
      (annotation : answer.erase.erase.port = ScopedPorts.eraseType handler.answer)
      (clauses : ScopedPorts.ClausesTyped operations.erase.erase.ports world SourceDependencyAnnotations.Environment.empty.erase.ports handler.effectInst answer.erase.erase.port residual handler.clauses.erase)
      (coverage : ScopedPorts.Covers operations.erase.erase.ports handler.effectInst handler.clauses.erase)
      (unique : (ScopedTyping.clauseKeys handler.clauses.erase).Nodup)
      (declarations : Declarations operations policy contracts world (fun _ => none) residual handler.effectInst answer handler.clauses (tables handler.erase) plans)
      (recipes : evidence (required handler.erase) plans)
      (supplied : SourceContextualHints.checkRequirements receivingScope (required handler.erase) = true)
      (capabilities : ClausesUse policy handler.clauses.erase)
      (modes : SourceTemplates.ClauseModes handler.clauses.erase (tables handler.erase)) :
      Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world receiving (.handler handler) answer answer [] (.request [] [])
        (.handler handler.effectInst (tables handler.erase) (families handler.erase))
        (fun rest => .handler (required handler.erase) rest) (fun rest => .handler rest) (handler.effectInst :: residual) residual
  | cell (scopeKnown : ScopedPorts.ScopeKnown contracts.erase.erase.ports.types caller)
      (noEscape : identity ∉ (ScopedPorts.eraseType answer).resources)
      (annotation : result.erase.erase.port = ScopedPorts.eraseType answer)
      (interface : ScopedPorts.EffectFrame operations.erase.erase.ports contracts.erase.erase.ports world (.cell identity payload caller answer) incoming outgoing) :
      Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world receiving (.cell identity payload caller answer) result result [] (.request [] []) (.cell identity) (fun rest => .cell rest) (fun rest => .cell rest) incoming outgoing
  | armed {callbackPlan : Plan callbackDep} (scopeKnown : ScopedPorts.ScopeKnown contracts.erase.erase.ports.types action.scope)
      (callback : ValueSummary operations policy contracts world (fun _ => none) [] action.action (.function .unit .unit action.requests latent (signature callbackPlan)))
      (annotation : result.erase.erase.port = ScopedPorts.eraseType action.answer)
      (interface : ScopedPorts.EffectFrame operations.erase.erase.ports contracts.erase.erase.ports world (.armed action.erase) incoming outgoing)
      (checked : Local outward actions phases world callbackPlan (.running receiving)) :
      Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world receiving (.armed action) result result [] (.request [] (qualify true latent))
        (.cleanup action.requests callbackDep) (fun rest => .cleanup rest) (fun rest => .cleanup callbackPlan rest) incoming outgoing
  | running {callbackPlan : Plan callbackDep} (scopeKnown : ScopedPorts.ScopeKnown contracts.erase.erase.ports.types action.scope)
      (callback : ValueSummary operations policy contracts world (fun _ => none) [] action.action (.function .unit .unit action.requests latent (signature callbackPlan)))
      (saved : ValueSummary operations policy contracts world (fun _ => none) [] value result)
      (annotation : result.erase.erase.port = ScopedPorts.eraseType action.answer)
      (interface : ScopedPorts.EffectFrame operations.erase.erase.ports contracts.erase.erase.ports world (.running action.erase value.erase closed) incoming outgoing) :
      Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world receiving (.running action value closed) .unit result [] (.request [] []) .running (fun rest => .running rest) (fun rest => .running rest) incoming outgoing
  | closing (scopeKnown : ScopedPorts.ScopeKnown contracts.erase.erase.ports.types caller)
      (interface : ScopedPorts.EffectFrame operations.erase.erase.ports contracts.erase.erase.ports world (.closing identity caller) incoming outgoing) :
      Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world receiving (.closing identity caller) .unit .unit [] (.request [] []) .running (fun rest => .running rest) (fun rest => .running rest) incoming outgoing
  | retiring (known : contracts owner = some contract)
      (interface : ScopedPorts.EffectFrame operations.erase.erase.ports contracts.erase.erase.ports world (.retiring owner) incoming outgoing) :
      Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world receiving (.retiring owner) .unit .unit [owner] (.retire owner) .running (fun rest => .running rest) (fun rest => .running rest) incoming outgoing

theorem Frame.erase {receivingHints : Hints receivingScope} {receiving : Forest receivingHints}
    (frame : Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world receiving
      entry input output demand requirements layer decorate decoratePlans incoming outgoing) :
    SourceScheduledFrames.Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world receiving
      entry.erase input output demand requirements layer decorate decoratePlans incoming outgoing := by
  cases frame with
  | plain context hint closed scope inputAnnotation outputAnnotation checked =>
      exact .plain context.erase scope inputAnnotation outputAnnotation checked
  | handler scope annotation clauses coverage unique declarations recipes supplied capabilities modes =>
      exact .handler scope annotation clauses coverage unique declarations.erase recipes supplied capabilities modes
  | cell scopeKnown noEscape annotation interface => exact .cell scopeKnown noEscape annotation interface
  | armed scopeKnown callback annotation interface checked => exact .armed scopeKnown callback.erase annotation interface checked
  | running scopeKnown callback saved annotation interface => exact .running scopeKnown callback.erase saved.erase annotation interface
  | closing scopeKnown interface => exact .closing scopeKnown interface
  | retiring known interface => exact .retiring known interface

inductive Segment [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy] (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : Families) (required : SourceContextualRechecking.Required) (actions : Syntax.UsageTickets)
    (outward : List Instance) (phases : OwnerPhaseTransitions.Phases) (world : List Nat) :
    SourceAnnotatedRuntime.Stack → Value → Value → (demand : List Nat) → Requirements demand → Store → {dependencyScope : DependencyScope} → {hints : Hints dependencyScope} → Forest hints → {outsideScope : DependencyScope} → {outsideHints : Hints outsideScope} → Forest outsideHints →
      List Instance → List Instance → (evidence : optParam DeclarationEvidence recipeEvidence) → Prop where
  | nil (bound : incoming ⊆ outgoing) :
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world .nil result result [] (.request [] []) [] .nil outside incoming outgoing
  | push (head : Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world (restHints.append outside) entry input middle headDemand first layer decorate decoratePlans inner outer)
      (tail : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world rest middle output tailDemand second records restHints outside outer outgoing)
      (bound : incoming ⊆ inner) :
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world (.push entry rest) input output
        (headDemand ++ tailDemand) (.sequence (first.prepend (OwnerPhases.ofStack tables rest.erase)) second) records (decoratePlans restHints) outside incoming outgoing
  | live (known : contracts owner = some contract) (actionKnown : actions owner = some rights)
      (inputAnnotation : contract.input.erase.erase.port = ScopedPorts.eraseType inputType)
      (answerAnnotation : contract.answer.erase.erase.port = ScopedPorts.eraseType answerType)
      (scope : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports caller)
      (held : contract.held = ProtectionContexts.protectedMode capture.erase.erase)
      (saved : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
        capture contract.input contract.answer contract.resumeDemand body nested savedHints (restHints.append outside) [] savedBoundary)
      (savedBound : rights.resume = true → savedBoundary ⊆ contract.resumeEffects)
      (tail : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world rest contract.answer output
        demand requirements remaining restHints outside boundary outgoing)
      (resume : rights.resume = true → contract.resumeEffects ⊆ boundary)
      (close : rights.dispose = true → contract.closeEffects ⊆ boundary)
      (bound : incoming ⊆ boundary) :
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world (.live owner inputType answerType capture caller rest)
        contract.answer output demand (.sequence (.spent owner) requirements)
        ((⟨owner, .resume⟩, ⟨contract.resumeDemand, body⟩) :: (nested ++ remaining)) (.live (owner := owner) savedHints restHints) outside incoming outgoing
  | spent (known : contracts owner = some contract)
      (annotation : contract.answer.erase.erase.port = ScopedPorts.eraseType answerType)
      (scope : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports caller)
      (tail : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world rest contract.answer output
        demand requirements records restHints outside boundary outgoing)
      (bound : incoming ⊆ boundary) :
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world (.spent owner answerType caller rest) contract.answer output
        demand (.sequence (.spent owner) requirements) records (.spent (owner := owner) restHints) outside incoming outgoing

theorem Segment.erase {hints : Hints dependencyScope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (segment : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records forest outside incoming outgoing) :
    SourceScheduledFrames.Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack.erase input output demand requirements records forest outside incoming outgoing := by
  induction segment with
  | nil bound => exact .nil bound
  | push head tail bound ih => exact .push head.erase ih bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held ihSaved savedBound ihTail resume close bound
  | spent known annotation scope tail bound ih => exact .spent known annotation scope ih bound

/-- Frame ports come from the same retained rich types, including code-free
frames and the unit input of a running cleanup. -/
theorem Frame.ports
    (frame : Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world receiving
      entry input output demand requirements layer decorate decoratePlans incoming outgoing) :
    input.erase.erase.port = ScopedPorts.eraseType entry.erase.erase.input ∧
    output.erase.erase.port = ScopedPorts.eraseType entry.erase.erase.output := by
  cases frame with
  | plain context hint closed scope inputAnnotation outputAnnotation checked => exact ⟨inputAnnotation, outputAnnotation⟩
  | handler scope annotation clauses coverage unique declarations recipes supplied capabilities modes => exact ⟨annotation, annotation⟩
  | cell scopeKnown noEscape annotation interface => exact ⟨annotation, annotation⟩
  | armed scopeKnown callback annotation interface checked => exact ⟨annotation, annotation⟩
  | running scopeKnown callback saved annotation interface => exact ⟨rfl, annotation⟩
  | closing scopeKnown interface => exact ⟨rfl, rfl⟩
  | retiring known interface => exact ⟨rfl, rfl⟩

theorem Segment.input_port
    (segment : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world
      stack input output demand requirements records forest outside incoming outgoing) :
    SourceScheduledExecution.stackInputPort stack.erase output.erase.erase.port = input.erase.erase.port := by
  cases segment with
  | nil bound => rfl
  | push head tail bound => exact head.ports.1.symm
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound => exact answerAnnotation.symm
  | spent known annotation scope tail bound => exact annotation.symm

end Ash.OneShot.SourceAnnotatedRuntimeTyping

#print axioms Ash.OneShot.SourceAnnotatedRuntimeTyping.Frame.erase
#print axioms Ash.OneShot.SourceAnnotatedRuntimeTyping.Segment.erase

#print axioms Ash.OneShot.SourceAnnotatedRuntimeTyping.Frame.ports
#print axioms Ash.OneShot.SourceAnnotatedRuntimeTyping.Segment.input_port
