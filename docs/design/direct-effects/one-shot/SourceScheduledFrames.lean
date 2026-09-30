import SourceScheduledChecks

/-! Typed frames and retained scheduling share one explicit plan forest. Source
and capability erasures reuse the existing joint frame proofs. No plan is
reconstructed from an erased dependency index. -/
namespace Ash.OneShot.SourceScheduledFrames
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Value Environment Operations Contract Contracts)
open SourcePlannedSources (Expression Body Offer Declarations Context ValueSummary)
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
    ExecFrame → Value → Value → (demand : List Nat) → Requirements demand → (layer : DependencyScope → DependencyScope) → (decorate : Decoration layer) → PlanDecoration decorate →
      List Instance → List Instance → (evidence : optParam DeclarationEvidence recipeEvidence) → Prop where
  | plain {plan : Plan dependencies}
      (context : Context operations policy contracts world (fun _ => none) allowed plain.scope plain.context input output demand requirements (signature plan))
      (scope : ScopedPorts.EffectScope contracts.erase.erase.ports plain.scope ticket)
      (inputAnnotation : input.erase.erase.port = ScopedPorts.eraseType plain.input)
      (outputAnnotation : output.erase.erase.port = ScopedPorts.eraseType plain.output)
      (checked : Local outward actions phases world plan receiving) :
      Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world receiving (.plain plain) input output demand requirements (.plain dependencies) (fun rest => .plain rest) (fun rest => .plain plan rest) allowed allowed
  | handler {plans : ClausePlans handler.clauses (families handler)}
      (scope : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports handler.scope)
      (annotation : answer.erase.erase.port = ScopedPorts.eraseType handler.answer)
      (clauses : ScopedPorts.ClausesTyped operations.erase.erase.ports world SourceDependencyAnnotations.Environment.empty.erase.ports handler.effectInst answer.erase.erase.port residual handler.clauses)
      (coverage : ScopedPorts.Covers operations.erase.erase.ports handler.effectInst handler.clauses)
      (unique : (ScopedTyping.clauseKeys handler.clauses).Nodup)
      (declarations : Declarations operations policy contracts world (fun _ => none) residual handler.effectInst answer handler.clauses (tables handler) plans)
      (recipes : evidence (required handler) plans)
      (supplied : SourceContextualHints.checkRequirements receivingScope (required handler) = true)
      (capabilities : ClausesUse policy handler.clauses)
      (modes : SourceTemplates.ClauseModes handler.clauses (tables handler)) :
      Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world receiving (.handler handler) answer answer [] (.request [] [])
        (.handler handler.effectInst (tables handler) (families handler))
        (fun rest => .handler (required handler) rest) (fun rest => .handler rest) (handler.effectInst :: residual) residual
  | cell (scopeKnown : ScopedPorts.ScopeKnown contracts.erase.erase.ports.types caller)
      (noEscape : identity ∉ (ScopedPorts.eraseType answer).resources)
      (annotation : result.erase.erase.port = ScopedPorts.eraseType answer)
      (interface : ScopedPorts.EffectFrame operations.erase.erase.ports contracts.erase.erase.ports world (.cell identity payload caller answer) incoming outgoing) :
      Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world receiving (.cell identity payload caller answer) result result [] (.request [] []) (.cell identity) (fun rest => .cell rest) (fun rest => .cell rest) incoming outgoing
  | armed {callbackPlan : Plan callbackDep} (scopeKnown : ScopedPorts.ScopeKnown contracts.erase.erase.ports.types action.scope)
      (callback : ValueSummary operations policy contracts world (fun _ => none) [] action.action (.function .unit .unit action.requests latent (signature callbackPlan)))
      (annotation : result.erase.erase.port = ScopedPorts.eraseType action.answer)
      (interface : ScopedPorts.EffectFrame operations.erase.erase.ports contracts.erase.erase.ports world (.armed action) incoming outgoing)
      (checked : Local outward actions phases world callbackPlan (.running receiving)) :
      Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world receiving (.armed action) result result [] (.request [] (qualify true latent))
        (.cleanup action.requests callbackDep) (fun rest => .cleanup rest) (fun rest => .cleanup callbackPlan rest) incoming outgoing
  | running {callbackPlan : Plan callbackDep} (scopeKnown : ScopedPorts.ScopeKnown contracts.erase.erase.ports.types action.scope)
      (callback : ValueSummary operations policy contracts world (fun _ => none) [] action.action (.function .unit .unit action.requests latent (signature callbackPlan)))
      (saved : ValueSummary operations policy contracts world (fun _ => none) [] value result)
      (annotation : result.erase.erase.port = ScopedPorts.eraseType action.answer)
      (interface : ScopedPorts.EffectFrame operations.erase.erase.ports contracts.erase.erase.ports world (.running action value closed) incoming outgoing) :
      Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world receiving (.running action value closed) .unit result [] (.request [] []) .running (fun rest => .running rest) (fun rest => .running rest) incoming outgoing
  | closing (scopeKnown : ScopedPorts.ScopeKnown contracts.erase.erase.ports.types caller)
      (interface : ScopedPorts.EffectFrame operations.erase.erase.ports contracts.erase.erase.ports world (.closing identity caller) incoming outgoing) :
      Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world receiving (.closing identity caller) .unit .unit [] (.request [] []) .running (fun rest => .running rest) (fun rest => .running rest) incoming outgoing
  | retiring (known : contracts owner = some contract)
      (interface : ScopedPorts.EffectFrame operations.erase.erase.ports contracts.erase.erase.ports world (.retiring owner) incoming outgoing) :
      Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world receiving (.retiring owner) .unit .unit [owner] (.retire owner) .running (fun rest => .running rest) (fun rest => .running rest) incoming outgoing

theorem Frame.source [SourceScheduledChecks.DeclarationProjection admission certification] {receivingHints : Hints receivingScope} {receiving : Forest receivingHints}
    (frame : Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world receiving entry input output demand requirements layer decorate decoratePlans incoming outgoing) :
    SourcePlannedCheckedFrames.Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world receivingHints entry input output demand requirements layer decorate incoming outgoing := by
  cases frame with
  | plain context scope inputAnnotation outputAnnotation checked => exact .plain context scope inputAnnotation outputAnnotation checked.erase
  | handler scope annotation clauses coverage unique declarations recipes supplied capabilities modes =>
      exact .handler scope annotation clauses coverage unique declarations recipes capabilities modes
  | cell scopeKnown noEscape annotation interface => exact .cell scopeKnown noEscape annotation interface
  | armed scopeKnown callback annotation interface checked => exact .armed scopeKnown callback annotation interface checked.erase
  | running scopeKnown callback saved annotation interface => exact .running scopeKnown callback saved annotation interface
  | closing scopeKnown interface => exact .closing scopeKnown interface
  | retiring known interface => exact .retiring known interface

theorem Frame.pending {restHints : Hints restScope} {outsideHints : Hints outsideScope}
    {rest : Forest restHints} {outside : Forest outsideHints}
    (frame : Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world
      (rest.append outside) entry input output demand requirements layer decorate decoratePlans incoming outgoing)
    (tail : Pending outward actions phases world rest outside) :
    Pending outward actions phases world (decoratePlans rest) outside := by
  cases frame with
  | plain context scope inputAnnotation outputAnnotation checked => exact .plain checked tail
  | armed scopeKnown callback annotation interface checked => exact .cleanup checked tail
  | handler => exact .handler ‹_› tail
  | cell => exact .cell tail
  | running | closing | retiring => exact .running tail

inductive Segment [admission : SourceScheduledChecks.DeclarationPolicy] [certification : SourcePlannedChecks.DeclarationPolicy] (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : Families) (required : SourceContextualRechecking.Required) (actions : Syntax.UsageTickets)
    (outward : List Instance) (phases : OwnerPhaseTransitions.Phases) (world : List Nat) :
    Stack → Value → Value → (demand : List Nat) → Requirements demand → Store → {dependencyScope : DependencyScope} → {hints : Hints dependencyScope} → Forest hints → {outsideScope : DependencyScope} → {outsideHints : Hints outsideScope} → Forest outsideHints →
      List Instance → List Instance → (evidence : optParam DeclarationEvidence recipeEvidence) → Prop where
  | nil (bound : incoming ⊆ outgoing) :
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world .nil result result [] (.request [] []) [] .nil outside incoming outgoing
  | push (head : Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world (restHints.append outside) entry input middle headDemand first layer decorate decoratePlans inner outer)
      (tail : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world rest middle output tailDemand second records restHints outside outer outgoing)
      (bound : incoming ⊆ inner) :
      Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world (.push entry rest) input output
        (headDemand ++ tailDemand) (.sequence (first.prepend (OwnerPhases.ofStack tables rest)) second) records (decoratePlans restHints) outside incoming outgoing
  | live (known : contracts owner = some contract) (actionKnown : actions owner = some rights)
      (inputAnnotation : contract.input.erase.erase.port = ScopedPorts.eraseType inputType)
      (answerAnnotation : contract.answer.erase.erase.port = ScopedPorts.eraseType answerType)
      (scope : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports caller)
      (held : contract.held = ProtectionContexts.protectedMode capture.erase)
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

theorem Segment.source [SourceScheduledChecks.DeclarationProjection admission certification] {hints : Hints dependencyScope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (segment : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world stack input output demand requirements records forest outside incoming outgoing) :
    SourcePlannedCheckedFrames.Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world stack input output demand requirements records hints outsideHints incoming outgoing := by
  induction segment with
  | nil bound => exact .nil bound
  | push head tail bound ih => exact .push head.source ih bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held ihSaved savedBound ihTail resume close bound
  | spent known annotation scope tail bound ih => exact .spent known annotation scope ih bound

theorem Segment.pending {hints : Hints dependencyScope} {outsideHints : Hints outsideScope}
    {forest : Forest hints} {outside : Forest outsideHints}
    (segment : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world stack input output demand requirements records forest outside incoming outgoing) :
    Pending outward actions phases world forest outside := by
  induction segment with
  | nil bound => exact .nil
  | push head tail bound ih => exact head.pending ih
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live ihSaved ihTail
  | spent known annotation scope tail bound ih => exact .spent ih

/-- Change only the declaration evidence. Source syntax, types and retained
plans are preserved; any local checks in the frame are unchanged. -/
theorem Frame.map_evidence
    (frame : Frame (evidence := evidence) operations policy contracts tables families required outward actions phases world receiving entry input output demand requirements layer decorate decoratePlans incoming outgoing)
    (changed : ∀ needed {clauses families} (plans : ClausePlans clauses families),
      evidence needed plans → nextEvidence needed plans) :
    Frame (evidence := nextEvidence) operations policy contracts tables families required outward actions phases world receiving entry input output demand requirements layer decorate decoratePlans incoming outgoing := by
  cases frame
  all_goals constructor <;> first | assumption | exact changed _ _ ‹_›

theorem Segment.map_evidence
    (segment : Segment (evidence := evidence) operations policy contracts tables families required actions outward phases world stack input output demand requirements records forest outside incoming outgoing)
    (changed : ∀ needed {clauses families} (plans : ClausePlans clauses families),
      evidence needed plans → nextEvidence needed plans) :
    Segment (evidence := nextEvidence) operations policy contracts tables families required actions outward phases world stack input output demand requirements records forest outside incoming outgoing := by
  induction segment with
  | nil bound => exact .nil bound
  | push head tail bound ih => exact .push (head.map_evidence changed) (ih changed) bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held (ihSaved changed) savedBound (ihTail changed) resume close bound
  | spent known annotation scope tail bound ih => exact .spent known annotation scope (ih changed) bound

end Ash.OneShot.SourceScheduledFrames

#print axioms Ash.OneShot.SourceScheduledFrames.Frame.source
#print axioms Ash.OneShot.SourceScheduledFrames.Frame.pending
#print axioms Ash.OneShot.SourceScheduledFrames.Segment.source
#print axioms Ash.OneShot.SourceScheduledFrames.Segment.pending

#print axioms Ash.OneShot.SourceScheduledFrames.Frame.map_evidence
#print axioms Ash.OneShot.SourceScheduledFrames.Segment.map_evidence
