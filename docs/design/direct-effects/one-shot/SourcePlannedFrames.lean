import SourcePlannedAllocation

/-! Retained source frames preserve synchronized value annotations and actual
checking plans. Installed handlers retain structural recipes for both offered
modes. Erasure reuses the existing source frame and segment judgments. Local
execution checking and full runtime preservation remain separate obligations. -/
namespace Ash.OneShot.SourcePlannedFrames
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Value Environment Operations Contract Contracts)
open SourcePlannedSources (Expression Body Offer Declarations Context ValueSummary)
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlanSignatures (signature)
open SourceContextualHints (Hints)
open RecursiveRequirements (Requirements Store)
abbrev DependencyScope := SourceDependencyCapture.Scope
abbrev Families := SourceDependencyCapture.Families
abbrev Decoration (layer : DependencyScope → DependencyScope) := ∀ {scope}, Hints scope → Hints (layer scope)

/-- Declaration syntax and value typing do not depend on a particular scheme
for checking future captures. Evidence is indexed separately and defaults to
the earlier recipe discipline for existing clients. -/
abbrev DeclarationEvidence := ∀ (_required : List SourceContextualHints.Requirement)
    {clauses : Clauses} {families : SourceDependencyAnnotations.ClauseDependencies}, ClausePlans clauses families → Prop

def recipeEvidence : DeclarationEvidence := fun required {_ _} plans =>
  SourcePlannedRecipeDeclarations.Declarations required plans

/-- Typing-only projection: actual declaration plans remain in the source
judgment, while execution obligations must be established separately. -/
def planEvidence : DeclarationEvidence := fun _ {_ _} _ => True

theorem offer_erase {plans : SourceDeclarationPlans.ModePlans family}
    (source : Offer operations policy contracts world environment allowed parameter binder argument input answer
      resumeEffects closeEffects code held disposes row plans) :
    SourceDependencyAnnotations.Offer operations.erase policy contracts.erase world environment.erase allowed parameter binder
      argument.erase input.erase answer.erase resumeEffects closeEffects code held disposes row family := by
  cases source with
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface source =>
      apply SourceDependencyAnnotations.Offer.available resumeInterface closeInterface
      intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
      have absent : contracts owner = none := by simpa only [Contracts.erase, Option.map_eq_none_iff] using fresh
      have exactErasure := SourcePlannedSources.refine_contract_erase inputSame answerSame
      have body := SourcePlannedAllocationData.body_erase
        (source owner (SourcePlannedSources.refineContract contract input answer) absent rfl rfl resumeSame closeSame heldSame balance)
      simpa only [SourcePlannedTyping.contracts_erase_insert, exactErasure,
        SourcePlannedTyping.environment_erase_extend] using body

theorem declarations_erase {plans : ClausePlans clauses families}
    (source : Declarations operations policy contracts world environment allowed effect answer clauses table plans) :
    SourceDependencyAnnotations.Declarations operations.erase policy contracts.erase world environment.erase allowed effect
      answer.erase clauses table families := by
  induction clauses using Clauses.rec (motive_1 := fun _ => True) generalizing table families
  case nil => cases source; exact .nil
  case cons operation parameter binder body rest ihBody ihRest => cases source with
    | cons known ordinary protectedMode rest =>
        exact .cons (SourcePlannedSources.operation_erase known) (offer_erase ordinary) (offer_erase protectedMode) (ihRest rest)
  all_goals trivial

inductive Frame (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : Families) (required : SourceContextualRechecking.Required) (world : List Nat) :
    ExecFrame → Value → Value → (demand : List Nat) → Requirements demand → (layer : DependencyScope → DependencyScope) → Decoration layer →
      List Instance → List Instance → (evidence : optParam DeclarationEvidence recipeEvidence) → Prop where
  | plain {plan : Plan dependencies}
      (context : Context operations policy contracts world (fun _ => none) allowed plain.scope plain.context input output demand requirements (signature plan))
      (scope : ScopedPorts.EffectScope contracts.erase.erase.ports plain.scope ticket)
      (inputAnnotation : input.erase.erase.port = ScopedPorts.eraseType plain.input)
      (outputAnnotation : output.erase.erase.port = ScopedPorts.eraseType plain.output) :
      Frame (evidence := evidence) operations policy contracts tables families required world (.plain plain) input output demand requirements (.plain dependencies) (fun rest => .plain rest) allowed allowed
  | handler {plans : ClausePlans handler.clauses (families handler)}
      (scope : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports handler.scope)
      (annotation : answer.erase.erase.port = ScopedPorts.eraseType handler.answer)
      (clauses : ScopedPorts.ClausesTyped operations.erase.erase.ports world SourceDependencyAnnotations.Environment.empty.erase.ports handler.effectInst answer.erase.erase.port residual handler.clauses)
      (coverage : ScopedPorts.Covers operations.erase.erase.ports handler.effectInst handler.clauses)
      (unique : (ScopedTyping.clauseKeys handler.clauses).Nodup)
      (declarations : Declarations operations policy contracts world (fun _ => none) residual handler.effectInst answer handler.clauses (tables handler) plans)
      (recipes : evidence (required handler) plans)
      (capabilities : ClausesUse policy handler.clauses)
      (modes : SourceTemplates.ClauseModes handler.clauses (tables handler)) :
      Frame (evidence := evidence) operations policy contracts tables families required world (.handler handler) answer answer [] (.request [] [])
        (.handler handler.effectInst (tables handler) (families handler))
        (fun rest => .handler (required handler) rest) (handler.effectInst :: residual) residual
  | cell (scopeKnown : ScopedPorts.ScopeKnown contracts.erase.erase.ports.types caller)
      (noEscape : identity ∉ (ScopedPorts.eraseType answer).resources)
      (annotation : result.erase.erase.port = ScopedPorts.eraseType answer)
      (interface : ScopedPorts.EffectFrame operations.erase.erase.ports contracts.erase.erase.ports world (.cell identity payload caller answer) incoming outgoing) :
      Frame (evidence := evidence) operations policy contracts tables families required world (.cell identity payload caller answer) result result [] (.request [] []) (.cell identity) (fun rest => .cell rest) incoming outgoing
  | armed {callbackPlan : Plan callbackDep} (scopeKnown : ScopedPorts.ScopeKnown contracts.erase.erase.ports.types action.scope)
      (callback : ValueSummary operations policy contracts world (fun _ => none) [] action.action (.function .unit .unit action.requests latent (signature callbackPlan)))
      (annotation : result.erase.erase.port = ScopedPorts.eraseType action.answer)
      (interface : ScopedPorts.EffectFrame operations.erase.erase.ports contracts.erase.erase.ports world (.armed action) incoming outgoing) :
      Frame (evidence := evidence) operations policy contracts tables families required world (.armed action) result result [] (.request [] (qualify true latent))
        (.cleanup action.requests callbackDep) (fun rest => .cleanup rest) incoming outgoing
  | running {callbackPlan : Plan callbackDep} (scopeKnown : ScopedPorts.ScopeKnown contracts.erase.erase.ports.types action.scope)
      (callback : ValueSummary operations policy contracts world (fun _ => none) [] action.action (.function .unit .unit action.requests latent (signature callbackPlan)))
      (saved : ValueSummary operations policy contracts world (fun _ => none) [] value result)
      (annotation : result.erase.erase.port = ScopedPorts.eraseType action.answer)
      (interface : ScopedPorts.EffectFrame operations.erase.erase.ports contracts.erase.erase.ports world (.running action value closed) incoming outgoing) :
      Frame (evidence := evidence) operations policy contracts tables families required world (.running action value closed) .unit result [] (.request [] []) .running (fun rest => .running rest) incoming outgoing
  | closing (scopeKnown : ScopedPorts.ScopeKnown contracts.erase.erase.ports.types caller)
      (interface : ScopedPorts.EffectFrame operations.erase.erase.ports contracts.erase.erase.ports world (.closing identity caller) incoming outgoing) :
      Frame (evidence := evidence) operations policy contracts tables families required world (.closing identity caller) .unit .unit [] (.request [] []) .running (fun rest => .running rest) incoming outgoing
  | retiring (known : contracts owner = some contract)
      (interface : ScopedPorts.EffectFrame operations.erase.erase.ports contracts.erase.erase.ports world (.retiring owner) incoming outgoing) :
      Frame (evidence := evidence) operations policy contracts tables families required world (.retiring owner) .unit .unit [owner] (.retire owner) .running (fun rest => .running rest) incoming outgoing

theorem Frame.erase
    (frame : Frame (evidence := evidence) operations policy contracts tables families required world entry input output demand requirements layer decorate incoming outgoing) :
    SourceDependencyFrames.Frame operations.erase policy contracts.erase tables families world entry input.erase output.erase
      demand requirements layer incoming outgoing := by
  cases frame with
  | plain context scope inputAnnotation outputAnnotation =>
      exact .plain (SourcePlannedSources.context_erase context) scope inputAnnotation outputAnnotation
  | handler scope annotation clauses coverage unique declarations recipes capabilities modes =>
      exact .handler scope annotation clauses coverage unique (declarations_erase declarations) capabilities modes
  | cell scopeKnown noEscape annotation interface => exact .cell scopeKnown noEscape annotation interface
  | armed scopeKnown callback annotation interface => exact .armed scopeKnown (SourcePlannedSources.expression_erase callback) annotation interface
  | running scopeKnown callback saved annotation interface =>
      exact .running scopeKnown (SourcePlannedSources.expression_erase callback) (SourcePlannedSources.expression_erase saved) annotation interface
  | closing scopeKnown interface => exact .closing scopeKnown interface
  | retiring known interface => exact .retiring (SourcePlannedSources.contract_erase_known known) interface

theorem Frame.matches
    (frame : Frame (evidence := evidence) operations policy contracts tables families required world entry input output demand requirements layer decorate incoming outgoing)
    (tail : SourceContextualHintChecking.Matches tables families required hints stack) :
    SourceContextualHintChecking.Matches tables families required (decorate hints) (.push entry stack) := by
  cases frame
  all_goals first | exact .plain tail | exact .handler tail | exact .cell tail | exact .cleanup tail |
    exact .running tail | exact .closing tail | exact .retiring tail

inductive Segment (operations : Operations) (policy : Syntax.TicketPolicy) (contracts : Contracts)
    (tables : CallableProtectionFrames.Tables) (families : Families) (required : SourceContextualRechecking.Required) (actions : Syntax.UsageTickets) (world : List Nat) :
    Stack → Value → Value → (demand : List Nat) → Requirements demand → Store → {dependencyScope : DependencyScope} → Hints dependencyScope →
      List Instance → List Instance → (evidence : optParam DeclarationEvidence recipeEvidence) → Prop where
  | nil (bound : incoming ⊆ outgoing) :
      Segment (evidence := evidence) operations policy contracts tables families required actions world .nil result result [] (.request [] []) [] .nil incoming outgoing
  | push (head : Frame (evidence := evidence) operations policy contracts tables families required world entry input middle headDemand first layer decorate inner outer)
      (tail : Segment (evidence := evidence) operations policy contracts tables families required actions world rest middle output tailDemand second records restHints outer outgoing)
      (bound : incoming ⊆ inner) :
      Segment (evidence := evidence) operations policy contracts tables families required actions world (.push entry rest) input output
        (headDemand ++ tailDemand) (.sequence (first.prepend (OwnerPhases.ofStack tables rest)) second) records (decorate restHints) incoming outgoing
  | live (known : contracts owner = some contract) (actionKnown : actions owner = some rights)
      (inputAnnotation : contract.input.erase.erase.port = ScopedPorts.eraseType inputType)
      (answerAnnotation : contract.answer.erase.erase.port = ScopedPorts.eraseType answerType)
      (scope : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports caller)
      (held : contract.held = ProtectionContexts.protectedMode capture.erase)
      (saved : Segment (evidence := evidence) operations policy contracts tables families required actions world
        capture contract.input contract.answer contract.resumeDemand body nested savedHints [] savedBoundary)
      (savedBound : rights.resume = true → savedBoundary ⊆ contract.resumeEffects)
      (tail : Segment (evidence := evidence) operations policy contracts tables families required actions world rest contract.answer output
        demand requirements remaining restHints boundary outgoing)
      (resume : rights.resume = true → contract.resumeEffects ⊆ boundary)
      (close : rights.dispose = true → contract.closeEffects ⊆ boundary)
      (bound : incoming ⊆ boundary) :
      Segment (evidence := evidence) operations policy contracts tables families required actions world (.live owner inputType answerType capture caller rest)
        contract.answer output demand (.sequence (.spent owner) requirements)
        ((⟨owner, .resume⟩, ⟨contract.resumeDemand, body⟩) :: (nested ++ remaining)) (.live (owner := owner) savedHints restHints) incoming outgoing
  | spent (known : contracts owner = some contract)
      (annotation : contract.answer.erase.erase.port = ScopedPorts.eraseType answerType)
      (scope : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports caller)
      (tail : Segment (evidence := evidence) operations policy contracts tables families required actions world rest contract.answer output
        demand requirements records restHints boundary outgoing)
      (bound : incoming ⊆ boundary) :
      Segment (evidence := evidence) operations policy contracts tables families required actions world (.spent owner answerType caller rest) contract.answer output
        demand (.sequence (.spent owner) requirements) records (.spent (owner := owner) restHints) incoming outgoing

theorem Segment.erase {hints : Hints dependencyScope}
    (segment : Segment (evidence := evidence) operations policy contracts tables families required actions world stack input output demand requirements records hints incoming outgoing) :
    SourceDependencyFrames.Segment operations.erase policy contracts.erase tables families actions world stack input.erase output.erase
      demand requirements records dependencyScope incoming outgoing := by
  induction segment with
  | nil bound => exact .nil bound
  | push head tail bound ih => exact .push head.erase ih bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live (SourcePlannedSources.contract_erase_known known) actionKnown inputAnnotation answerAnnotation scope held
        ihSaved savedBound ihTail resume close bound
  | spent known annotation scope tail bound ih =>
      exact .spent (SourcePlannedSources.contract_erase_known known) annotation scope ih bound

theorem Segment.matches
    (segment : Segment (evidence := evidence) operations policy contracts tables families required actions world stack input output demand requirements records hints incoming outgoing) :
    SourceContextualHintChecking.Matches tables families required hints stack := by
  induction segment with
  | nil => exact .nil
  | push head tail bound ih => exact head.matches ih
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live ihSaved ihTail
  | spent known annotation scope tail bound ih => exact .spent ih

/-- Change only the declaration evidence. Source syntax, types and retained
plans are preserved; any local checks in the frame are unchanged. -/
theorem Frame.map_evidence
    (frame : Frame (evidence := evidence) operations policy contracts tables families required world entry input output demand requirements layer decorate incoming outgoing)
    (changed : ∀ needed {clauses families} (plans : ClausePlans clauses families),
      evidence needed plans → nextEvidence needed plans) :
    Frame (evidence := nextEvidence) operations policy contracts tables families required world entry input output demand requirements layer decorate incoming outgoing := by
  cases frame
  all_goals constructor <;> first | assumption | exact changed _ _ ‹_›

theorem Segment.map_evidence
    (segment : Segment (evidence := evidence) operations policy contracts tables families required actions world stack input output demand requirements records hints incoming outgoing)
    (changed : ∀ needed {clauses families} (plans : ClausePlans clauses families),
      evidence needed plans → nextEvidence needed plans) :
    Segment (evidence := nextEvidence) operations policy contracts tables families required actions world stack input output demand requirements records hints incoming outgoing := by
  induction segment with
  | nil bound => exact .nil bound
  | push head tail bound ih => exact .push (head.map_evidence changed) (ih changed) bound
  | live known actionKnown inputAnnotation answerAnnotation scope held saved savedBound tail resume close bound ihSaved ihTail =>
      exact .live known actionKnown inputAnnotation answerAnnotation scope held (ihSaved changed) savedBound (ihTail changed) resume close bound
  | spent known annotation scope tail bound ih => exact .spent known annotation scope (ih changed) bound

end Ash.OneShot.SourcePlannedFrames

#print axioms Ash.OneShot.SourcePlannedFrames.offer_erase
#print axioms Ash.OneShot.SourcePlannedFrames.declarations_erase
#print axioms Ash.OneShot.SourcePlannedFrames.Frame.erase
#print axioms Ash.OneShot.SourcePlannedFrames.Frame.matches
#print axioms Ash.OneShot.SourcePlannedFrames.Segment.erase
#print axioms Ash.OneShot.SourcePlannedFrames.Segment.matches

#print axioms Ash.OneShot.SourcePlannedFrames.Frame.map_evidence
#print axioms Ash.OneShot.SourcePlannedFrames.Segment.map_evidence
