import SourceConsumingBoundCongruence
import SourceStructuralHandlerEntry

/-! Install the concrete structural declaration judgment in the existing typed
handler frame. The source derivation supplies clause-local operation checks;
actual captured-interface bounds still need authentication by request typing. -/
namespace Ash.OneShot.SourceConsumingDeclarationEntry
open SourceDeclarationPlans (ClausePlans)
open SourceContextualHints (Hints checkRequirements)
open SourceRetainedPlans (Forest)
open SourceConsumingClauseAnnotations (Declarations ClauseBounds Bounded)

variable [nested : SourceScheduledCapabilityAnnotations.DeclarationPolicy]

/-- Evidence has a structural source derivation for these exact plans. It
contains no whole-body scheduling or successful future-capture predicate. -/
def evidence (world : List Nat) : SourcePlannedFrames.DeclarationEvidence :=
  fun required {_ _} plans => ∃ bounds : ClauseBounds plans, ∃ annotated : Declarations world plans,
    Bounded bounds annotated required

/-- The existing frame constructor retains the source judgment and the finite
operation check at the actual waiting scope. Rich typing and clause modes stay
independent, exactly as at the existing handler-entry boundary. -/
theorem install [admission : SourceScheduledChecks.DeclarationPolicy]
    [certification : SourcePlannedChecks.DeclarationPolicy] {handler : SourceAnnotatedRuntime.Handler}
    {hints : Hints receivingScope} {forest : Forest hints}
    {plans : ClausePlans handler.clauses.erase (families handler.erase)}
    (bounds : ClauseBounds plans) (annotated : Declarations world plans)
    (admitted : Bounded bounds annotated (required handler.erase))
    (supplied : checkRequirements receivingScope (required handler.erase) = true)
    (scope : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports handler.scope)
    (annotation : answer.erase.erase.port = ScopedPorts.eraseType handler.answer)
    (clauses : ScopedPorts.ClausesTyped operations.erase.erase.ports world
      SourceDependencyAnnotations.Environment.empty.erase.ports handler.effectInst
      answer.erase.erase.port residual handler.clauses.erase)
    (coverage : ScopedPorts.Covers operations.erase.erase.ports handler.effectInst handler.clauses.erase)
    (unique : (ScopedTyping.clauseKeys handler.clauses.erase).Nodup)
    (source : SourceAnnotatedSources.Declarations operations policy contracts world
      (fun _ => none) residual handler.effectInst answer handler.clauses (tables handler.erase) plans)
    (capabilities : ScopedExpressions.ClausesUse policy handler.clauses.erase)
    (modes : SourceTemplates.ClauseModes handler.clauses.erase (tables handler.erase)) :
    SourceAnnotatedRuntimeTyping.Frame (evidence := evidence world)
      operations policy contracts tables families required outward actions phases world forest
      (.handler handler) answer answer [] (.request [] [])
      (.handler handler.effectInst (tables handler.erase) (families handler.erase))
      (fun rest => .handler (required handler.erase) rest) (fun rest => .handler rest)
      (handler.effectInst :: residual) residual :=
  .handler scope annotation clauses coverage unique source ⟨bounds, annotated, admitted⟩ supplied capabilities modes

/-- Reuse source world weakening when a stored declaration is needed in a
larger resource world. This changes the evidence's index, not runtime dispatch. -/
theorem evidence_world_weaken (admitted : evidence world required plans) (larger : world ⊆ next) :
    evidence next required plans := by
  obtain ⟨bounds, annotated, checked⟩ := admitted
  exact ⟨bounds, annotated.world_weaken larger, checked.world_weaken larger⟩

theorem evidence_substitution (admitted : evidence world required plans) (isValue : value.IsValue) :
    evidence world required (SourcePlanSignatures.substituteClauses plans name value) := by
  obtain ⟨bounds, annotated, checked⟩ := admitted
  exact ⟨bounds.substitution name value, annotated.substitution name value, checked.substitution isValue⟩

/-- Actual clause plans may differ from the checking witnesses. Structural
transport derives their evidence while retaining the original bound values. -/
theorem evidence_signature_congr
    (transport : ∀ {before after families required}
      {first : ClausePlans before families} {second : ClausePlans after families},
      nested.accepts required first → SourcePlanSignatures.clauseSignatures first = SourcePlanSignatures.clauseSignatures second →
        nested.accepts required second)
    {first : ClausePlans before families} {second : ClausePlans after families}
    (admitted : evidence world required first)
    (same : SourcePlanSignatures.clauseSignatures first = SourcePlanSignatures.clauseSignatures second) :
    evidence world required second := by
  obtain ⟨bounds, annotated, checked⟩ := admitted
  obtain ⟨actual, preserved⟩ := checked.signature_congr transport same
  exact ⟨bounds.reindex second, actual, preserved⟩

end Ash.OneShot.SourceConsumingDeclarationEntry

#print axioms Ash.OneShot.SourceConsumingDeclarationEntry.install
#print axioms Ash.OneShot.SourceConsumingDeclarationEntry.evidence_world_weaken
#print axioms Ash.OneShot.SourceConsumingDeclarationEntry.evidence_substitution
#print axioms Ash.OneShot.SourceConsumingDeclarationEntry.evidence_signature_congr
