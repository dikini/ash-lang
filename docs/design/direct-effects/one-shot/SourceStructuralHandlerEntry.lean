import SourceAnnotatedRuntimeTyping

/-! Install the declaration evidence carried by the structural handler check
into the actual typed runtime frame. This boundary is independent of the old
recipe grammar. Whole-state preservation and a sound concrete declaration
policy remain separate obligations. -/
namespace Ash.OneShot.SourceStructuralHandlerEntry
open ScopedExpressions ScopedExecution
open SourceDeclarationPlans (Plan ClausePlans)
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

/-- Installation transfers source evidence to the actual clause plans whose
control signature was authenticated by expression typing. This is a law of
declaration judgments, not a premise about execution or successor validity. -/
class DeclarationRetention (admission : SourceScheduledChecks.DeclarationPolicy)
    (evidence : SourcePlannedFrames.DeclarationEvidence) (outward : List Instance) : Prop where
  retain : ∀ {before after families required}
    {first : ClausePlans before families} {second : ClausePlans after families},
    admission.accepts outward required first →
    SourcePlanSignatures.clauseSignatures first = SourcePlanSignatures.clauseSignatures second →
    evidence required second

/-- The current structural recipe judgment already has the required source
transport proof. Broader judgments must supply their own proved instance. -/
instance recipeRetention (outward : List Instance) :
    DeclarationRetention SourceScheduledChecks.recipePolicy SourcePlannedFrames.recipeEvidence outward where
  retain := fun admitted same => SourcePlannedRecipeDeclarations.Declarations.signature_congr admitted same

variable [admission : SourceScheduledChecks.DeclarationPolicy]
variable [certification : SourcePlannedChecks.DeclarationPolicy]

/-- Install the authenticated actual clause plans and retain their declaration
evidence. The body keeps its original structural check under that handler. -/
theorem handler_frame
    [DeclarationRetention admission evidence outward] {handler : SourceAnnotatedRuntime.Handler}
    {hints : Hints receivingScope} {forest : Forest hints}
    {plans : ClausePlans handler.clauses.erase (families handler.erase)}
    {sourcePlans : ClausePlans sourceClauses (families handler.erase)}
    {body : Plan dependencies}
    (checked : SourceScheduledChecks.Local outward actions phases world
      (.handler (effect := handler.effectInst) (table := tables handler.erase)
        (required handler.erase) sourcePlans body) forest)
    (same : SourcePlanSignatures.clauseSignatures sourcePlans = SourcePlanSignatures.clauseSignatures plans)
    (scope : ScopedPorts.EffectScopeKnown contracts.erase.erase.ports handler.scope)
    (annotation : answer.erase.erase.port = ScopedPorts.eraseType handler.answer)
    (clauses : ScopedPorts.ClausesTyped operations.erase.erase.ports world
      SourceDependencyAnnotations.Environment.empty.erase.ports handler.effectInst
      answer.erase.erase.port residual handler.clauses.erase)
    (coverage : ScopedPorts.Covers operations.erase.erase.ports handler.effectInst handler.clauses.erase)
    (unique : (ScopedTyping.clauseKeys handler.clauses.erase).Nodup)
    (declarations : SourceAnnotatedSources.Declarations operations policy contracts world
      (fun _ => none) residual handler.effectInst answer handler.clauses (tables handler.erase) plans)
    (capabilities : ClausesUse policy handler.clauses.erase)
    (modes : SourceTemplates.ClauseModes handler.clauses.erase (tables handler.erase)) :
    SourceAnnotatedRuntimeTyping.Frame (evidence := evidence)
      operations policy contracts tables families required outward actions phases world (forest.append .nil)
      (.handler handler) answer answer [] (.request [] [])
      (.handler handler.effectInst (tables handler.erase) (families handler.erase))
      (fun rest => .handler (required handler.erase) rest) (fun rest => .handler rest)
      (handler.effectInst :: residual) residual ∧
    SourceScheduledChecks.Local outward actions phases world body
      (.handler (effect := handler.effectInst) (table := tables handler.erase)
        (families := families handler.erase) (required := required handler.erase) forest) := by
  cases checked with
  | handler admitted certified supplied body =>
      exact ⟨.handler scope annotation clauses coverage unique declarations (DeclarationRetention.retain admitted same)
        (by simpa only [SourceDependencyProjection.scope_append_nil] using supplied) capabilities modes, body⟩

end Ash.OneShot.SourceStructuralHandlerEntry

#print axioms Ash.OneShot.SourceStructuralHandlerEntry.handler_frame

#print axioms Ash.OneShot.SourceStructuralHandlerEntry.recipeRetention
