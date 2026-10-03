import CoreCallableRestoredChecking

namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract Environment)
open CoreCallableContractAdmission CoreCallableReceiverRefinement
open SourceDeclarationPlans (Plan ClausePlans)
open SourcePlanSignatures (signature clauseSignatures)
open SourceDependencyAnnotations (Dependencies RowAnnotation)
open SourceDependencyChecks.Lexical (ReturnHints)
open RecursiveRequirements (Requirements Checked)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy)

section
variable [DeclarationPolicy]

/-- Install the original complete declarations and body at the actually fresh
current handler identity. Whole and domain authentication retain their mode. -/
theorem Site.enter_handler_at
    {hints : ReturnHints receiving} {context : Context hints}
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.handle (Instantiation.freezeEffect effect) body arms) runtimeScope stack result final context root)
    (fresh : activation ∉ installations) :
    ∃ handler : HandlerData, ∃ residual : List Instance,
    ∃ table : List (Nat × ClauseContract),
    ∃ families : SourceDependencyAnnotations.ClauseDependencies,
    ∃ plans : ClausePlans handler.clauses families, ∃ rows : ClauseRows (clauseSignatures plans),
    ∃ _next : Site globals outward world (effect :: residual) actions phases budget ambient
      (installations ++ [activation]) body runtimeScope (.push (.handler handler) stack)
      result final (.handler (effect := effect) (table := table) activation rows context) root,
      handler.activation = activation ∧ handler.scope = runtimeScope ∧
      handler.effectInst = effect ∧ handler.clauses = arms ∧
      HandlerSource globals outward world residual handler result table
        plans rows
        (actualReceiver world receiving ambient) := by
  rcases site with ⟨sourceDemand, requirements, dependencies, plan, rows, bound, current,
    received, certificate, certificateChecked, pending, retained, retainedChecked, accounting,
    annotated, row, annotation, checked, bounded⟩
  generalize frozen : Instantiation.freezeEffect effect = syntaxEffect at current
  obtain ⟨lexical, sameEnvironment, authentication⟩ := current.authentication
  cases authentication with
  | checked currentSupport hereditary =>
    cases hereditary
    all_goals first | contradiction | skip
    all_goals rename_i effectOriginal residual bodyDependencies bodyPlan bodyRows table families required admitted plans declarationRows capabilities coverage unique modes recipes clauses declarationSource bodyReq bodySource declarationsAuth bodyAuth
    all_goals cases freeze_effect_injective frozen
    all_goals
      let handler : HandlerData := ⟨activation, effect, arms, runtimeScope,
        runtimeType result, ScopedPorts.clauses_have_ticket_barrier clauses⟩
      have history : activation :: installations ⊆ installations ++ [activation] := by
        intro name member
        rcases List.mem_cons.mp member with same | old
        · exact same ▸ List.mem_append_right _ List.mem_cons_self
        · exact List.mem_append_left _ old
      obtain ⟨bodyCertificate, bodyChecked⟩ := certificateChecked.handler_body fresh
      let frame : HandlerSource globals outward world _ handler result _ _ _
          (actualReceiver world receiving ambient) := by
        first
        | exact HandlerSource.of_whole (runtimeType_port result) modes declarationSource
            ⟨lexical, sameEnvironment, declarationsAuth⟩
        | exact HandlerSource.of_domain (runtimeType_port result) modes declarationSource
            ⟨lexical, sameEnvironment, declarationsAuth⟩
      let next : Site globals outward world _ actions phases budget ambient
          (installations ++ [activation]) body runtimeScope (.push (.handler handler) stack)
          result final (.handler (effect := effect) activation _ context) root := {
        sourceDemand := _, requirements := _, dependencies := _, plan := _, rows := _,
        bound := actualReceiver world receiving ambient,
        current := ⟨bodySource, by simpa only [sameEnvironment] using bodyAuth.current_support,
          actualReceiver.issued, ⟨lexical, sameEnvironment, bodyAuth⟩, actualReceiver.issued⟩,
        received := actualReceiver.received,
        certificate := bodyCertificate.installations_mono history,
        certificateChecked := bodyChecked.installations_mono history,
        pending := .handler frame admitted pending,
        retained := .handler (retained.installations_mono (List.subset_append_left _ _)),
        retainedChecked := .handler (retainedChecked.installations_mono (List.subset_append_left _ _)),
        accounting := (accounting.enter_handler fresh).mono (List.Subset.refl _) history,
        annotated := annotated, row := row, annotation := annotation, checked := checked, bounded := bounded }
      exact ⟨handler, _, _, _, _, _, next, rfl, rfl, rfl, rfl, frame⟩

end
#print axioms Site.enter_handler_at
end Ash.OneShot.CoreCallableContractExecution
