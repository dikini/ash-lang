import SourceScheduledPreservation

/-! M4 progress starts from the current executable invariant.  The existing
progress theorem is indexed by the older retained `Run`; this file keeps the
current `InstallationState` boundary explicit and first supplies the reusable
syntax classification for it.  No successor validity is assumed here. -/

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations)
open RecursiveRequirements (Requirements)

open ScopedPortProgress (CurrentForm)
open RecursiveExpressions (Ready)

private theorem auth_current_form
    {operations : SourcePlannedTyping.Operations} {policy : Syntax.TicketPolicy}
    {ports : OperationRows operations} {contracts : SourcePlannedTyping.Contracts}
    {owners : ContractRows contracts}
    {environmentRows : EnvironmentRows (fun _ => none)} {world : List Nat}
    {allowed : List Instance} {runtimeScope : Execution.Scope}
    {code : Code} {result : SourcePlannedTyping.Value} {demand : List Nat}
    {requirements : Requirements demand}
    {dependencies : SourceDependencyAnnotations.Dependencies}
    {checking : SourcePlanSignatures.Signature dependencies}
    {source : SourcePlannedSources.Expression operations policy contracts world allowed runtimeScope
      (fun _ => none) code result demand requirements checking}
    {resultRows : ValueRows result} {rows : Rows checking}
    (authenticated : Auth operations policy ports owners environmentRows source resultRows rows) :
    CurrentForm code := by
  cases code with
  | unit => exact .value trivial
  | boolean => exact .value trivial
  | integer => exact .value trivial
  | «variable» => cases authenticated <;> simp_all
  | resourceRef => cases authenticated <;> exact .value trivial
  | lambda => exact .value trivial
  | pair left right =>
      by_cases leftValue : left.IsValue
      · by_cases rightValue : right.IsValue
        · exact .value ⟨leftValue, rightValue⟩
        · exact .focus (.pairRight leftValue rightValue)
      · exact .focus (.pairLeft leftValue)
  | app function argument =>
      by_cases functionValue : function.IsValue
      · by_cases argumentValue : argument.IsValue
        · exact .app functionValue argumentValue
        · exact .focus (.appArgument functionValue argumentValue)
      · exact .focus (.appFunction functionValue)
  | bind parameter initializer body =>
      by_cases initializerValue : initializer.IsValue
      · exact .bind initializerValue
      · exact .focus (.bind initializerValue)
  | branch condition yes no =>
      by_cases conditionValue : condition.IsValue
      · exact .branch conditionValue
      · exact .focus (.branch conditionValue)
  | perform effect operation operand =>
      cases authenticated with
      | perform operandChecked =>
          by_cases operandValue : operand.IsValue
          · exact .request operandValue
          · exact .focus (.perform operandValue)
  | handle effect body clauses => exact .handler
  | resume binder operand =>
      by_cases operandValue : operand.IsValue
      · exact .resume operandValue
      · exact .focus (.resume operandValue)
  | discard binder => exact .discard
  | resource binder initializer body =>
      by_cases initializerValue : initializer.IsValue
      · exact .resource initializerValue
      · exact .focus (.resource initializerValue)
  | cleanup callback body =>
      by_cases callbackValue : callback.IsValue
      · exact .cleanup callbackValue
      · exact .focus (.cleanup callbackValue)

private theorem site_current_form
    (site : ExecutionSite ambient operations policy contracts tables families required outward actions phases world installations
      resumes budget ports owners emptyRows output outputRows) :
    CurrentForm site.expression := by
  exact auth_current_form site.current.previous.authenticated

/-- The authenticated current source determines the exhaustive expression
form of an executable evaluation site.  This is the current-state adapter for
the older `ScopedPortProgress.typed_current_form` lemma. -/
theorem ExecutableSource.current_form
    (source : ExecutableSource ambient operations policy contracts tables families required outward actions annotations
      world installations resumes annotatedStore budget ports owners emptyRows output outputRows machine)
    (shape : machine = .eval ⟨code, runtimeScope, stack⟩) :
    CurrentForm code := by
  cases source with
  | eval site phaseAgreement rooted bound annotation checked bounded =>
      have fields := LexicalUnwind.Machine.eval.inj shape
      obtain ⟨expressionEq, runtimeEq, stackEq⟩ := ScopedExecution.Configuration.mk.inj fields
      simpa only [expressionEq] using site_current_form site

  | unwind pending coherent certificate waiting bound annotation checked bounded resourceChecked =>
      cases shape

theorem InstallationState.current_form
    (valid : Valid policy outward ambient budget ports emptyRows output outputRows snapshot)
    (shape : snapshot.run.execution.machine =
      .eval ⟨code, runtimeScope, stack⟩) :
    CurrentForm code :=
  Preservation.ExecutableSource.current_form (source := valid.unpack.source) shape

/-- A supplied ready-computation witness is already enough to make the
corresponding M3 stable request available.  This is intentionally a local
adapter: it does not manufacture the raw step or claim validity of its
successor. -/
theorem request_of_ready_computation
    {operations : Operations} {snapshot : Snapshot operations}
    {code after : Code} {runtimeScope : Scope} {stack : ScopedExecution.Stack}
    {issued completed : List Owner} {actions : Syntax.UsageTickets}
    (shape : snapshot.run =
      ⟨⟨.eval ⟨code, runtimeScope, stack⟩, issued, completed⟩, actions⟩)
    (ready : Ready code)
    (raw : RawStep ⟨code, runtimeScope, stack⟩
      ⟨after, runtimeScope, stack⟩ [] []) :
    ∃ request : Request snapshot, ∃ expected : Snapshot operations,
      ∃ step : Stable.Step operations snapshot expected,
        request = .stable expected step := by
  cases snapshot with
  | mk contracts tables families required annotations world history resumes disposals annotatedStore owners run =>
      cases shape
      let successor : Snapshot operations :=
        { contracts := contracts, tables := tables, families := families, required := required,
          annotations := annotations, world := world, history := history, resumes := resumes,
          disposals := disposals, annotatedStore := annotatedStore, owners := owners,
          run := ⟨⟨.eval ⟨after, runtimeScope, stack⟩, issued, completed⟩, actions⟩ }
      have step : Stable.Step operations
          ({ contracts := contracts, tables := tables, families := families, required := required,
             annotations := annotations, world := world, history := history, resumes := resumes,
             disposals := disposals, annotatedStore := annotatedStore, owners := owners,
             run := ⟨⟨.eval ⟨code, runtimeScope, stack⟩, issued, completed⟩, actions⟩ })
          successor := by
        dsimp [successor]
        exact .computation (snapshot :=
          { contracts := contracts, tables := tables, families := families, required := required,
            annotations := annotations, world := world, history := history, resumes := resumes,
            disposals := disposals, annotatedStore := annotatedStore, owners := owners,
            run := ⟨⟨.eval ⟨code, runtimeScope, stack⟩, issued, completed⟩, actions⟩ }) ready raw
      exact ⟨.stable successor step, successor, step, rfl⟩

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.ExecutableSource.current_form
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.InstallationState.current_form
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation.request_of_ready_computation

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InstallationSupport.Preservation
