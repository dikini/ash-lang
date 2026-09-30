import CoreCallableContractAdmission

/-! Upper companion for a bounded current/plain-frame/builtin-reply migration.
It uses existing M4 certificates and accounting, but carries the new recursive
contract source instead of asserting legacy exact-body Auth. No back import
into the shared M4 module is required. -/
namespace Ash.OneShot.CoreCallableContractExecution
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies RowAnnotation)
open SourceDependencyChecks.Lexical (ReturnHints)
open RecursiveRequirements (Requirements Checked)
open CoreCallableContractSource (Contract Environment sequenceRows)
open CoreCallableContractAdmission (Globals Source Supported)
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open SourceScheduledCleanupInterfaces.Lexical.Recursive (annotateDisposals)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks (DeclarationPolicy Certified)

/-- These erasures retain the declared ports and latent scalar footprints,
without identifying a public signature with a lambda's private body signature. -/
def lowerOperations (globals : Globals) : CoherentSourceTypes.Operations :=
  fun effect operation => (globals.operations effect operation).map (fun pair =>
    (pair.1.value.erase.erase, pair.2.value.erase.erase))
def lowerEnvironment (environment : Environment) : CoherentSourceTypes.Environment :=
  fun name => (environment name).map (fun contract => contract.value.erase.erase)
@[simp] theorem lowerEnvironment_extend :
    lowerEnvironment (environment.extend name contract) =
      (lowerEnvironment environment).extend name contract.value.erase.erase := by
  funext other
  by_cases same : other = name <;> simp [lowerEnvironment, Environment.extend, CoherentSourceTypes.Environment.extend, same]

section
variable [DeclarationPolicy]
/-- Constructive lower scalar/type/effect source, useful at the M4 progress
consumer. This deliberately does not project into legacy Source/Auth. -/
theorem Source.lower (source : Source globals outward world allowed scope environment code contract demand requirements plan rows) :
    SourceTemplates.Expression (lowerOperations globals) globals.policy globals.owners.erase.erase world allowed scope
      (lowerEnvironment environment) code contract.value.erase.erase demand requirements := by
  induction source with
  | unit => exact .stable .unit
  | boolean => exact .stable .boolean
  | integer => exact .stable .integer
  | reference issued => exact .stable (.reference issued)
  | «variable» known formed => exact .stable (.variable (by simp [lowerEnvironment, known]) formed)
  | lambda body refinement bodyOutward latentBound publicCertified formed ih =>
      exact .lambda (by simpa using ih) bodyOutward formed
  | purePair left right ihL ihR => exact .purePair ihL ihR
  | pair left right ihL ihR => exact .pair ihL ihR
  | app function argument admitted publicCertified ihF ihA => exact .app ihF ihA admitted
  | bind initial body ihI ihB => exact .bind ihI (by simpa using ihB)
  | branch condition yes no same ihC ihY ihN => exact .branch ihC ihY ihN same
  | perform known admitted operand formed ih => exact .perform (by simp [lowerOperations, known]) admitted ih formed

/-- The actual saved bind suffix, including private recursive bodies and a
finite lexical support entry for the eventual value. That entry is independent
of the input's declared port; plugging must supply its authenticated bound. -/
structure FrameSource (globals : Globals) (outward : List Instance) (world : List Nat) (allowed : List Instance)
    (data : PlainData) (input output : Contract) (parameter : Nat) (body : Code)
    (demand : List Nat) (requirements : Requirements demand)
    {dependencies : Dependencies} (plan : Plan dependencies) (rows : Rows (signature plan))
    (inputBound bodyBound : List Nat) : Prop where
  position : data.context = ScopedExecution.Context.bind parameter body
  inputAnnotation : ScopedPorts.eraseType data.input = input.port
  outputAnnotation : ScopedPorts.eraseType data.output = output.port
  inputIssued : inputBound ⊆ world
  bodySource : CoreCallableContractAdmission.Supported globals outward world
    allowed data.scope (Environment.empty.extend parameter input)
    (ScopedPorts.Support.extend ScopedPorts.Support.empty parameter inputBound) body output demand requirements plan rows bodyBound


/-- A saved suffix is plugged using its own recursive evidence and the actual
returned value, with the same public input contract and finite support bound. -/
theorem FrameSource.plug
    (frame : FrameSource globals outward world allowed data input output parameter body demand requirements plan rows inputBound bodyBound)
    (valueSource : CoreCallableContractAdmission.Supported globals outward world allowed data.scope Environment.empty
      ScopedPorts.Support.empty value input valueDemand valueRequirements valuePlan valueRows inputBound)
    (closed : ClosedValue value) :
    CoreCallableContractAdmission.Supported globals outward world allowed data.scope Environment.empty ScopedPorts.Support.empty
      (body.subst parameter value) output demand requirements plan rows bodyBound ∧ Certified outward world plan :=
  ⟨frame.bodySource.substitution valueSource closed, frame.bodySource.source.certified⟩

/-- The bounded chain covers actual plain and cell frames, with common
contracts at every boundary. Handler and owner frames need additional cases. -/
inductive Pending (globals : Globals) (outward : List Instance) (world : List Nat) (allowed : List Instance) (ambient : List Nat) :
    Stack → Contract → Contract → {scope : SourceDependencyCapture.Scope} → {hints : ReturnHints scope} → Context hints → Prop where
  | nil : Pending globals outward world allowed ambient .nil input input .nil
  | plain
      (frame : FrameSource globals outward world allowed
        data input middle parameter body demand requirements plan rows inputBound bodyBound)
      (received : bodyBound ⊆ scope.visibleResources ++ ambient)
      (accepts : ∀ identity, identity ∈ world → identity ∈ scope.visibleResources ++ ambient → identity ∈ inputBound)
      (tail : Pending globals outward world allowed ambient stack middle output (context : Context (hints : ReturnHints scope))) :
      Pending globals outward world allowed ambient (.push (.plain data) stack) input output (.plain rows context)
  | cell (issued : identity ∈ world)
      (annotation : ScopedPorts.eraseType answer = input.port)
      (tail : Pending globals outward world allowed ambient stack input output context) :
      Pending globals outward world allowed ambient (.push (.cell identity payload caller answer) stack) input output (.cell (identity := identity) context)

/-- Updating a live physical cell preserves the recursive saved source exactly. -/
theorem Pending.cell_update (pending : Pending globals outward world allowed ambient before input output context)
    (updated : CellUpdate identity old new before after) : Pending globals outward world allowed ambient after input output context := by
  induction pending generalizing after with
  | nil => cases updated
  | plain frame received accepts tail ih => cases updated with
    | push miss next => exact .plain frame received accepts (ih next)
  | cell issued annotation tail ih => cases updated with
    | hit => exact .cell issued annotation tail
    | push miss next => exact .cell issued annotation (ih next)

/-- The same physical cell update and saved-frame relation identify the
actual contextual builtin receiver. No chosen response source is assumed. -/
theorem Pending.cell_update_builtin
    (pending : Pending globals outward world allowed ambient before input output context)
    (updated : CellUpdate identity old new before after) : select (.cell identity) 0 context = some (.builtin identity) := by
  induction pending generalizing after with
  | nil => cases updated
  | plain frame received accepts tail ih =>
      cases updated with
      | push miss next => simp only [select, ih next, Option.map_some, Selection.prepend]
  | cell issued annotation tail ih =>
      cases updated with
      | hit => simp [select]
      | push miss next =>
          simp only [select]
          split
          · rename_i same
            exact False.elim (miss (by simpa only [ExecFrame.erase, Frame.target] using congrArg some same.symm))
          · simp only [ih next, Option.map_some, Selection.prepend]

/-- Actual current source and saved recursive frames share one context. The
certificate, retained checks and executable root are existing M4 structures;
this replaces the legacy exact-body facet in the bounded companion only. -/
structure Site (globals : Globals) (outward : List Instance) (world : List Nat) (allowed : List Instance)
    (actions : Syntax.UsageTickets) (phases : OwnerPhaseTransitions.Phases) (budget : Footprint)
    (ambient installations : List Nat) (expression : Code) (runtimeScope : Execution.Scope) (stack : Stack)
    (result final : Contract) {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving}
    (context : Context hints) (root : Requirements rootDemand) where
  sourceDemand : List Nat
  requirements : Requirements sourceDemand
  dependencies : Dependencies
  plan : Plan dependencies
  rows : Rows (signature plan)
  bound : List Nat
  current : CoreCallableContractAdmission.Supported globals outward
    world allowed runtimeScope
    Environment.empty ScopedPorts.Support.empty expression result sourceDemand requirements plan rows bound
  received : bound ⊆ receiving.visibleResources ++ ambient
  certificate : SourceAdmission.Code outward actions budget phases
    world installations rows context
  certificateChecked : InstallationSupport.CodeChecked ambient outward certificate
  pending : Pending globals outward world allowed ambient stack result final context
  retained : SourceAdmission.Pending outward actions budget phases
    world installations context .nil .ordinary .ordinary
  retainedChecked : InstallationSupport.PendingChecked ambient outward retained
  accounting : Accounting.Run
    world installations rows context root
  annotated : Requirements rootDemand
  row : Footprint
  annotation : RowAnnotation root annotated
  checked : Checked [] [] phases (annotateDisposals annotated) row
  bounded : row ⊆ budget

theorem Site.certified (site : Site globals outward world allowed actions phases budget ambient installations expression runtimeScope stack result final context root) :
    Certified outward world site.plan := site.current.source.certified

/-- Runtime port annotations erase to the same common declared contract.
Retained support is deliberately checked in separate lexical fields. -/
def runtimeType : Contract → Ty
  | .unit => .unit
  | .boolean => .boolean
  | .integer => .integer
  | .reference identity => .reference identity
  | .pair left right => .product (runtimeType left) (runtimeType right)
  | .function input output requests _ _ _ => .function (runtimeType input) (runtimeType output) requests []
omit [DeclarationPolicy] in
theorem runtimeType_port (contract : Contract) : ScopedPorts.eraseType (runtimeType contract) = contract.port := by
  induction contract with
  | unit | boolean | integer | reference => rfl
  | pair first second ihL ihR => simp [runtimeType, ScopedPorts.eraseType, Contract.port, Contract.value, SourcePlannedTyping.Value.erase,
      SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port, ihL, ihR]
  | function input output requests latent plan rows ihI ihO => simp [runtimeType, ScopedPorts.eraseType, Contract.port, Contract.value,
      SourcePlannedTyping.Value.erase, SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port, ihI, ihO]

omit [DeclarationPolicy] in
private theorem empty_extend (parameter : Nat) : ScopedPorts.Support.extend ScopedPorts.Support.empty parameter [] = ScopedPorts.Support.empty := by
  funext other
  simp [ScopedPorts.Support.extend, ScopedPorts.Support.empty]

omit [DeclarationPolicy] in
private theorem finite_bounds {environment : ScopedPorts.Support.Env} {dependencies : List Syntax.Dependency} {bound : List Nat}
    (resources : Syntax.resourceDependencies dependencies ⊆ bound)
    (variables : ∀ name, environment name ⊆ bound) : SourceSupport.Bounds environment dependencies bound := by
  induction dependencies with
  | nil => exact .nil
  | cons dependency rest ih =>
      have tail : Syntax.resourceDependencies rest ⊆ bound := by
        intro identity member
        exact resources (Syntax.mem_resourceDependencies.mpr (List.mem_cons_of_mem _ (Syntax.mem_resourceDependencies.mp member)))
      cases dependency with
      | resource identity => exact .resource (resources (by simp [Syntax.resourceDependencies])) (ih tail)
      | «variable» name => exact .variable (variables name) (ih tail)
      | ticket owner => exact .ticket (ih tail)

/-- Actual bind focus constructs its child and saved suffix from the same
recursive current source. Translation is finite static runtime-frame data. -/
theorem Site.focus_bind {receiving : SourceDependencyCapture.Scope} {hints : ReturnHints receiving} {context : Context hints}
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.bind parameter initializer body) runtimeScope stack output final context root)
    (notValue : ¬ initializer.IsValue)
    (translated : runtimeScope.translate (ScopedExecution.Context.bind parameter body).dependencies = some []) :
    ∃ (input : Contract) (data : PlainData) (restDependencies : Dependencies) (restPlan : Plan restDependencies)
      (restRows : Rows (signature restPlan)),
      data.context = .bind parameter body ∧ data.scope = runtimeScope ∧
      ∃ _next : Site globals outward world allowed actions phases budget ambient installations initializer runtimeScope
        (.push (.plain data) stack) input final (.plain restRows context) root,
        RawStep ⟨.bind parameter initializer body, runtimeScope, stack⟩ ⟨initializer, runtimeScope, .push (.plain data) stack⟩ [] [] := by
  rcases site with ⟨sourceDemand, requirements, dependencies, plan, rows, bound, current, received, certificate, certificateChecked,
    pending, retained, retainedChecked, accounting, annotated, row, annotation, checked, bounded⟩
  rcases current with ⟨source, support, issued⟩
  cases source with
  | bind initialSource bodySource =>
      rename_i input initialDemand initialReq initialDependencies initialPlan initialRows bodyDemand bodyReq bodyDependencies bodyPlan bodyRows
      let data : PlainData := ⟨.bind parameter body, runtimeScope, runtimeType input, runtimeType output, [], translated⟩
      let receiverBound := (receiving.visibleResources ++ ambient).filter (fun identity => identity ∈ world)
      have accepts : ∀ identity, identity ∈ world → identity ∈ receiving.visibleResources ++ ambient → identity ∈ receiverBound := by
        intro identity historical visible
        exact List.mem_filter.mpr ⟨visible, by simpa using historical⟩
      have receiverIssued : receiverBound ⊆ world := by
        intro identity member
        exact of_decide_eq_true (List.mem_filter.mp member).2
      have receiverReceived : receiverBound ⊆ receiving.visibleResources ++ ambient := fun _ member => (List.mem_filter.mp member).1
      have currentBound : bound ⊆ receiverBound := fun identity member => accepts identity (issued member) (received member)
      have childSupport : SourceSupport.Bounds ScopedPorts.Support.empty initializer.dependencies receiverBound := by
        apply finite_bounds
        · intro identity member
          apply currentBound
          apply support.resources
          exact Syntax.mem_resourceDependencies.mpr (List.mem_append_left _ (Syntax.mem_resourceDependencies.mp member))
        · intro name; simp [ScopedPorts.Support.empty]
      have bodySupport : SourceSupport.Bounds (ScopedPorts.Support.extend ScopedPorts.Support.empty parameter receiverBound) body.dependencies receiverBound := by
        apply finite_bounds
        · intro identity member
          apply currentBound
          apply support.resources
          exact Syntax.mem_resourceDependencies.mpr (List.mem_append_right _
            (Syntax.mem_without.mpr ⟨Syntax.mem_resourceDependencies.mp member, by simp⟩))
        · intro name
          by_cases same : name = parameter
          · simp [ScopedPorts.Support.extend, same]
          · simp [ScopedPorts.Support.extend, ScopedPorts.Support.empty, same]
      let frame : FrameSource globals outward world allowed data input output parameter body bodyDemand bodyReq bodyPlan bodyRows receiverBound receiverBound :=
        ⟨rfl, runtimeType_port _, runtimeType_port _, receiverIssued, ⟨bodySource, bodySupport, receiverIssued⟩⟩
      have split : FocusRows (sequenceRows initialRows bodyRows) initialRows bodyRows := .sequence
      obtain ⟨childCertificate, restCertificate⟩ := split.source_certificate certificate
      obtain ⟨childChecked, restChecked⟩ := InstallationSupport.focus_rows split certificateChecked
      let nextRetained : SourceAdmission.Pending outward actions budget phases world installations (.plain bodyRows context) .nil .ordinary .ordinary :=
        .plain (restCertificate.reindex_context context.append_nil_pack.symm) retained
      let next : Site globals outward world allowed actions phases budget ambient installations initializer runtimeScope
        (.push (.plain data) stack) input final (.plain bodyRows context) root :=
        { sourceDemand := initialDemand, requirements := initialReq, dependencies := initialDependencies, plan := initialPlan, rows := initialRows,
          bound := receiverBound, current := ⟨initialSource, childSupport, receiverIssued⟩, received := receiverReceived,
          certificate := childCertificate, certificateChecked := childChecked,
          pending := .plain frame receiverReceived accepts pending, retained := nextRetained,
          retainedChecked := .plain (restChecked.reindex_context context.append_nil_pack.symm) retainedChecked,
          accounting := accounting.focus_rows split, annotated := annotated, row := row, annotation := annotation, checked := checked, bounded := bounded }
      exact ⟨input, data, bodyDependencies, bodyPlan, bodyRows, rfl, rfl, next, .focus data (.bind notValue) stack⟩

/-- Immediate rows of an actual value are silent, including product values;
private callable bodies remain in the recursive source witness. -/
theorem Source.value_silent {dependencies : Dependencies} {plan : Plan dependencies} {rows : Rows (signature plan)}
    (source : Source globals outward world allowed scope environment value contract demand requirements plan rows)
    (isValue : value.IsValue) : dependencies.Silent := by
  induction source with
  | unit | boolean | integer | reference | lambda | purePair => exact .pure
  | pair left right ihL ihR => exact .sequence (ihL isValue.1) (ihR isValue.2)
  | «variable» | app | bind | branch | perform => cases isValue

/-- Bind consumes the actual closed value and substitutes into the same
recursive body witness. Current support bounds both operand and suffix. -/
theorem Site.bind_value
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.bind parameter value body) runtimeScope stack output final context root)
    (closed : ClosedValue value) (captureClosed : ClosedExcept parameter body) :
    ∃ _next : Site globals outward world allowed actions phases budget ambient installations
      (body.subst parameter value) runtimeScope stack output final context root,
      RawStep ⟨.bind parameter value body, runtimeScope, stack⟩ ⟨body.subst parameter value, runtimeScope, stack⟩ [] [] := by
  rcases site with ⟨sourceDemand, requirements, dependencies, plan, rows, bound, current, received, certificate, certificateChecked,
    pending, retained, retainedChecked, accounting, annotated, row, annotation, checked, bounded⟩
  rcases current with ⟨source, support, issued⟩
  cases source with
  | bind initialSource bodySource =>
      rename_i input initialDemand initialReq initialDependencies initialPlan initialRows bodyDemand bodyReq bodyDependencies bodyPlan bodyRows
      have operandSupport : SourceSupport.Bounds ScopedPorts.Support.empty value.dependencies bound := by
        apply finite_bounds
        · intro identity member
          exact support.resources (Syntax.mem_resourceDependencies.mpr (List.mem_append_left _ (Syntax.mem_resourceDependencies.mp member)))
        · intro name; simp [ScopedPorts.Support.empty]
      have bodySupport : SourceSupport.Bounds (ScopedPorts.Support.extend ScopedPorts.Support.empty parameter bound) body.dependencies bound := by
        apply finite_bounds
        · intro identity member
          exact support.resources (Syntax.mem_resourceDependencies.mpr (List.mem_append_right _
            (Syntax.mem_without.mpr ⟨Syntax.mem_resourceDependencies.mp member, by simp⟩)))
        · intro name
          by_cases same : name = parameter
          · simp [ScopedPorts.Support.extend, same]
          · simp [ScopedPorts.Support.extend, ScopedPorts.Support.empty, same]
      have nextCurrent : CoreCallableContractAdmission.Supported globals outward world allowed runtimeScope Environment.empty ScopedPorts.Support.empty
          (body.subst parameter value) output bodyDemand bodyReq bodyPlan bodyRows bound :=
        (CoreCallableContractAdmission.Supported.mk bodySource bodySupport issued).substitution
          ⟨initialSource, operandSupport, issued⟩ closed
      cases certificate with
      | sequence initialCertificate bodyCertificate =>
          cases certificateChecked with
          | sequence initialChecked bodyChecked =>
              let next : Site globals outward world allowed actions phases budget ambient installations
                  (body.subst parameter value) runtimeScope stack output final context root :=
                { sourceDemand := bodyDemand, requirements := bodyReq, dependencies := bodyDependencies, plan := bodyPlan, rows := bodyRows,
                  bound := bound, current := nextCurrent, received := received,
                  certificate := bodyCertificate, certificateChecked := bodyChecked,
                  pending := pending, retained := retained, retainedChecked := retainedChecked,
                  accounting := (Accounting.silent_prefix_iff (Source.value_silent initialSource closed.1) initialRows bodyRows).mp accounting,
                  annotated := annotated, row := row, annotation := annotation, checked := checked, bounded := bounded }
              exact ⟨next, .bind parameter value body runtimeScope stack closed captureClosed⟩

/-- Plug recovers the saved suffix from the same pending frame. Its accepted
support bound is discharged by current issued/receiver facts, including actual
retaining callable values, rather than by their public ports. -/
theorem Site.plug_bind
    (site : Site globals outward world allowed actions phases budget ambient installations
      value runtimeScope (.push (.plain data) stack) input final (.plain restRows context) root)
    (closed : ClosedValue value) :
    ∃ (parameter : Nat) (body : Code), data.context = .bind parameter body ∧
      ∃ output : Contract, ∃ _next : Site globals outward world allowed actions phases budget ambient installations
        (.bind parameter value body) data.scope stack output final context root,
        RawStep ⟨value, runtimeScope, .push (.plain data) stack⟩ ⟨.bind parameter value body, data.scope, stack⟩ [] [] := by
  rcases site with ⟨sourceDemand, requirements, dependencies, plan, rows, bound, current, received, certificate, certificateChecked,
    pending, retained, retainedChecked, accounting, annotated, row, annotation, checked, bounded⟩
  cases pending with
  | plain frame bodyReceived accepts tail =>
      rename_i middle parameter body bodyDemand bodyReq inputBound bodyBound bodyPlan bodyRows
      have valueSupport : SourceSupport.Bounds ScopedPorts.Support.empty value.dependencies inputBound := by
        apply finite_bounds
        · intro identity member
          have supported := current.support.resources member
          exact accepts identity (current.issued supported) (received supported)
        · intro name; simp [ScopedPorts.Support.empty]
      have valueSource := (current.source.value_summary closed.1).value_allowed closed.1 allowed data.scope
      have valueSupported : CoreCallableContractAdmission.Supported globals outward world allowed data.scope Environment.empty
          ScopedPorts.Support.empty value input [] (.request [] []) .pure Rows.pure inputBound :=
        ⟨valueSource, valueSupport, frame.inputIssued⟩
      have pluggedSource := Source.bind valueSource frame.bodySource.source
      have pluggedSupport : SourceSupport.Bounds ScopedPorts.Support.empty (Code.bind parameter value body).dependencies (bound ++ bodyBound) := by
        apply finite_bounds
        · intro identity member
          obtain left | right := List.mem_append.mp (Syntax.mem_resourceDependencies.mp member)
          · exact List.mem_append_left _ (current.support.resources (Syntax.mem_resourceDependencies.mpr left))
          · exact List.mem_append_right _ (frame.bodySource.support.resources (Syntax.mem_resourceDependencies.mpr (Syntax.mem_without.mp right).1))
        · intro name; simp [ScopedPorts.Support.empty]
      have nextReceived : bound ++ bodyBound ⊆ _ := List.append_subset.mpr ⟨received, bodyReceived⟩
      have nextIssued : bound ++ bodyBound ⊆ world := List.append_subset.mpr ⟨current.issued, frame.bodySource.issued⟩
      have waiting := (Accounting.silent_iff (Source.value_silent current.source closed.1) rows).mp accounting
      cases retained with
      | plain suffixCertificate tailCertificate =>
          cases retainedChecked with
          | plain suffixChecked tailChecked =>
              cases waiting with
              | plain suffixRun =>
                  have bodyCertificate := suffixCertificate.reindex_context context.append_nil_pack
                  have bodyChecked := suffixChecked.reindex_context context.append_nil_pack
                  have shape : PlugRows bodyRows (sequenceRows (first := .pure) Rows.pure bodyRows) := .single
                  let next : Site globals outward world allowed actions phases budget ambient installations
                      (.bind parameter value body) data.scope stack middle final context root :=
                    { sourceDemand := bodyDemand, requirements := .sequence (.request [] []) bodyReq,
                      dependencies := .sequence .pure _, plan := .sequence .pure bodyPlan, rows := sequenceRows (first := .pure) Rows.pure bodyRows,
                      bound := bound ++ bodyBound, current := ⟨pluggedSource, pluggedSupport, nextIssued⟩, received := nextReceived,
                      certificate := shape.source_certificate bodyCertificate, certificateChecked := InstallationSupport.plug_rows shape bodyChecked,
                      pending := tail, retained := tailCertificate, retainedChecked := tailChecked,
                      accounting := shape.accounting_iff.mpr suffixRun,
                      annotated := annotated, row := row, annotation := annotation, checked := checked, bounded := bounded }
                  refine ⟨parameter, body, frame.position, middle, next, ?_⟩
                  have raw := RawStep.plug data value closed runtimeScope stack
                  simpa only [frame.position, ScopedExecution.Context.plug] using raw

/-- An exact builtin reply obtains the primitive result contract from the
same global key used by the request, and transports the saved recursive source
through the actual physical cell update. -/
theorem Site.read_cell_reply
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity))) runtimeScope stack result final context root)
    (compatible : globals.operations (.cell identity) 0 = some (.reference identity, .integer))
    (updated : CellUpdate identity payload payload stack after) :
    ∃ _next : Site globals outward world allowed actions phases budget ambient installations
      (.integer payload) runtimeScope after .integer final context root,
      RawStep ⟨.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)), runtimeScope, stack⟩
        ⟨.integer payload, runtimeScope, after⟩ [] [] := by
  rcases site with ⟨sourceDemand, requirements, dependencies, plan, rows, bound, current, received, certificate, certificateChecked,
    pending, retained, retainedChecked, accounting, annotated, row, annotation, checked, bounded⟩
  rcases current with ⟨source, support, issued⟩
  generalize equation : Code.perform (Instantiation.freezeEffect (.cell identity)) 0 (.resourceRef (.activation identity)) = code at source
  cases source <;> try { cases equation }
  case perform =>
    rename_i actual operationActual input valueActual deps operandPlan operandRows admitted known formed operandReq operand
    simp only [Code.perform.injEq] at equation
    obtain ⟨sameEffect, sameOperation, sameValue⟩ := equation
    have same : Instance.cell identity = actual := Instantiation.effect_realization_unique
      (Instantiation.frozen_effect_realizes Instantiation.Environment.empty (.cell identity))
      (by rw [sameEffect]; exact Instantiation.frozen_effect_realizes Instantiation.Environment.empty actual)
    subst actual
    subst operationActual
    subst valueActual
    have signatures := Option.some.inj (known.symm.trans compatible)
    obtain ⟨inputSame, resultSame⟩ := Prod.mk.inj signatures
    subst input
    subst result
    cases operand with
    | reference operandIssued =>
        have requestRun : Accounting.Run world installations Rows.request context root :=
          (Accounting.silent_prefix_iff .pure Rows.pure Rows.request).mp accounting
        have waiting := requestRun.builtin_wait (pending.cell_update_builtin updated)
        let next : Site globals outward world allowed actions phases budget ambient installations
            (.integer payload) runtimeScope after .integer final context root :=
          { sourceDemand := [], requirements := .request [] [], dependencies := .pure, plan := .pure, rows := Rows.pure,
            bound := [], current := ⟨.integer, .nil, by simp⟩, received := by simp,
            certificate := .pure, certificateChecked := .pure,
            pending := pending.cell_update updated, retained := retained, retainedChecked := retainedChecked,
            accounting := .pure waiting, annotated := annotated, row := row, annotation := annotation, checked := checked, bounded := bounded }
        exact ⟨next, .readCell identity payload runtimeScope stack after updated⟩

/-- Finite structural row data for the concrete builtin acceptance gate. -/
inductive ReadRows : {dependencies : Dependencies} → {plan : Plan dependencies} → Rows (signature plan) → Prop where
  | pure : ReadRows (plan := .pure) Rows.pure
  | read : ReadRows (plan := .request (effect := .cell 0) (operation := 0)) Rows.request
  | sequence (left : ReadRows first) (right : ReadRows second) : ReadRows (sequenceRows first second)

/-- Actual lexical receivers with cell0, allowing retained plain suffixes. -/
inductive ReadReceiver : {scope : SourceDependencyCapture.Scope} → {hints : ReturnHints scope} → Context hints → Prop where
  | cell : ReadReceiver (Context.cell (identity := 0) Context.nil)
  | plain (tail : ReadReceiver context) : ReadReceiver (Context.plain rows context)

omit [DeclarationPolicy] in
theorem ReadReceiver.select (receiver : ReadReceiver context) : select (.cell 0) 0 context = some (.builtin 0) := by
  induction receiver with
  | cell => rfl
  | plain tail ih => simp [SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.select, ih, Selection.prepend]

omit [DeclarationPolicy] in
/-- Construct current checking, rather than leave it a generic premise. -/
theorem ReadRows.admission {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope} {context : Context hints} (structural : ReadRows rows) (receiver : ReadReceiver context) :
    ∃ certificate : SourceAdmission.Code outward actions budget phases world installations rows context,
      InstallationSupport.CodeChecked ambient outward certificate := by
  induction structural generalizing scope with
  | pure => exact ⟨.pure, .pure⟩
  | read => exact ⟨.builtin receiver.select, .builtin (found := receiver.select)⟩
  | sequence left right ihL ihR =>
      obtain ⟨first, firstChecked⟩ := ihL (.plain receiver)
      obtain ⟨second, secondChecked⟩ := ihR receiver
      exact ⟨.sequence first second, .sequence firstChecked secondChecked⟩

omit [DeclarationPolicy] in
/-- Every read is interpreted by the actual cell receiver. The exact root
comes from the continuation, with no assumption about a future execution. -/
theorem ReadRows.accounting {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope} {context : Context hints} (structural : ReadRows rows) (receiver : ReadReceiver context)
    (waiting : Accounting.Wait world installations context .ordinary root) :
    Accounting.Run world installations rows context root := by
  induction structural generalizing scope with
  | pure => exact .pure waiting
  | read => exact .builtin receiver.select waiting
  | sequence left right ihL ihR => exact .sequence (ihL (.plain receiver) (.plain (ihR receiver waiting)))

#print axioms ReadReceiver.select
#print axioms ReadRows.admission
#print axioms ReadRows.accounting
#print axioms Site.focus_bind
#print axioms Site.plug_bind
#print axioms Site.bind_value
#print axioms Site.read_cell_reply
#print axioms Pending.cell_update_builtin
#print axioms Source.value_silent
#print axioms Source.lower
#print axioms FrameSource.plug
#print axioms Pending.cell_update
#print axioms Site.certified
end
end Ash.OneShot.CoreCallableContractExecution
