import CoreHigherOrderSupport

/-! Bounded DN-0033 payload-refinement prototype. The fixed declaration is
Invoke.run : (Unit → Unit with requests []) → Unit. This leaf computes retention
from closed code and authenticates the actual callable BODY, not the old lambda
Auth at its resource-free port. It does not construct unchanged M4 admission.
Higher-order outputs, branch joins and stored polymorphic helpers remain open. -/
namespace Ash.OneShot.CorePayloadRefinement
open ScopedExpressions ScopedExecution ProtectionContracts
open SourcePlannedTyping (Operations Contracts Value Environment)
open SourceDeclarationPlans (Plan)
open SourcePlanSignatures (signature)
open SourceDependencyAnnotations (Dependencies)
open RecursiveRequirements (Requirements)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.InitialAdmission.CoreCallableSupport (body bodyPlan bodyRequirements bodyOutward)

/-- A syntactic structural subset of plans. This finite witness derives Local
and Certified fields; it does not assume any future machine validity. -/
inductive PurePlan : {dependencies : Dependencies} → Plan dependencies → Prop where
  | pure : PurePlan .pure
  | sequence : PurePlan first → PurePlan second → PurePlan (.sequence first second)

variable {operations : Operations} {policy : Syntax.TicketPolicy} {contracts : Contracts}
  {ports : OperationRows operations} {owners : ContractRows contracts} {world : List Nat}

def baseRows : EnvironmentRows (fun _ => none) := by intro _ _ known; cases known

/-- Actual body data and present structural derivations. No execution or
successor premise is included. Historically-issued support is a finite current
world check and is proved explicitly for the concrete constructors below. -/
structure Payload (operations : Operations) (policy : Syntax.TicketPolicy)
    (contracts : Contracts) (ports : OperationRows operations)
    (owners : ContractRows contracts) (world : List Nat) where
  body : Code
  dependencies : Dependencies
  plan : Plan dependencies
  rows : Rows (signature plan)
  requirements : Requirements []
  source : SourcePlannedSources.Expression operations policy contracts world [] .none
    (Environment.extend (fun _ => none) 2 .unit) body .unit [] requirements (signature plan)
  authenticated : Auth operations policy ports owners (EnvironmentRows.extend baseRows 2 ValueRows.unit) source .unit rows
  outward : RecursiveOutward.Outward requirements (some [])
  structural : PurePlan plan
  closed : ClosedValue (.lambda 2 body)
  issued : Syntax.resourceDependencies (Code.lambda 2 body).dependencies ⊆ world

namespace Payload
variable (payload : Payload operations policy contracts ports owners world)
def code : Code := .lambda 2 payload.body
def value : Value := .function .unit .unit [] [] (signature payload.plan)
def retained : List Nat := ScopedPorts.Support.evaluate ScopedPorts.Support.empty payload.code.dependencies

theorem exact_port : payload.value.erase.erase.port = ScopedPorts.Port.function .unit .unit [] := rfl

theorem retained_exact : payload.retained = Syntax.resourceDependencies payload.code.dependencies :=
  ScopedPorts.Support.empty_evaluation _

theorem retained_issued : payload.retained ⊆ world := by
  rw [payload.retained_exact]
  exact payload.issued

theorem closure_source : SourcePlannedSources.ValueSummary operations policy contracts world
    (fun _ => none) [] payload.code payload.value := by
  apply SourcePlannedSources.Expression.lambda payload.source payload.outward
  · intro resource present
    simp [Value.erase, SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port, ScopedPorts.Port.resources] at present
  · intro request present
    cases present

/-- The old lambda Auth is deliberately not assumed. Its exact-body inversion
and substitution can instead be performed directly on the supplied BODY proof. -/
theorem invocation :
    ∃ source : SourcePlannedSources.Expression operations policy contracts world [] .none
      (fun _ => none) (payload.body.subst 2 .unit) .unit [] payload.requirements (signature payload.plan),
      Auth operations policy ports owners baseRows source .unit payload.rows := by
  have unitAuth : Auth operations policy ports owners baseRows
      (SourcePlannedSources.Expression.unit (world := world) (allowed := []) (scope := .none)
        (environment := fun _ => none)) .unit .pure := .unit
  exact ⟨SourcePlannedSources.substitution payload.source .unit ScopedExecution.Examples.unit_closed,
    payload.authenticated.substitution unitAuth ScopedExecution.Examples.unit_closed⟩

theorem invocation_support : SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Expression operations policy contracts world [] .none
    (fun _ => none) ScopedPorts.Support.empty (payload.body.subst 2 .unit) .unit []
    payload.requirements (signature payload.plan)
    (ScopedPorts.Support.evaluate (ScopedPorts.Support.extend ScopedPorts.Support.empty 2
      (Syntax.resourceDependencies Code.unit.dependencies)) payload.body.dependencies) :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Expression.annotate_substitution payload.source
    (SourcePlannedSources.Expression.unit (environment := fun _ => none))
    ScopedExecution.Examples.unit_closed ScopedPorts.Support.empty

theorem beta (scope : Execution.Scope) (tail : Stack) :
    RawStep ⟨.app payload.code .unit, scope, tail⟩
      ⟨payload.body.subst 2 .unit, .none, tail⟩ [] [] :=
  .beta 2 payload.body .unit scope tail ScopedExecution.Examples.unit_closed payload.closed
end Payload

/-- The actual body plans, rather than erased function ports, construct the
existing Local and Certified judgments at any receiving hints. -/
theorem PurePlan.local [SourcePlannedChecks.DeclarationPolicy]
    {plan : Plan dependencies} (checked : PurePlan plan)
    (hints : SourceContextualHints.Hints scope) :
    SourcePlannedChecks.Local outward actions phases world plan hints := by
  induction checked generalizing scope with
  | pure => exact .pure
  | sequence first second ihFirst ihSecond => exact .sequence (ihFirst _) (ihSecond _)

theorem PurePlan.certified [SourcePlannedChecks.DeclarationPolicy]
    {plan : Plan dependencies} (checked : PurePlan plan) :
    SourcePlannedChecks.Certified outward world plan := by
  induction checked with
  | pure => exact .pure
  | sequence first second ihFirst ihSecond => exact .sequence ihFirst ihSecond

/-- Two ordinary pure bodies have different rich refinements at one declared
port; the retained body shares the second plan but has independent cell support. -/
def trivial : Payload operations policy contracts ports owners world where
  body := .unit
  dependencies := .pure
  plan := .pure
  rows := .pure
  requirements := .request [] []
  source := .unit
  authenticated := .unit
  outward := .request (layers := [])
  structural := .pure
  closed := by simp [ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Code.dependencies]
  issued := by simp [Code.dependencies, Syntax.without, Syntax.resourceDependencies]

def sequenced : Payload operations policy contracts ports owners world where
  body := .bind 3 .unit .unit
  dependencies := .sequence .pure .pure
  plan := .sequence .pure .pure
  rows := .sequence .pure .pure
  requirements := .sequence (.request [] []) (.request [] [])
  source := .bind .unit .unit
  authenticated := .bind .unit .unit
  outward := .sequence (.request (layers := [])) (.request (layers := []))
  structural := .sequence .pure .pure
  closed := by simp [ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Code.dependencies, Syntax.without]
  issued := by simp [Code.dependencies, Syntax.without, Syntax.resourceDependencies]

def retaining (identity : Nat) (issued : identity ∈ world) :
    Payload operations policy contracts ports owners world where
  body := body identity
  dependencies := .sequence .pure .pure
  plan := bodyPlan
  rows := .sequence .pure .pure
  requirements := bodyRequirements
  source := .bind (.reference issued) .unit
  authenticated := .bind (.reference (issued := issued)) .unit
  outward := bodyOutward
  structural := .sequence .pure .pure
  closed := by simp [ClosedValue, body, Code.IsValue, Code.ResourceClosed, Code.freeNames, Instantiation.ResourceName.freeNames, Code.dependencies, Syntax.without]
  issued := by simpa [body, Code.dependencies, Syntax.without, Syntax.resourceDependencies] using issued

theorem two_body_same_port :
    (trivial (operations := operations) (policy := policy) (contracts := contracts)
      (ports := ports) (owners := owners) (world := world)).value.erase.erase.port =
    (sequenced (operations := operations) (policy := policy) (contracts := contracts)
      (ports := ports) (owners := owners) (world := world)).value.erase.erase.port := rfl

theorem two_body_distinct_refinements :
    (trivial (operations := operations) (policy := policy) (contracts := contracts)
      (ports := ports) (owners := owners) (world := world)).value ≠
    (sequenced (operations := operations) (policy := policy) (contracts := contracts)
      (ports := ports) (owners := owners) (world := world)).value := by
  intro same
  have erased := congrArg Value.erase same
  cases erased

theorem retaining_support (issued : identity ∈ world) :
    (retaining (operations := operations) (policy := policy) (contracts := contracts)
      (ports := ports) (owners := owners) identity issued).retained = [identity] := by
  simp [Payload.retained, Payload.code, retaining, body, Code.dependencies, Syntax.without,
    ScopedPorts.Support.evaluate]

/-- The handler syntax is fixed; rich plans below vary with its payload. -/
def handlerBody : Code := .bind 3 (.app (.variable 0) .unit) (.resume 1 .unit)
def invoke : Instance := .user 0 []
def handler : HandlerData where
  activation := 0
  effectInst := invoke
  clauses := .cons 0 0 1 handlerBody .nil
  scope := .none
  answer := .unit
  ticketBarrier := by simp [handlerBody, Clauses.dependencies, Code.dependencies, Syntax.without,
    Syntax.ticketDependencies]

theorem handlerReady : ClosedExcept 0 handlerBody := by
  intro name present
  simpa [handlerBody, Code.dependencies, Syntax.without] using present

def clause (payload : Payload operations policy contracts ports owners world) : Code :=
  .bind 3 (.app payload.code .unit) (.resume 1 .unit)

theorem substituted_clause (payload : Payload operations policy contracts ports owners world) :
    handlerBody.subst 0 payload.code = clause payload := rfl

/-- Exact RawStep constructors expose the actual capture, strict initializer
focus and beta transition. No expected successor certificate is a premise. -/
theorem capture (payload : Payload operations policy contracts ports owners world)
    (cut : HandlerCut invoke whole captured tail handler) :
    RawStep ⟨.perform (Instantiation.freezeEffect invoke) 0 payload.code, caller, whole⟩
      ⟨clause payload, .ticket 1 owner, .live owner .unit .unit captured .none tail⟩
      [.ticket owner] [] := by
  simpa only [substituted_clause, handler] using RawStep.capture invoke 0 0 1 owner payload.code
    handlerBody caller whole captured tail handler .unit cut ClauseAt.hit payload.closed handlerReady

def pendingResume (owner : Nat) : PlainData :=
  { context := .bind 3 (.resume 1 .unit), scope := .ticket 1 owner, input := .unit, output := .unit, pending := [owner], translated := rfl }

theorem focus_call (payload : Payload operations policy contracts ports owners world) :
    RawStep ⟨clause payload, .ticket 1 owner, live⟩
      ⟨.app payload.code .unit, .ticket 1 owner, .push (.plain (pendingResume owner)) live⟩ [] [] :=
  .focus (pendingResume owner) (.bind (by simp [Code.IsValue])) live

theorem call_beta (payload : Payload operations policy contracts ports owners world) :
    RawStep ⟨.app payload.code .unit, .ticket 1 owner, .push (.plain (pendingResume owner)) live⟩
      ⟨payload.body.subst 2 .unit, .none, .push (.plain (pendingResume owner)) live⟩ [] [] :=
  payload.beta _ _

/-- Selected receiver annotations are realized by the actual cell/handler
stacks below. Their finite support check uses the existing selector. -/
def unitContract : SourcePlannedTyping.Contract where
  input := .unit
  answer := .unit
  held := false
  resumeDemand := []
  resumeRow := []
  closeDemand := []
  closeRow := some []
  resumeEffects := []
  closeEffects := []

def handlerDependencies (payload : Payload operations policy contracts ports owners world) (owner : Nat) : Dependencies :=
  .sequence (.sequence .pure (.sequence .pure payload.dependencies))
    (.sequence .pure (.invoke ⟨owner, .resume⟩))
def handlerPlan (payload : Payload operations policy contracts ports owners world) (owner : Nat) :=
  Plan.sequence (Plan.sequence Plan.pure (Plan.sequence Plan.pure payload.plan))
    (Plan.sequence Plan.pure (Plan.invoke (key := ⟨owner, .resume⟩)))
def handlerRows (payload : Payload operations policy contracts ports owners world) (owner : Nat) :
    Rows (signature (handlerPlan payload owner)) :=
  .sequence (.sequence .pure (.sequence .pure payload.rows)) (.sequence .pure .invoke)
def handlerRequirements (owner : Nat) : Requirements [owner] :=
  .sequence (.emitAfter (.sequence (.request [] []) (.request [] [])) [] [])
    (.sequence (.request [] []) (.invoke ⟨owner, .resume⟩ [] []))

theorem handler_source (payload : Payload operations policy contracts ports owners world)
    (known : contracts owner = some unitContract) (permission : (policy 1).resume = true) :
    SourcePlannedSources.Expression operations policy contracts world [] (.ticket 1 owner)
      (Environment.extend (fun _ => none) 0 payload.value) handlerBody .unit [owner]
      (handlerRequirements owner) (signature (handlerPlan payload owner)) := by
  unfold handlerBody handlerRequirements handlerPlan
  dsimp only [signature]
  refine SourcePlannedSources.Expression.bind (input := .unit) (initialDemand := []) (bodyDemand := [owner]) ?_ ?_
  · apply SourcePlannedSources.Expression.app (functionDemand := []) (argumentDemand := []) (requests := []) (latent := [])
    · apply SourcePlannedSources.Expression.variable rfl
      intro identity present
      simp [Value.erase, SourceDependencyAnnotations.Value.erase,
        CoherentSourceTypes.Value.port, ScopedPorts.Port.resources] at present
    · exact .unit
    · exact List.nil_subset _
  · apply SourcePlannedSources.Expression.resume known rfl permission SourcePlannedSources.Expression.unit
    · exact List.nil_subset _
    · intro identity present
      cases present

theorem handler_authenticated (payload : Payload operations policy contracts ports owners world)
    (known : contracts owner = some unitContract) (permission : (policy 1).resume = true) :
    Auth operations policy ports owners
      (EnvironmentRows.extend baseRows 0 ((.function .unit .unit payload.rows) : ValueRows payload.value))
      (handler_source payload known permission) .unit (handlerRows payload owner) := by
  unfold handlerRows handlerBody handlerRequirements
  unfold handlerPlan at *
  dsimp only [signature] at *
  apply Auth.bind (input := .unit) (inputRows := ValueRows.unit) (initialDemand := []) (bodyDemand := [owner])
    (initializer := by
      apply SourcePlannedSources.Expression.app (functionDemand := []) (argumentDemand := []) (requests := []) (latent := [])
      · apply SourcePlannedSources.Expression.variable rfl
        intro identity present
        simp [Value.erase, SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port, ScopedPorts.Port.resources] at present
      · exact .unit
      · exact List.nil_subset _)
    (body := by
      apply SourcePlannedSources.Expression.resume known rfl permission SourcePlannedSources.Expression.unit
      · exact List.nil_subset _
      · intro identity present; cases present)
  · apply Auth.app (inputRows := ValueRows.unit) (outputRows := ValueRows.unit) (bodyRows := payload.rows)
      (functionDemand := []) (argumentDemand := []) (requests := []) (latent := []) (admitted := List.nil_subset _)
    · exact Auth.variable (environmentRows := EnvironmentRows.extend baseRows 0 ((.function .unit .unit payload.rows) : ValueRows payload.value)) (known := rfl) (formed := by
        intro identity present
        simp [Value.erase, SourceDependencyAnnotations.Value.erase, CoherentSourceTypes.Value.port, ScopedPorts.Port.resources] at present)
    · exact Auth.unit
  · have inputSame : (owners owner unitContract known).1 = ValueRows.unit := by
      cases (owners owner unitContract known).1
      rfl
    have answerSame : (owners owner unitContract known).2 = ValueRows.unit := by
      cases (owners owner unitContract known).2
      rfl
    have unitAuth : Auth operations policy ports owners
        ((EnvironmentRows.extend baseRows 0 ((.function .unit .unit payload.rows) : ValueRows payload.value)).extend 3 ValueRows.unit)
        (SourcePlannedSources.Expression.unit (world := world) (allowed := []) (scope := .ticket 1 owner)
          (environment := Environment.extend (Environment.extend (fun _ => none) 0 payload.value) 3 .unit))
        (owners owner unitContract known).1 .pure := by
      rw [inputSame]
      exact .unit
    have resumed := Auth.resume unitAuth (known := known) (resolved := rfl)
      (permission := permission) (admitted := List.nil_subset _) (formed := by intro identity present; cases present)
    rw [answerSame] at resumed
    simpa only [unitContract, List.nil_append] using resumed

def table : List (Nat × ClauseContract) := [(0, ⟨false, some [], some []⟩)]
def families (payload : Payload operations policy contracts ports owners world) :
    SourceDependencyAnnotations.ClauseDependencies :=
  [(0, (some (handlerDependencies payload), some (handlerDependencies payload)))]
def tables : CallableProtectionFrames.Tables := fun _ => table
def allFamilies (payload : Payload operations policy contracts ports owners world) :
    SourceDependencyCapture.Families := fun _ => families payload

def innerWhole (identity : Nat) : Stack :=
  .push (.handler handler) (.push (.cell identity 0 .none .unit) .nil)
def outerWhole (identity : Nat) : Stack :=
  .push (.cell identity 0 .none .unit) (.push (.handler handler) .nil)
def innerScope (payload : Payload operations policy contracts ports owners world) (identity : Nat) : SourceDependencyCapture.Scope :=
  .handler invoke table (families payload) (.cell identity .nil)
def outerScope (payload : Payload operations policy contracts ports owners world) (identity : Nat) : SourceDependencyCapture.Scope :=
  .cell identity (.handler invoke table (families payload) .nil)

theorem inner_realizes (payload : Payload operations policy contracts ports owners world) (identity : Nat) :
    SourceDependencyCapture.Realizes tables (allFamilies payload) (innerScope payload identity) (innerWhole identity) := by
  unfold innerScope innerWhole tables allFamilies handler
  apply SourceDependencyCapture.Realizes.push
  · exact @SourceDependencyCapture.Frame.handler tables (allFamilies payload) handler
  · exact .push .cell .nil
theorem outer_realizes (payload : Payload operations policy contracts ports owners world) (identity : Nat) :
    SourceDependencyCapture.Realizes tables (allFamilies payload) (outerScope payload identity) (outerWhole identity) := by
  unfold outerScope outerWhole tables allFamilies handler
  apply SourceDependencyCapture.Realizes.push .cell
  apply SourceDependencyCapture.Realizes.push
  · exact @SourceDependencyCapture.Frame.handler tables (allFamilies payload) handler
  · exact .nil
theorem inner_cut (identity : Nat) :
    HandlerCut invoke (innerWhole identity) (.push (.handler handler) .nil)
      (.push (.cell identity 0 .none .unit) .nil) handler := .hit _ _ rfl
theorem outer_cut (identity : Nat) :
    HandlerCut invoke (outerWhole identity)
      (.push (.cell identity 0 .none .unit) (.push (.handler handler) .nil)) .nil handler :=
  .push _ _ _ _ _ (by simp [ExecFrame.erase, Frame.target, invoke]) (.hit _ _ rfl)

def receiverCheck (payload : Payload operations policy contracts ports owners world)
    (scope : SourceDependencyCapture.Scope) (ambient : List Nat) : Prop :=
  match SourceDependencyCapture.select invoke 0 scope with
  | some (.handler _ receiving _ _) => payload.retained ⊆ receiving.visibleResources ++ ambient
  | _ => False

theorem retained_inner_receiver (issued : identity ∈ world) :
    let payload : Payload operations policy contracts ports owners world := retaining identity issued
    receiverCheck payload (innerScope payload identity) [] := by
  dsimp only
  simp [receiverCheck, SourceDependencyCapture.select, innerScope, table, families,
    SourceDependencyCapture.lookupDependencies, lookup, SourceDependencyCapture.Scope.visibleResources,
    retaining_support]

theorem retained_outer_receiver_rejected (issued : identity ∈ world) :
    let payload : Payload operations policy contracts ports owners world := retaining identity issued
    ¬ receiverCheck payload (outerScope payload identity) [] := by
  dsimp only
  simp [receiverCheck, SourceDependencyCapture.select, outerScope, table, families, invoke,
    SourceDependencyCapture.lookupDependencies, lookup, SourceDependencyCapture.Selection.prepend,
    SourceDependencyCapture.Scope.visibleResources, retaining_support]


def savedHints (payload : Payload operations policy contracts ports owners world) :
    SourceContextualHints.Hints (.handler invoke table (families payload) .nil) := .handler [] .nil
def tailHints (identity : Nat) : SourceContextualHints.Hints (.cell identity .nil) := .cell .nil
def liveHints (payload : Payload operations policy contracts ports owners world) (identity : Nat) :
    SourceContextualHints.Hints (.live 9 (.handler invoke table (families payload) .nil) (.cell identity .nil)) :=
  .live (savedHints payload) (tailHints identity)
def selectedOwner (payload : Payload operations policy contracts ports owners world) (identity : Nat) :
    SourceContextualInvocationHints.Selection :=
  ⟨⟨.nil, .handler invoke table (families payload) .nil, .cell identity .nil⟩,
    .nil, savedHints payload, tailHints identity⟩
def actions : Syntax.UsageTickets := fun _ => some ⟨true, false⟩

theorem resume_access (payload : Payload operations policy contracts ports owners world) (identity : Nat) :
    SourceContextualInvocations.Resume actions (OwnerPhaseTransitions.available [9]) 9
      (liveHints payload identity) ((selectedOwner payload identity).resumed 9) :=
  SourceContextualInvocations.check_resume_iff.mp rfl

theorem restored_pending [SourcePlannedChecks.DeclarationPolicy]
    (payload : Payload operations policy contracts ports owners world) (identity : Nat) :
    SourcePlannedChecks.Pending [] actions (OwnerPhaseTransitions.spend (OwnerPhaseTransitions.available [9]) 9)
      world ((selectedOwner payload identity).resumed 9).hints .nil :=
  .handler (.spent (.cell .nil))

/-- The fixed clause obtains the existing Local and Pending fields from its
payload's actual structural body, plus the checked active owner's resume. -/
theorem handler_local [SourcePlannedChecks.DeclarationPolicy]
    (payload : Payload operations policy contracts ports owners world) (identity : Nat) :
    SourcePlannedChecks.Local [] actions (OwnerPhaseTransitions.available [9]) world
      (handlerPlan payload 9) (liveHints payload identity) := by
  apply SourcePlannedChecks.Local.sequence
  · apply SourcePlannedChecks.Local.sequence
    · exact .pure
    · apply SourcePlannedChecks.Local.sequence
      · exact .pure
      · exact payload.structural.local _
  · exact .sequence .pure (.resume (resume_access payload identity) (restored_pending payload identity))

theorem handler_pending [SourcePlannedChecks.DeclarationPolicy]
    (payload : Payload operations policy contracts ports owners world) (identity : Nat) :
    SourcePlannedChecks.Pending [] actions (OwnerPhaseTransitions.available [9]) world
      (liveHints payload identity) .nil := .live (.handler .nil) (.cell .nil)

theorem handler_certified [SourcePlannedChecks.DeclarationPolicy]
    (payload : Payload operations policy contracts ports owners world) (owner : Nat) :
    SourcePlannedChecks.Certified [] world (handlerPlan payload owner) :=
  .sequence (.sequence .pure (.sequence .pure payload.structural.certified)) (.sequence .pure .invoke)


def clausePlans (payload : Payload operations policy contracts ports owners world) :
    SourceDeclarationPlans.ClausePlans handler.clauses (families payload) :=
  .cons (.available (fun owner => handlerPlan payload owner))
    (.available (fun owner => handlerPlan payload owner)) .nil

theorem selected_plan (payload : Payload operations policy contracts ports owners world) :
    SourcePlannedRecipeDeclarations.Selected 0 false (clausePlans payload) 0 1 handlerBody
      (fun owner => handlerPlan payload owner) := .ordinary

def checkReceiver (payload : Payload operations policy contracts ports owners world)
    (scope : SourceDependencyCapture.Scope) (ambient : List Nat) : Bool :=
  match SourceDependencyCapture.select invoke 0 scope with
  | some (.handler _ receiving _ _) =>
      payload.retained.all (fun identity => decide (identity ∈ receiving.visibleResources ++ ambient))
  | _ => false

theorem checkReceiver_iff (payload : Payload operations policy contracts ports owners world)
    (scope : SourceDependencyCapture.Scope) (ambient : List Nat) :
    checkReceiver payload scope ambient = true ↔ receiverCheck payload scope ambient := by
  unfold checkReceiver receiverCheck
  cases SourceDependencyCapture.select invoke 0 scope with
  | none => simp
  | some selected => cases selected with
    | builtin => simp
    | handler => simp [List.all_eq_true, List.subset_def]

/- Specialized existing Selected/Local/Pending fields are constructed. The
stored family still varies with the actual payload, so this does not supply a
single old OperationRows/Declarations witness before that payload is known. -/
def declared : ScopedPorts.Signature := fun effect operation =>
  if effect = invoke ∧ operation = 0 then some (.function .unit .unit [], .unit) else none

theorem declared_exact (payload : Payload operations policy contracts ports owners world) :
    declared invoke 0 = some (payload.value.erase.erase.port, .unit) := by rw [payload.exact_port]; simp [declared]

theorem retaining_pre_beta_auth_unavailable (issued : identity ∈ world) :
    let payload : Payload operations policy contracts ports owners world := retaining identity issued
    ¬ Auth operations policy ports owners baseRows payload.closure_source
      (.function .unit .unit payload.rows) .pure := by
  dsimp only
  apply CoreHigherOrderSupport.retained_code_resource_free_auth_obstruction
  rfl

theorem beta_support (payload : Payload operations policy contracts ports owners world) :
    Syntax.resourceDependencies (payload.body.subst 2 .unit).dependencies ⊆ payload.retained := by
  apply substitution_resource_support
  · rw [payload.retained_exact]
    simpa only [Payload.code, Code.dependencies, resource_dependencies_without_variable]
      using List.Subset.refl (Syntax.resourceDependencies payload.body.dependencies)
  · simp [Code.dependencies, Syntax.resourceDependencies]

def betaHints (payload : Payload operations policy contracts ports owners world) (identity : Nat) :
    SourceContextualHints.Hints
      (.plain (.sequence .pure (.invoke ⟨9, .resume⟩))
        (.live 9 (.handler invoke table (families payload) .nil) (.cell identity .nil))) :=
  .plain (liveHints payload identity)

theorem beta_local [SourcePlannedChecks.DeclarationPolicy]
    (payload : Payload operations policy contracts ports owners world) (identity : Nat) :
    SourcePlannedChecks.Local [] actions (OwnerPhaseTransitions.available [9]) world
      payload.plan (betaHints payload identity) := payload.structural.local _

theorem beta_pending [SourcePlannedChecks.DeclarationPolicy]
    (payload : Payload operations policy contracts ports owners world) (identity : Nat) :
    SourcePlannedChecks.Pending [] actions (OwnerPhaseTransitions.available [9]) world
      (betaHints payload identity) .nil :=
  .plain (.sequence .pure (.resume (resume_access payload identity) (restored_pending payload identity)))
    (handler_pending payload identity)

/-- A complete three-transition prefix with actual selected clause and body
checks. This is a calculus interface experiment, not the full Rust trace
correspondence or unchanged InitialAdmission. -/
theorem capture_invocation [SourcePlannedChecks.DeclarationPolicy]
    (payload : Payload operations policy contracts ports owners world) (identity : Nat) :
    RawStep ⟨.perform (Instantiation.freezeEffect invoke) 0 payload.code, .none, innerWhole identity⟩
      ⟨clause payload, .ticket 1 9,
        .live 9 .unit .unit (.push (.handler handler) .nil) .none (.push (.cell identity 0 .none .unit) .nil)⟩
      [.ticket 9] [] ∧
    RawStep ⟨clause payload, .ticket 1 9,
        .live 9 .unit .unit (.push (.handler handler) .nil) .none (.push (.cell identity 0 .none .unit) .nil)⟩
      ⟨.app payload.code .unit, .ticket 1 9,
        .push (.plain (pendingResume 9))
          (.live 9 .unit .unit (.push (.handler handler) .nil) .none (.push (.cell identity 0 .none .unit) .nil))⟩ [] [] ∧
    RawStep ⟨.app payload.code .unit, .ticket 1 9,
        .push (.plain (pendingResume 9))
          (.live 9 .unit .unit (.push (.handler handler) .nil) .none (.push (.cell identity 0 .none .unit) .nil))⟩
      ⟨payload.body.subst 2 .unit, .none,
        .push (.plain (pendingResume 9))
          (.live 9 .unit .unit (.push (.handler handler) .nil) .none (.push (.cell identity 0 .none .unit) .nil))⟩ [] [] ∧
    (∃ source : SourcePlannedSources.Expression operations policy contracts world [] .none
        (fun _ => none) (payload.body.subst 2 .unit) .unit [] payload.requirements (signature payload.plan),
      Auth operations policy ports owners baseRows source .unit payload.rows) ∧
    SourcePlannedChecks.Local [] actions (OwnerPhaseTransitions.available [9]) world payload.plan (betaHints payload identity) ∧
    SourcePlannedChecks.Pending [] actions (OwnerPhaseTransitions.available [9]) world (betaHints payload identity) .nil :=
  ⟨capture payload (inner_cut identity), focus_call payload, call_beta payload,
    payload.invocation, beta_local payload identity, beta_pending payload identity⟩

/-- A fixed rich table cannot simultaneously authenticate both actual body
refinements by equality at this same key. A candidate retaining these exact
refinements must change this interface; selecting a different table per payload
does not construct one shared declaration. -/
theorem fixed_operation_input_obstruction :
    ¬ (operations invoke 0 = some
        ((trivial (operations := operations) (policy := policy) (contracts := contracts)
          (ports := ports) (owners := owners) (world := world)).value, .unit) ∧
      operations invoke 0 = some
        ((sequenced (operations := operations) (policy := policy) (contracts := contracts)
          (ports := ports) (owners := owners) (world := world)).value, .unit)) := by
  rintro ⟨first, second⟩
  exact two_body_distinct_refinements (Prod.mk.inj (Option.some.inj (first.symm.trans second))).1

theorem trivial_receiver :
    let payload : Payload operations policy contracts ports owners world := trivial
    checkReceiver payload (innerScope payload identity) [] = true := by
  dsimp only
  simp [checkReceiver, SourceDependencyCapture.select, innerScope, table, families,
    SourceDependencyCapture.lookupDependencies, lookup, Payload.retained, Payload.code,
    trivial, Code.dependencies, Syntax.without, ScopedPorts.Support.evaluate]

theorem sequenced_receiver :
    let payload : Payload operations policy contracts ports owners world := sequenced
    checkReceiver payload (innerScope payload identity) [] = true := by
  dsimp only
  simp [checkReceiver, SourceDependencyCapture.select, innerScope, table, families,
    SourceDependencyCapture.lookupDependencies, lookup, Payload.retained, Payload.code,
    sequenced, Code.dependencies, Syntax.without, ScopedPorts.Support.evaluate]

theorem retaining_receiver_checked (issued : identity ∈ world) :
    let payload : Payload operations policy contracts ports owners world := retaining identity issued
    checkReceiver payload (innerScope payload identity) [] = true :=
  (checkReceiver_iff _ _ _).mpr (retained_inner_receiver issued)

theorem retaining_receiver_rejected (issued : identity ∈ world) :
    let payload : Payload operations policy contracts ports owners world := retaining identity issued
    checkReceiver payload (outerScope payload identity) [] = false := by
  dsimp only
  apply Bool.eq_false_iff.mpr
  intro accepted
  exact retained_outer_receiver_rejected issued ((checkReceiver_iff _ _ _).mp accepted)

/-- Fresh acquisition keeps its cell event. Only the closed callable body is
substituted by the prototype; no pure-function or capture erasure occurs. -/
def resourceTemplate : Code := .handle (Instantiation.freezeEffect invoke)
  (.perform (Instantiation.freezeEffect invoke) 0
    (.lambda 2 (.bind 3 (.resourceRef (.bound 0)) .unit))) handler.clauses

theorem acquire (identity : Nat) :
    RawStep ⟨.resource 0 (.integer 0) resourceTemplate, .none, .nil⟩
      ⟨resourceTemplate.instantiate (Instantiation.Environment.empty.bind 0 identity), .none,
        .push (.cell identity 0 .none .unit) .nil⟩ [.resource identity] [] := by
  apply RawStep.enterCell
  simp [Code.ResourceClosed, Code.freeNames, resourceTemplate, handler, handlerBody, Clauses.freeNames,
    Instantiation.Effect.freeNames, Instantiation.ResourceName.freeNames, Instantiation.freezeEffect, invoke]

theorem install_after_acquire (identity : Nat) (issued : identity ∈ world) :
    let payload : Payload operations policy contracts ports owners world := retaining identity issued
    RawStep ⟨resourceTemplate.instantiate (Instantiation.Environment.empty.bind 0 identity), .none,
        .push (.cell identity 0 .none .unit) .nil⟩
      ⟨.perform (Instantiation.freezeEffect invoke) 0 payload.code, .none, innerWhole identity⟩ [] [] := by
  dsimp only
  simpa only [resourceTemplate, Code.instantiate, Clauses.instantiate, Instantiation.freezeEffect,
    Instantiation.Effect.instantiate, Instantiation.ResourceName.instantiate, Instantiation.Environment.bind, Instantiation.Environment.empty, List.map_nil, if_true,
    Payload.code, retaining, body, handler, handlerBody, innerWhole, invoke] using
      RawStep.enterHandler handler
        (.perform (Instantiation.freezeEffect invoke) 0
          (retaining (operations := operations) (policy := policy) (contracts := contracts)
            (ports := ports) (owners := owners) identity issued).code)
        (.push (.cell identity 0 .none .unit) .nil)

namespace Payload
variable (payload : Payload operations policy contracts ports owners world)
/-- The bound is computed by the existing structural source annotation, not a
list supplied as an alleged capture fact. -/
theorem supported : SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Expression
    operations policy contracts world [] .none (fun _ => none) ScopedPorts.Support.empty
    payload.code payload.value [] (.request [] []) .pure payload.retained :=
  SourceScheduledCleanupInterfaces.Lexical.Recursive.SourceSupport.Expression.annotate
    payload.closure_source ScopedPorts.Support.empty

theorem capture_support (selected : SourceDependencyCapture.select invoke 0 scope =
      some (.handler captured receiving contract modes))
    (checked : checkReceiver payload scope ambient = true) :
    Syntax.resourceDependencies payload.code.dependencies ⊆ receiving.visibleResources ++ ambient := by
  have boundary : payload.retained ⊆ receiving.visibleResources ++ ambient := by
    simpa only [receiverCheck, selected] using (checkReceiver_iff payload scope ambient).mp checked
  exact payload.supported.capture_support boundary
end Payload

/-- The body call's saved lexical barrier and full capture remain synchronized
with the actual post-beta stack, including the live (unconsumed) owner. -/
theorem beta_realizes (payload : Payload operations policy contracts ports owners world) (identity : Nat) :
    SourceDependencyCapture.Realizes tables (allFamilies payload)
      (.plain (.sequence .pure (.invoke ⟨9, .resume⟩))
        (.live 9 (.handler invoke table (families payload) .nil) (.cell identity .nil)))
      (.push (.plain (pendingResume 9))
        (.live 9 .unit .unit (.push (.handler handler) .nil) .none
          (.push (.cell identity 0 .none .unit) .nil))) := by
  apply SourceDependencyCapture.Realizes.push .plain
  apply SourceDependencyCapture.Realizes.live
  · apply SourceDependencyCapture.Realizes.push
    · exact @SourceDependencyCapture.Frame.handler tables (allFamilies payload) handler
    · exact .nil
  · exact .push .cell .nil

theorem sequenced_body_step (tail : Stack) :
    RawStep ⟨(sequenced (operations := operations) (policy := policy) (contracts := contracts)
      (ports := ports) (owners := owners) (world := world)).body.subst 2 .unit, .none, tail⟩
      ⟨.unit, .none, tail⟩ [] [] := by
  apply RawStep.bind 3 .unit .unit .none tail ScopedExecution.Examples.unit_closed
  intro name present
  cases present

theorem retaining_body_step (issued : identity ∈ world) (tail : Stack) :
    RawStep ⟨(retaining (operations := operations) (policy := policy) (contracts := contracts)
      (ports := ports) (owners := owners) identity issued).body.subst 2 .unit, .none, tail⟩
      ⟨.unit, .none, tail⟩ [] [] := by
  apply RawStep.bind 3 (.resourceRef (.activation identity)) .unit .none tail
  · simp [ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames,
      Instantiation.ResourceName.freeNames, Code.dependencies]
  · intro name present
    cases present

/-- The same generic capture/beta certificate applies to both differently
structured payloads. No operation table is changed per invocation. -/
example [SourcePlannedChecks.DeclarationPolicy] :
    declared invoke 0 = some ((trivial (operations := operations) (policy := policy)
      (contracts := contracts) (ports := ports) (owners := owners) (world := world)).value.erase.erase.port, .unit) ∧
    declared invoke 0 = some ((sequenced (operations := operations) (policy := policy)
      (contracts := contracts) (ports := ports) (owners := owners) (world := world)).value.erase.erase.port, .unit) :=
  ⟨declared_exact _, declared_exact _⟩

/-- Freshly issued support is recomputed after the acquisition instantiation.
The selected inner receiver accepts it; an outer selected receiver rejects it. -/
example (identity : Nat) (_fresh : identity ∉ world) :
    let payload : Payload operations policy contracts ports owners (world ++ [identity]) :=
      retaining identity (List.mem_append_right _ List.mem_cons_self)
    payload.retained ⊆ world ++ [identity] ∧
    checkReceiver payload (innerScope payload identity) [] = true ∧
    checkReceiver payload (outerScope payload identity) [] = false :=
  ⟨Payload.retained_issued _, retaining_receiver_checked _, retaining_receiver_rejected _⟩

#print axioms Payload.capture_support
#print axioms beta_realizes
#print axioms retaining_body_step

/- Retention decision: keep this bounded experiment as evidence for declared
ports plus payload-indexed clause plans and independent support. It constructs
specialized Selected, Source/Auth handler BODY, Certified, Local, Pending,
actual RawStep capture/focus/beta and after-beta Source/Auth/support fields.

It supplies neither old Auth of the retaining lambda nor a fixed rich
Operations/OperationRows/Declarations family admitting every payload. The
whole InitialAdmission Program's source/authenticated/certified/certificate,
resourceChecked, interpreted and accounting fields are not assembled here.
This candidate would first separate operation declarations from actual rich
operand refinements, then select the corresponding structural clause family.
Independent support must replace the old lambda/value_support,
substitution and resource-exit bounds. General helper parameters, branch joins,
higher-order operation outputs and caller-continuation refinements remain
required transport obligations. This prefix does not select or finish that
general repair and is not a whole-program M4 or Rust simulation theorem. -/

#print axioms fixed_operation_input_obstruction
#print axioms retaining_receiver_checked
#print axioms retaining_receiver_rejected
#print axioms acquire
#print axioms install_after_acquire

#print axioms retaining_pre_beta_auth_unavailable
#print axioms beta_support
#print axioms capture_invocation

#print axioms selected_plan
#print axioms checkReceiver_iff

#print axioms handler_local
#print axioms handler_pending

#print axioms handler_source
#print axioms handler_authenticated

#print axioms capture
#print axioms call_beta
#print axioms retained_inner_receiver
#print axioms retained_outer_receiver_rejected
#print axioms Payload.invocation
#print axioms Payload.invocation_support
#print axioms PurePlan.local
#print axioms two_body_distinct_refinements
#print axioms retaining_support
end Ash.OneShot.CorePayloadRefinement
