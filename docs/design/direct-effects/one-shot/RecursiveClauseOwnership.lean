import RecursiveDisposalCapture

/-!
Clause ownership for the full recursive source judgment. Source provenance
supplies the declared invocation demands; existing checked traces rule out a
second consumption. Resource bodies use their established discharge relation.
-/

namespace Ash.OneShot.RecursiveClauseOwnership
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts
open RecursiveRequirements (Requirements Checked Key Store)
open RecursiveClosing (PlanTemplate)
open ProtectionResiduals
open CallableProtectionFrames (contextOf)
open RecursiveDisposalCapture (directCalls directRetirements modeDemand)
open OwnerPhaseTransitions (Phases available spend spendAll)
open SourceTemplates (Expression Segment)
open RecursiveRecords (Records CheckedState)

def directInvocations : {owners : List Nat} → Requirements owners → List (Key × List Nat)
  | _, .request _ _ | _, .retire _ | _, .spent _ => []
  | _, .invoke key demand _ => [(key, demand)]
  | _, .sequence first second | _, .choice first second _ => directInvocations first ++ directInvocations second
  | _, .emitAfter body _ _ => directInvocations body

theorem invocations_prepend (requirements : Requirements owners) :
    directInvocations (requirements.prepend nearer) = directInvocations requirements := by
  induction requirements <;> simp_all [Requirements.prepend, directInvocations]

theorem invocation_owners (requirements : Requirements owners) :
    (directInvocations requirements).map (fun call => call.1.owner) = directCalls requirements := by
  induction requirements <;> simp_all [directInvocations, directCalls]

theorem hidden_invocations (hidden : ResourceRequirements.Hides identity opened closed) :
    directInvocations opened = directInvocations closed := by
  induction hidden <;> simp_all [directInvocations]

theorem source_invocation_contract
    (source : SourceTemplates.Expression operations policy contracts world allowed scope environment code output owners requirements)
    (member : (key, demand) ∈ directInvocations requirements) :
    ∃ contract, contracts key.owner = some contract ∧ demand = modeDemand contract key.mode := by
  induction source using SourceTemplates.Expression.rec (motive_2 := fun _ _ _ _ _ _ _ => True) with
  | handler body clauses capabilities coverage unique admitted table modes ih => exact ih (by simpa only [invocations_prepend] using member)
  | stable | callable | lambda | purePair => cases member
  | pair left right ihLeft ihRight | app left right _ ihLeft ihRight | bind left right ihLeft ihRight | cleanup left right _ ihLeft ihRight =>
      rcases List.mem_append.mp member with first | second
      · exact ihLeft first
      · exact ihRight second
  | branch condition yes no same ihCondition ihYes ihNo =>
      rcases List.mem_append.mp member with first | second
      · exact ihCondition first
      · rcases List.mem_append.mp second with yes | no
        · exact ihYes yes
        · exact ihNo no
  | perform known admitted operand formed ih | resource operand _ _ _ _ _ ih ihBody => exact ih member
  | resume known resolved permission operand admitted formed ih =>
      rcases List.mem_append.mp member with operand | invoked
      · exact ih operand
      · have same := List.mem_singleton.mp invoked
        obtain ⟨sameKey, sameDemand⟩ := Prod.mk.inj same
        subst key demand
        exact ⟨_, known, rfl⟩
  | discard known resolved permission unprotected admitted =>
      have same := List.mem_singleton.mp member
      obtain ⟨sameKey, sameDemand⟩ := Prod.mk.inj same
      subst key demand
      exact ⟨_, known, rfl⟩
  | scopedResource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      rcases List.mem_append.mp member with first | second
      · exact ihInit first
      · obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
        rw [← hidden_invocations (hidden identity fresh)] at second
        exact ihBody identity fresh second
  | _ => intros; trivial

/-- The checker already contains the complete recursive saved-body trace.
    Only its directly named owner and source-origin demands are needed here. -/

theorem checked_single_owner_demand
    {requirements : Requirements owners}
    (checked : Checked store receiving before requirements row)
    (calls : ∀ key demand, (key, demand) ∈ directInvocations requirements →
      key.owner = owner ∧ demand = modeDemand contract key.mode)
    (noRetirements : directRetirements requirements = []) :
    owners = [] ∨ ∃ mode, owners = owner :: modeDemand contract mode := by
  induction checked with
  | request | spent => exact Or.inl rfl
  | retire => cases noRetirements
  | invoke known ready selection next ih =>
      obtain ⟨sameOwner, sameDemand⟩ := calls _ _ List.mem_cons_self
      exact Or.inr ⟨_, by rw [sameOwner, sameDemand]⟩
  | sequence first second ihFirst ihSecond =>
      have empty := List.append_eq_nil_iff.mp noRetirements
      have left := ihFirst (fun key demand member => calls key demand (List.mem_append_left _ member)) empty.1
      have right := ihSecond (fun key demand member => calls key demand (List.mem_append_right _ member)) empty.2
      rcases left with noLeft | ⟨leftMode, usedLeft⟩
      · simpa only [noLeft, List.nil_append] using right
      · rcases right with noRight | ⟨rightMode, usedRight⟩
        · exact Or.inr ⟨leftMode, by simp only [usedLeft, noRight, List.append_nil]⟩
        · have consumed := OwnerPhaseTransitions.trace_consumed (RecursiveRequirements.checked_trace first)
            (usedLeft ▸ List.mem_cons_self)
          have available := OwnerPhaseTransitions.trace_available (RecursiveRequirements.checked_trace second) owner
            (usedRight ▸ List.mem_cons_self)
          rw [consumed] at available
          cases available
  | emitAfter body exported ih => exact ih calls noRetirements
  | choice first second ihFirst ihSecond =>
      exact ihFirst (fun key demand member => calls key demand (List.mem_append_left _ member))
        (List.append_eq_nil_iff.mp noRetirements).1

theorem source_clause_demand
    (source : SourceTemplates.Expression operations policy contracts world allowed (.ticket binder owner)
      environment code output demand requirements)
    (known : contracts owner = some contract)
    (checked : Checked store receiving before requirements row) :
    demand = [] ∨ ∃ mode, demand = owner :: modeDemand contract mode := by
  apply checked_single_owner_demand checked _ (RecursiveDisposalCapture.expression_no_retirements source)
  intro key nested member
  have named : key.owner ∈ directCalls requirements := by
    rw [← invocation_owners]
    exact List.mem_map.mpr ⟨(key, nested), member, rfl⟩
  obtain ⟨name, dependency, resolved⟩ := RecursiveDisposalCapture.expression_call_ticket source named
  have sameOwner := RecursiveClauses.resolved_owner resolved
  obtain ⟨actual, actualKnown, sameDemand⟩ := source_invocation_contract source member
  rw [sameOwner] at actualKnown
  have sameContract := Option.some.inj (actualKnown.symm.trans known)
  subst actual
  exact ⟨sameOwner, sameDemand⟩

theorem consuming_clause_demand
    (source : SourceTemplates.Expression operations policy contracts world allowed (.ticket binder owner)
      environment code output demand requirements)
    (known : contracts owner = some contract)
    (checked : Checked store receiving before requirements row)
    (ready : before owner = .available) (consumed : spendAll before demand owner = .consumed) :
    ∃ mode, demand = owner :: modeDemand contract mode := by
  rcases source_clause_demand source known checked with empty | used
  · simp only [empty, spendAll, ready] at consumed
    cases consumed
  · exact used

theorem consuming_clause_balance
    (source : SourceTemplates.Expression operations policy contracts world allowed (.ticket binder owner)
      environment code output demand requirements)
    (known : contracts owner = some contract)
    (checked : Checked store receiving before requirements row)
    (ready : before owner = .available) (consumed : spendAll before demand owner = .consumed)
    (balance : contract.closeDemand.Perm contract.resumeDemand) :
    demand.Perm (owner :: contract.resumeDemand) := by
  obtain ⟨mode, same⟩ := consuming_clause_demand source known checked ready consumed
  cases mode with
  | resume => exact same ▸ List.Perm.refl _
  | dispose => exact same ▸ balance.cons owner

/-- Clause entry also covers recursive resource bodies with owner actions. -/
theorem fresh_clause_configuration
    (known : contracts owner = some contract)
    (source : Segment operations policy contracts tables world
      (.live owner inputType answerType capture caller tail) contract.answer output tailDemand
      (.sequence (.spent owner) tailRequirements)
      ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: records))
    (closing : Records operations policy contracts tables world
      (.live owner inputType answerType capture caller tail) disposals)
    (savedCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals))
      (OwnerPhases.ofStack tables tail) before capturedRequirements contract.resumeRow)
    (tailCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals)) []
      (spendAll before contract.resumeDemand) tailRequirements tailRow)
    (phases : spend (available (ownedTickets (.live owner inputType answerType capture caller tail))) owner = before)
    (unique : (ownedTickets (.live owner inputType answerType capture caller tail)).Nodup)
    (current : Expression operations policy contracts world allowed (.ticket binder owner)
      Environment.empty code contract.answer clauseDemand clauseRequirements)
    (currentCheck : Checked ((⟨owner, .resume⟩, ⟨contract.resumeDemand, capturedRequirements⟩) :: (records ++ disposals))
      (OwnerPhases.ofStack tables (.live owner inputType answerType capture caller tail))
      (available (ownedTickets (.live owner inputType answerType capture caller tail)))
      clauseRequirements clauseRow)
    (balance : contract.closeDemand.Perm contract.resumeDemand)
    (completed : spendAll (available (ownedTickets (.live owner inputType answerType capture caller tail)))
      clauseDemand owner = .consumed)
    (accepted : checkFootprint outside (clauseRow ++ tailRow) = true) :
    CheckedState operations policy contracts tables world outside (.ticket binder owner)
      code (.live owner inputType answerType capture caller tail) output
      (clauseDemand ++ tailDemand) (clauseRow ++ tailRow) ∧
    (clauseDemand ++ tailDemand).Perm ((owner :: contract.resumeDemand) ++ tailDemand) := by
  have sameDemand := consuming_clause_balance current known currentCheck
    (by simp [available, ownedTickets]) completed balance
  exact RecursiveDisposalCapture.checked_clause_configuration known source closing savedCheck tailCheck phases unique
    current currentCheck sameDemand accepted

/-- The actual capture construction accepts the full recursive source judgment.
    Clause checking, completion and the footprint bound remain explicit inputs. -/
theorem capture_from_recursive_clause
    (source : CheckedState operations policy contracts tables world outside scope
      (.perform (Instantiation.freezeEffect requested) operation operand) whole output demand row)
    (cut : HandlerCut requested whole capture tail handler)
    (clause : ClauseAt operation handler.clauses parameter binder body)
    (operationKnown : operations requested operation = some (argument, input))
    (isValue : operand.IsValue) (fresh : contracts owner = none)
    (resumeEffects closeEffects : List Instance) (closingRow : Footprint)
    (built : makePlan capture = some plan)
    (internal : InternalUses capture.erase.liveTickets capture.erase.pending) :
    ∃ (contract : Owners.Contract) (offeredContract : ClauseContract) (offered requestRow tailRow raw : Footprint)
      (tailDemand : List Nat) (closingRequirements : Requirements (OwnerClosingSource.retirements plan)) (store : Store),
      contract.input = input ∧ contract.answer.port = ScopedPorts.eraseType handler.answer ∧
      contract.closeDemand = OwnerClosingSource.retirements plan ∧ contract.closeRow = some closingRow ∧
      contract.closeDemand.Perm contract.resumeDemand ∧
      contract.held = ProtectionContexts.protectedMode capture.erase ∧
      contract.resumeEffects = resumeEffects ∧ contract.closeEffects = closeEffects ∧
      PlanTemplate operations policy (contracts.insert owner contract) tables world .none plan raw closingRequirements ∧
      demand = contract.resumeDemand ++ tailDemand ∧
      (tail = .nil → tailDemand = []) ∧
      contract.resumeDemand.Sublist demand ∧
      row = (requestRow ++ contract.resumeRow) ++ tailRow ∧
      lookup operation (tables handler) = some offeredContract ∧
      modeCheck offeredContract.dispose (ProtectionContexts.protectedMode capture.erase) = true ∧
      offeredContract.row (ProtectionContexts.protectedMode capture.erase) = some offered ∧
      residualize (contextOf tables tail) offered = some requestRow ∧
      Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
        (.invoke ⟨owner, .resume⟩ contract.resumeDemand []) contract.resumeRow ∧
      (∀ actualRow, contract.closeRow = some actualRow →
        residualize (contextOf tables tail) raw = some closingRow →
        Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
          (.invoke ⟨owner, .dispose⟩ contract.closeDemand []) actualRow) ∧
      ∀ (allowed : List Instance) (clauseDemand : List Nat) (clauseRow : Footprint)
          (clauseRequirements : Requirements clauseDemand),
        Expression operations policy (contracts.insert owner contract) world allowed (.ticket binder owner)
          (Environment.empty.extend parameter argument) body contract.answer clauseDemand clauseRequirements →
        Checked store
        (OwnerPhases.ofStack tables (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))
        (available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail))) clauseRequirements clauseRow →
        spendAll (available (ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)))
          clauseDemand owner = .consumed → clauseRow ⊆ (requestRow ++ contract.resumeRow) →
        RawStep ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, whole⟩
          ⟨body.subst parameter operand, .ticket binder owner,
            .live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail⟩ [.ticket owner] [] ∧
        CheckedState operations policy (contracts.insert owner contract) tables world outside (.ticket binder owner)
          (body.subst parameter operand) (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail)
          output (clauseDemand ++ tailDemand) (clauseRow ++ tailRow) ∧
        (clauseDemand ++ tailDemand).Perm (owner :: demand) ∧
        (clauseRow ++ tailRow) ⊆ row ∧
        ownedTickets (.live owner (ScopedPorts.embedPort input.port) handler.answer capture handler.scope tail) = owner :: ownedTickets whole := by
  obtain ⟨contract, offeredContract, offered, requestRow, tailRow, raw, tailDemand, closingRequirements, store,
    inputSame, answerSame, closeDemandSame, closeRowSame, balance, held, resumeSame, closeSame,
    template, sameDemand, emptyTail, subDemand, sameRow, offeredKnown, offeredMode, offeredRow, offeredExport,
    resumeCheck, disposeCheck, enter⟩ :=
    RecursiveDisposalCapture.prepare_capture source cut clause operationKnown isValue fresh
      resumeEffects closeEffects closingRow built internal
  refine ⟨contract, offeredContract, offered, requestRow, tailRow, raw, tailDemand, closingRequirements, store,
    inputSame, answerSame, closeDemandSame, closeRowSame, balance, held, resumeSame, closeSame,
    template, sameDemand, emptyTail, subDemand, sameRow, offeredKnown, offeredMode, offeredRow, offeredExport,
    resumeCheck, disposeCheck, ?_⟩
  intro allowed clauseDemand clauseRow requirements current currentCheck completed bounded
  have known : (contracts.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
  have sameClause := consuming_clause_balance current known currentCheck (by simp [available, ownedTickets]) completed balance
  exact enter allowed clauseDemand clauseRow requirements current currentCheck sameClause bounded

namespace ResourceClauseExamples
open RecursiveDisposalCapture.Examples (effect operations operation_known tables)
open RecursiveRecords.Examples (policy)

def contracts : Owners.Contracts := fun _ => none
def clause : Code := .resource 8 (.integer 17) (.discard 1)
def handler : HandlerData := ⟨73, effect, .cons 0 2 1 clause .nil, .none, .unit, rfl⟩
def stack : Stack := .push (.handler handler) .nil
def boundary : Stack := .live 23 .unit .unit stack .none .nil

theorem clauses_usage : ClausesUse policy handler.clauses :=
  .cons (.resource .integer (.discard rfl)) .nil

theorem clauses_typed : ScopedPorts.ClausesTyped operations.ports [] ScopedPorts.TypeEnv.empty effect .unit [] handler.clauses := by
  have body : ScopedPorts.Typed operations.ports [] (ScopedPorts.TypeEnv.empty.extend 2 .unit)
      (.bound 1 .unit .unit [] []) [] clause .unit :=
    .resource (residual := []) .integer
      (fun identity fresh => .discard (by simp))
      (by simp [ScopedPorts.InWorld, ScopedPorts.Port.resources]) (List.Subset.refl []) (List.Subset.refl [])
  exact .cons (port_lookup operation_known) body .nil

theorem handler_typed : ScopedPorts.FrameTyped operations.ports contracts.ports.types [] (.handler handler) := by
  refine .handler (residual := []) ⟨.none, .none⟩ clauses_typed ?_ (by decide)

  intro operation input output known
  by_cases same : operation = 0
  · subst operation
    simp [handler, ScopedTyping.clauseKeys]
  · simp [Operations.ports, operations, same, handler] at known

theorem requesting : CheckedState operations policy contracts tables [] [] .none
    (.perform (Instantiation.freezeEffect effect) 0 .unit) stack .unit [] [] := by
  have pending : Segment operations policy contracts tables [] stack .unit .unit []
      (.sequence ((Requirements.request [] []).prepend []) (.request [] [])) [] :=
    .push (.handler handler_typed rfl) .nil
  have current : Expression operations policy contracts [] [effect] .none Environment.empty
      (.perform (Instantiation.freezeEffect effect) 0 .unit) .unit []
      (.emitAfter (.request [] []) [] [⟨effect, 0, false⟩]) :=
    .perform operation_known List.mem_cons_self (.stable .unit)
      (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])
  have currentCheck : Checked [] (OwnerPhases.ofStack tables stack) (available (ownedTickets stack))
      (.emitAfter (.request [] []) [] [⟨effect, 0, false⟩]) [] :=
    .emitAfter (bodyRow := []) (requestRow := [])
      (.request (by simp [OwnerSource.exportAt, residual_empty])) (by decide)
  have restCheck : Checked [] [] (available (ownedTickets stack))
      (.sequence ((Requirements.request [] []).prepend []) (.request [] [])) [] :=
    .sequence (firstRow := []) (secondRow := [])
      (.request (by simp [OwnerSource.exportAt, residual_empty])) (.request (by simp [OwnerSource.exportAt, residual_empty]))
  have prefixed : Checked [] [] (available (ownedTickets stack))
      ((Requirements.emitAfter (.request [] []) [] [⟨effect, 0, false⟩]).prepend (OwnerPhases.ofStack tables stack)) [] :=
    RecursiveRequirements.checked_prepend_iff.mpr (by simpa only [List.append_nil] using currentCheck)
  exact .checked (.checked current .none pending) (.push .nil) (by decide)
    (.sequence prefixed restCheck) (by decide)

/-- A selected clause allocates a resource whose body disposes its newly
    captured owner. The recursive capture theorem constructs the successor. -/
theorem capture_preserved : ∃ contract : Owners.Contract,
    RawStep ⟨.perform (Instantiation.freezeEffect effect) 0 .unit, .none, stack⟩
      ⟨clause, .ticket 1 23, boundary⟩ [.ticket 23] [] ∧
    CheckedState operations policy (contracts.insert 23 contract) tables [] [] (.ticket 1 23)
      clause boundary .unit [23] [] := by
  obtain ⟨contract, offeredContract, offered, requestRow, tailRow, raw, tailDemand, closingRequirements, store,
    input, annotation, closeDemand, closing, balance, held, resumeEffects, closeEffects, template,
    totalDemand, emptyTail, capturedDemand, totalRow, knownOffer, permitted, offeredRow, exported,
    resumeCheck, disposeCheck, dispatch⟩ :=
    capture_from_recursive_clause requesting (.hit handler .nil rfl) (.hit) operation_known (by trivial)
      (owner := 23) rfl [] [] [] (plan := []) rfl .nil
  have tailEmpty := emptyTail rfl
  have closeEmpty : contract.closeDemand = [] := closeDemand
  obtain ⟨headEmpty, tailRowEmpty⟩ := List.append_eq_nil_iff.mp totalRow.symm
  obtain ⟨requestEmpty, resumeEmpty⟩ := List.append_eq_nil_iff.mp headEmpty
  have answer : contract.answer = .unit := by
    change contract.answer.port = .unit at annotation
    have unit_port : ∀ value : Value, value.port = .unit → value = .unit := by
      intro value port
      cases value <;> cases port <;> rfl
    exact unit_port contract.answer annotation
  have unprotected : contract.held = false := held
  have noCallbacks : raw = [] := by cases template; rfl
  have known : (contracts.insert 23 contract) 23 = some contract := by simp [Owners.Contracts.insert]
  have body : Expression operations policy (contracts.insert 23 contract) [] [] (.ticket 1 23)
      (Environment.empty.extend 2 .unit) clause contract.answer [23]
      (.sequence (.request [] []) (.invoke ⟨23, .dispose⟩ [] [])) := by
    rw [answer]
    apply Expression.scopedResource (residual := [])
      (bodyRequirements := fun _ => .invoke ⟨23, .dispose⟩ [] []) (.stable .integer)
    · intro identity fresh
      have disposed : Expression operations policy (contracts.insert 23 contract) [identity] [Instance.cell identity]
          (.ticket 1 23) (Environment.empty.extend 2 .unit) (.discard 1) .unit
          (23 :: contract.closeDemand) (.invoke ⟨23, .dispose⟩ contract.closeDemand []) :=
        .discard known rfl rfl unprotected (by rw [closeEffects]; exact List.nil_subset _)
      rw [closeEmpty] at disposed
      exact disposed
    · simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]
    · exact List.Subset.refl []
    · exact List.Subset.refl []
    · intro identity fresh
      exact .invoke
  have invocation := disposeCheck [] closing (by simp only [noCallbacks, residual_empty])
  rw [closeEmpty] at invocation
  have checked : Checked store (OwnerPhases.ofStack tables boundary) (available (ownedTickets boundary))
      (.sequence (.request [] []) (.invoke ⟨23, .dispose⟩ [] [])) [] :=
    .sequence (firstRow := []) (secondRow := []) (.request (by simp [OwnerSource.exportAt, residual_empty]))
      (by simpa only [closeEmpty, handler, Value.port, ScopedPorts.embedPort, boundary, stack, spendAll] using invocation)
  obtain ⟨step, successor, demand, included, owned⟩ := dispatch [] [23] [] _ body
    (by simpa only [handler, Value.port, ScopedPorts.embedPort, boundary, stack] using checked)
    (by rfl) (List.nil_subset _)
  exact ⟨contract,
    by simpa [clause, Code.subst, handler, boundary, stack, Value.port, ScopedPorts.embedPort] using step,
    by simpa [tailEmpty, tailRowEmpty, clause, Code.subst, handler, boundary, stack, Value.port, ScopedPorts.embedPort] using successor⟩

end ResourceClauseExamples

end Ash.OneShot.RecursiveClauseOwnership

#print axioms Ash.OneShot.RecursiveClauseOwnership.invocation_owners
#print axioms Ash.OneShot.RecursiveClauseOwnership.hidden_invocations
#print axioms Ash.OneShot.RecursiveClauseOwnership.source_invocation_contract
#print axioms Ash.OneShot.RecursiveClauseOwnership.checked_single_owner_demand
#print axioms Ash.OneShot.RecursiveClauseOwnership.source_clause_demand
#print axioms Ash.OneShot.RecursiveClauseOwnership.consuming_clause_demand
#print axioms Ash.OneShot.RecursiveClauseOwnership.consuming_clause_balance

#print axioms Ash.OneShot.RecursiveClauseOwnership.fresh_clause_configuration

#print axioms Ash.OneShot.RecursiveClauseOwnership.capture_from_recursive_clause

#print axioms Ash.OneShot.RecursiveClauseOwnership.ResourceClauseExamples.handler_typed
#print axioms Ash.OneShot.RecursiveClauseOwnership.ResourceClauseExamples.requesting
#print axioms Ash.OneShot.RecursiveClauseOwnership.ResourceClauseExamples.capture_preserved

#print axioms Ash.OneShot.RecursiveClauseOwnership.ResourceClauseExamples.clauses_typed

#print axioms Ash.OneShot.RecursiveClauseOwnership.invocations_prepend

#print axioms Ash.OneShot.RecursiveClauseOwnership.ResourceClauseExamples.clauses_usage
