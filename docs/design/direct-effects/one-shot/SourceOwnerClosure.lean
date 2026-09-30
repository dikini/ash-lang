import CallableSourceShapes
import CallerOwnerChecks

/-! Derive initial local owner usage from the existing source judgment.
The new induction is the missing source-to-usage projection. Stable usage,
resource instantiation, runtime preservation and caller composition reuse
their existing proofs. Admission of future owner/closing checks stays separate. -/
namespace Ash.OneShot.SourceOwnerClosure
open ScopedExpressions ScopedExecution CoherentSourceTypes

theorem expression_usage
    (source : SourceTemplates.Expression operations policy contracts world allowed scope environment
      code output demand requirements)
    (empty : scope = .none) : Uses policy .none .available code .available := by
  induction source using SourceTemplates.Expression.rec
      (motive_2 := fun world environment allowed code value row _ =>
        Uses policy .none .available code .available) with
  | stable summary =>
      exact ClauseProtection.stable_usage (CoherentSourceTypes.protection_summary summary) policy .none .available
  | callable summary ih => exact ih
  | lambda body outward formed ih => exact .lambda (ih rfl)
  | purePair left right ihLeft ihRight | pair left right ihLeft ihRight => exact .pair (ihLeft empty) (ihRight empty)
  | app function argument admitted ihFunction ihArgument => exact .app (ihFunction empty) (ihArgument empty)
  | bind initializer body ihInit ihBody => exact .bind (ihInit empty) (ihBody empty)
  | branch condition yes no same ihCondition ihYes ihNo =>
      exact .branch (ihCondition empty) (ihYes empty) (ihNo empty)
  | perform known admitted operand formed ih => exact .perform (ih empty)
  | handler body clauses capabilities coverage unique admitted table modes ih => exact .handle (ih empty) capabilities
  | resume known resolved permission operand admitted formed ih | discard known resolved permission unprotected admitted =>
      subst_vars
      cases resolved
  | cleanup callback body admitted ihCallback ihBody => exact .cleanup (ihCallback empty) (ihBody empty)
  | resource initializer body formed effectsBound admitted outward ihInit ihBody =>
      obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
      exact .resource (ihInit empty) ((instantiation_preserves_usage_iff _ _).mp (ihBody identity fresh))
  | scopedResource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
      exact .resource (ihInit empty) ((instantiation_preserves_usage_iff _ _).mp (ihBody identity fresh empty))
  | summaryUnit => exact .unit
  | summaryBoolean => exact .boolean
  | summaryInteger => exact .integer
  | summaryReference issued => exact .resourceRef
  | summaryVariable known formed => exact .variable
  | summaryPair left right ihLeft ihRight => exact .pair ihLeft ihRight
  | summaryLambda body outward formed ih => exact .lambda (ih rfl)
  | summaryApp function argument admitted ihFunction ihArgument => exact .app ihFunction ihArgument
  | summaryBind initializer body ihInit ihBody => exact .bind ihInit ihBody
  | summaryBranch condition yes no ihCondition ihYes ihNo => exact .branch ihCondition ihYes ihNo
  | summaryPerform known admitted operand formed ih => exact .perform ih
  | summaryCleanup callback body admitted ihCallback ihBody => exact .cleanup ihCallback ihBody
  | summaryResource initializer body formed effectsBound admitted outward ihInit ihBody =>
      obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
      exact .resource ihInit ((instantiation_preserves_usage_iff _ _).mp (ihBody identity fresh))

/-- Hereditary source evidence supplies initial ownership usage for any
policy, without a separate Uses premise. This does not supply access checks. -/
theorem initial_usage
    (source : DeclaredSources.Expression operations policy contracts world allowed .none environment
      code output demand requirements) :
    ConfigurationUsage policy tickets ⟨code, .none, .nil⟩ :=
  ⟨[], [], .idle .none (expression_usage (DeclaredSources.expression_erase source) rfl),
    .nil, List.nil_subset _, .refl _, List.nodup_nil⟩

/-- Actual argument instantiation now supplies both grouped source and its
initial local usage. Reuse the callable expansion and source projection. -/
theorem application_initial_usage
    (function : CallableSourceShapes.Callable operations policy contracts world environment allowed
      (.lambda parameter code) (.function input output requests latent) [])
    (argument : CallableSourceShapes.Callable operations policy contracts world environment allowed value input [])
    (closed : ClosedValue value) (admitted : requests ⊆ allowed) :
    ConfigurationUsage policy tickets ⟨code.subst parameter value, .none, .nil⟩ := by
  obtain ⟨requirements, shape, source, described, outward, evaluated⟩ :=
    CallableSourceShapes.application_shape function argument closed admitted
  exact initial_usage source

/-- Reuse the established finite-run invariant, including its explicit
per-step access checks. No intermediate usage invariant is supplied. -/
theorem local_run_interface
    (steps : NamedAccessSteps ambient before after)
    (source : DeclaredSources.Expression operations policy contracts world allowed .none environment
      code output demand requirements)
    (initial : before.execution.configuration = ⟨code, .none, .nil⟩)
    (ledger : Ledger before.execution.erase)
    (history : NameHistory before.execution before.activations)
    (access : AccessValid before.execution.configuration ambient)
    (registry : UsageRegistryHistory tickets before.execution.issued) :
    ∃ nextTickets nextDemand,
      StackUsage policy nextTickets after.execution.configuration.stack [] nextDemand ∧
      InternalUses after.execution.configuration.stack.erase.liveTickets
        after.execution.configuration.stack.erase.pending := by
  have usage : ConfigurationUsage policy tickets before.execution.configuration :=
    initial.symm ▸ initial_usage source
  obtain ⟨nextTickets, nextLedger, nextHistory, nextAccess, nextUsage, nextRegistry⟩ :=
    named_access_steps_joint_usage steps ledger history access usage registry
  obtain ⟨currentDemand, nextDemand, current, pending, available, balance, unique⟩ := nextUsage
  exact ⟨nextTickets, nextDemand, pending, CallerOwnerChecks.closed_prefix_internal pending⟩

/-- The local interface at an outward request now follows from source entry
and the existing checked local run, rather than a separately supplied callee
usage premise. The run's access checks are still explicit admission evidence. -/
theorem local_run_outward_owner_check
    (steps : NamedAccessSteps ambient before after)
    (source : DeclaredSources.Expression operations policy contracts world allowed .none environment
      code output demand requirements)
    (initial : before.execution.configuration = ⟨code, .none, .nil⟩)
    (ledger : Ledger before.execution.erase)
    (history : NameHistory before.execution before.activations)
    (access : AccessValid before.execution.configuration ambient)
    (registry : UsageRegistryHistory tickets before.execution.issued)
    (callerUsage : StackUsage callerPolicy callerTickets caller [] callerDemand)
    (unique : (ownedTickets (after.execution.configuration.stack.append caller)).Nodup)
    (cut : HandlerCut requested caller capture tail handler)
    (unresolved : after.execution.configuration.stack.erase.resolve requested = none) :
    OwnerOfferContexts.checkOwner requested operation
      (OwnerOfferContexts.ofStack tables (after.execution.configuration.stack.append caller)) =
    OwnerOfferContexts.checkOwner requested operation (OwnerOfferContexts.ofStack tables caller) := by
  obtain ⟨nextTickets, nextDemand, localUsage, internal⟩ :=
    local_run_interface steps source initial ledger history access registry
  exact CallerOwnerChecks.outward_owner_check localUsage callerUsage unique cut unresolved

/-- Replacing a ready outward request by an already usage-checked value
preserves the local ownership configuration. This is a projection for a reply,
not an additional reduction rule. The caller may extend the ticket registry
and return in a different registered continuation scope. -/
theorem request_reply_usage
    (localUsage : ConfigurationUsage policy beforeTickets
      ⟨.perform requested operation operand, localScope, localStack⟩)
    (operandValue : operand.IsValue)
    (extension : Syntax.UsageExtension beforeTickets afterTickets)
    (reply : CodeDemand policy afterTickets replyScope value replyDemand)
    (valueReady : value.IsValue) :
    ConfigurationUsage policy afterTickets ⟨value, replyScope, localStack⟩ := by
  obtain ⟨currentDemand, controlDemand, current, pending, available, balance, unique⟩ := localUsage
  have empty := perform_value_demand_empty current operandValue
  subst currentDemand
  exact ⟨[], controlDemand,
    code_demand_value_transport reply valueReady (Syntax.code_demand_scope reply),
    stack_usage_extension pending extension, List.nil_subset _, balance, unique⟩

/-- The existing full resumption proof supplies the returned value's usage.
The saved local request interface then supplies a separately balanced local
restart, with the actual resumer scope. Full caller admission and registry
extension are premises; no intervening caller run is inferred here. -/
theorem resume_local_usage {localStack callerCapture front tail : Stack}
    (localUsage : ConfigurationUsage policy beforeTickets
      ⟨.perform requested operation operand, localScope, localStack⟩)
    (operandValue : operand.IsValue)
    (extension : Syntax.UsageExtension beforeTickets afterTickets)
    (resuming : ConfigurationUsage policy afterTickets
      ⟨.resume binder value, replyScope,
        front.append (.live owner input answer (localStack.append callerCapture) callerScope tail)⟩)
    (resolved : replyScope.resolve binder = some owner)
    (closed : ClosedValue value) :
    RawStep
      ⟨.resume binder value, replyScope,
        front.append (.live owner input answer (localStack.append callerCapture) callerScope tail)⟩
      ⟨value, replyScope,
        (localStack.append callerCapture).append (front.append (.spent owner answer callerScope tail))⟩
      [] [.ticket owner] ∧
    ConfigurationUsage policy afterTickets
      ⟨value, replyScope,
        (localStack.append callerCapture).append (front.append (.spent owner answer callerScope tail))⟩ ∧
    ConfigurationUsage policy afterTickets ⟨value, replyScope, localStack⟩ := by
  have restored := resume_preserves_configuration_usage resuming resolved closed.1
  obtain ⟨currentDemand, controlDemand, current, pending, available, balance, unique⟩ := restored
  exact ⟨RawStep.resume binder owner replyScope callerScope input answer front
      (localStack.append callerCapture) tail value closed resolved,
    ⟨currentDemand, controlDemand, current, pending, available, balance, unique⟩,
    request_reply_usage localUsage operandValue extension current closed.1⟩

/-- An arbitrary finite access-checked caller run supplies both full resume
usage and registry extension. The saved local interface need only be checked
at the start of that run, not again at its endpoint. The endpoint retains the
same saved local prefix; preservation of that decomposition is separate. -/
theorem caller_run_resume_local_usage {localStack callerCapture front tail : Stack}
    (steps : NamedAccessSteps ambient before after)
    (localUsage : ConfigurationUsage policy tickets
      ⟨.perform requested operation operand, localScope, localStack⟩)
    (operandValue : operand.IsValue)
    (ledger : Ledger before.execution.erase)
    (history : NameHistory before.execution before.activations)
    (access : AccessValid before.execution.configuration ambient)
    (usage : ConfigurationUsage policy tickets before.execution.configuration)
    (registry : UsageRegistryHistory tickets before.execution.issued)
    (endpoint : after.execution.configuration =
      ⟨.resume binder value, replyScope,
        front.append (.live owner input answer (localStack.append callerCapture) callerScope tail)⟩)
    (resolved : replyScope.resolve binder = some owner)
    (closed : ClosedValue value) :
    ∃ afterTickets,
      RawStep after.execution.configuration
        ⟨value, replyScope,
          (localStack.append callerCapture).append (front.append (.spent owner answer callerScope tail))⟩
        [] [.ticket owner] ∧
      ConfigurationUsage policy afterTickets
        ⟨value, replyScope,
          (localStack.append callerCapture).append (front.append (.spent owner answer callerScope tail))⟩ ∧
      ConfigurationUsage policy afterTickets ⟨value, replyScope, localStack⟩ := by
  obtain ⟨afterTickets, nextLedger, nextHistory, nextAccess, nextUsage, nextRegistry, extension⟩ :=
    named_access_steps_joint_usage_extension steps ledger history access usage registry
  have resuming := endpoint ▸ nextUsage
  obtain ⟨raw, full, restarted⟩ :=
    resume_local_usage localUsage operandValue extension resuming resolved closed
  exact ⟨afterTickets, endpoint.symm ▸ raw, full, restarted⟩

end Ash.OneShot.SourceOwnerClosure

#print axioms Ash.OneShot.SourceOwnerClosure.expression_usage
#print axioms Ash.OneShot.SourceOwnerClosure.initial_usage
#print axioms Ash.OneShot.SourceOwnerClosure.application_initial_usage
#print axioms Ash.OneShot.SourceOwnerClosure.local_run_interface
#print axioms Ash.OneShot.SourceOwnerClosure.local_run_outward_owner_check
#print axioms Ash.OneShot.SourceOwnerClosure.request_reply_usage
#print axioms Ash.OneShot.SourceOwnerClosure.resume_local_usage
#print axioms Ash.OneShot.SourceOwnerClosure.caller_run_resume_local_usage
