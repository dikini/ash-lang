import DeclaredCaptureRetention

/-! Resource and handler installation choose annotations through the existing source
proof. Actual stack typing fixes the chosen result port, so the same fresh
opening preserves the independently checked effect interface.
-/
namespace Ash.OneShot.ScopedActionInterfaces
open ScopedExpressions ScopedExecution ScopedPorts

/-- Runtime frame annotations determine a stack's input port. This is
constructor inversion, independent of the worlds or typing derivations. -/
theorem stack_input_unique
    (first : StackTyped signature tickets world stack input result)
    (second : StackTyped otherSignature otherTickets otherWorld stack otherInput result) :
    input = otherInput := by
  cases first <;> cases second <;> rfl

/-- The source-produced successor supplies its actual annotation through port
typing. Fresh resource opening and the existing effect-frame rule do the rest. -/
theorem resource_preserves_configuration
    (before : ConfigurationConnected signature tickets actions (ScopedTyping.resourceWorld issued)
      ⟨.resource binder initializer body, scope, tail⟩ result outgoing)
    (fresh : Owner.resource identity ∉ issued)
    (after : ConfigurationTyped signature tickets.types
      (ScopedTyping.resourceWorld (issued ++ [.resource identity]))
      ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ result) :
    ConfigurationConnected signature tickets actions
      (ScopedTyping.resourceWorld (issued ++ [.resource identity]))
      ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) tail⟩ result outgoing := by
  obtain ⟨input, effects, expression, stack, connected⟩ := before
  obtain ⟨afterInput, afterExpression, afterStack⟩ := after
  cases afterStack with
  | push frame rest =>
      have aligned : input = eraseType answer := stack_input_unique stack rest
      cases expression with
      | checked scopeTyped expression =>
          obtain ⟨residual, bodyTyped, noEscape, noEffectEscape, available⟩ :=
            resource_body_typed_at_fresh expression fresh
          have larger : ScopedTyping.resourceWorld issued ⊆
              ScopedTyping.resourceWorld (issued ++ [.resource identity]) := by
            rw [ScopedTyping.resource_world_append]
            exact List.subset_append_left _ _
          have effectFrame : EffectFrame signature tickets
              (ScopedTyping.resourceWorld (issued ++ [.resource identity]))
              (.cell identity payload scope answer) (.cell identity :: residual) residual :=
            .cell ⟨_, scopeTyped⟩ (aligned ▸ noEscape)
          refine ⟨eraseType answer, .cell identity :: residual,
            .checked scopeTyped (aligned ▸ bodyTyped), .push frame rest, ?_⟩
          exact .push effectFrame (input_weaken (world_weaken connected larger) available)
            (List.Subset.refl _)

theorem handler_preserves_configuration
    (before : ConfigurationConnected signature tickets actions world
      ⟨.handle (Instantiation.freezeEffect handler.effectInst) body handler.clauses, handler.scope, tail⟩ result outgoing)
    (after : ConfigurationTyped signature tickets.types world
      ⟨body, handler.scope, .push (.handler handler) tail⟩ result) :
    ConfigurationConnected signature tickets actions world
      ⟨body, handler.scope, .push (.handler handler) tail⟩ result outgoing := by
  obtain ⟨input, effects, expression, stack, connected⟩ := before
  obtain ⟨afterInput, afterExpression, afterStack⟩ := after
  cases afterStack with
  | push frame rest =>
      have aligned : input = eraseType handler.answer := stack_input_unique stack rest
      cases expression with
      | checked scopeTyped expression =>
          generalize encoded : Instantiation.freezeEffect handler.effectInst = effect at expression
          cases expression with
          | handle bodyTyped clauses coverage unique available =>
              cases freeze_effect_injective encoded
              have effectFrame := EffectFrame.handler ⟨_, scopeTyped⟩ (aligned ▸ clauses) coverage unique
              exact ⟨eraseType handler.answer, _, .checked scopeTyped (aligned ▸ bodyTyped),
                .push frame rest, .push effectFrame (input_weaken connected available) (List.Subset.refl _)⟩

theorem raw_handler_preserves_configuration
    (before : ConfigurationConnected signature tickets actions world first result outgoing)
    (raw : RawStep first after created discharged)
    (form : ∃ effect body clauses, first.expression = .handle effect body clauses)
    (ports : ConfigurationTyped signature tickets.types world after result) :
    ConfigurationConnected signature tickets actions world after result outgoing := by
  obtain ⟨effect, body, clauses, same⟩ := form
  cases raw <;> try cases same
  all_goals try
    have impossible : ClosedValue (.handle effect body clauses) := by assumption
    cases impossible.1
  case focus plain tail focused => cases focused
  case enterHandler => exact handler_preserves_configuration before ports

end Ash.OneShot.ScopedActionInterfaces

namespace Ash.OneShot.DeclaredClosingInvariant
open ScopedExpressions ScopedExecution CoherentSourceTypes

/-- Reuse source-directed resource allocation and join all components at its
actual fresh identity and result annotation. No successor premise is supplied. -/
theorem resource_progress
    (before : Prepared operations declarations policy registry tables
      ⟨⟨⟨.resource binder initializer body, scope, stack⟩, issued, completed⟩, activations⟩ output demand row bound)
    (isValue : initializer.IsValue) :
    ∃ identity payload answer,
      initializer = .integer payload ∧
      let state : NamedState := ⟨⟨⟨.resource binder initializer body, scope, stack⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body.instantiate (Instantiation.Environment.empty.bind binder identity), scope,
        .push (.cell identity payload scope answer) stack⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [.resource identity] []) ∧
      Prepared operations declarations policy registry tables
        (ScopedPortJoint.advanceState state after [.resource identity] []) output demand row bound := by
  obtain ⟨identity, payload, answer, same, step, current⟩ := DeclaredExecution.resource_entry before.current isValue
  obtain ⟨created, discharged, raw, issuedSame, completedSame, freshOwners⟩ := named_event_parts step
  have createdSame : [.resource identity] = created := List.append_cancel_left issuedSame
  have dischargedSame : [] = discharged := List.append_cancel_right completedSame
  subst created
  subst discharged
  have fresh : Owner.resource identity ∉ issued := by
    intro member
    exact (List.nodup_append.mp freshOwners).2.2 _ member _ List.mem_cons_self rfl
  obtain ⟨actions, usage, history, interfaces, retained⟩ := before.actions
  obtain ⟨nextActions, nextUsage, nextHistory, extension⟩ := ScopedActionUsage.named_step_preserves step usage history
  have connected := ScopedActionInterfaces.resource_preserves_configuration interfaces fresh
    (DeclaredReturnAdmission.ports current.source)
  have larger : ScopedTyping.resourceWorld issued ⊆
      ScopedTyping.resourceWorld (issued ++ [.resource identity]) := by
    rw [ScopedTyping.resource_world_append]
    exact List.subset_append_left _ _
  have unique : (ownedTickets (.push (.cell identity payload scope answer) stack)).Nodup := by
    cases current.source with
    | checked _ _ unique _ _ => exact unique
  refine ⟨identity, payload, answer, same, step, current,
    nextActions, nextUsage, nextHistory,
    ScopedActionInterfaces.configuration_action_extension connected extension, ?_⟩
  exact raw_step_preserves_retained raw retained (fun _ _ known => known) extension larger
    (.none (by simp)) unique

/-- The selected source handler frame fixes its result port and code. Runtime
registration and all strengthened-state facets use the same fresh activation. -/
theorem handler_progress
    (before : Prepared operations declarations policy registry tables
      ⟨⟨⟨.handle requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩ output demand row bound) :
    ∃ (handler : HandlerData) (table : List (Nat × ProtectionContracts.ClauseContract)),
      handler.activation ∉ activations ∧
      let state : NamedState := ⟨⟨⟨.handle requested body clauses, scope, stack⟩, issued, completed⟩, activations⟩
      let after : Configuration := ⟨body, scope, .push (.handler handler) stack⟩
      NamedAccessStep [] state (ScopedPortJoint.advanceState state after [] []) ∧
      Prepared operations declarations policy registry
        (RecursiveHandlerTables.register tables handler.activation table)
        (ScopedPortJoint.advanceState state after [] []) output demand row bound := by
  obtain ⟨handler, table, fresh, step, current⟩ := DeclaredExecution.handler_entry before.current
  obtain ⟨created, discharged, raw, issuedSame, completedSame, freshOwners⟩ := named_event_parts step
  have createdSame : [] = created := List.append_cancel_left issuedSame
  have dischargedSame : [] = discharged := List.append_cancel_right completedSame
  subst created
  subst discharged
  obtain ⟨actions, usage, history, interfaces, retained⟩ := before.actions
  obtain ⟨nextActions, nextUsage, nextHistory, extension⟩ := ScopedActionUsage.named_step_preserves step usage history
  have connected := ScopedActionInterfaces.raw_handler_preserves_configuration interfaces raw
    ⟨requested, body, clauses, rfl⟩ (by simpa only [ScopedPortJoint.advanceState, List.append_nil] using DeclaredReturnAdmission.ports current.source)
  have unique : (ownedTickets (.push (.handler handler) stack)).Nodup := by
    cases current.source with
    | checked _ _ unique _ _ => exact unique
  refine ⟨handler, table, fresh, step, current, nextActions, nextUsage, nextHistory, ?_, ?_⟩
  · simpa only [ScopedPortJoint.advanceState, List.append_nil] using
      ScopedActionInterfaces.configuration_action_extension connected extension
  · simpa only [ScopedPortJoint.advanceState, List.append_nil] using
      raw_step_preserves_retained raw retained (fun _ _ known => known) extension (List.Subset.refl _)
        (.none (by simp)) unique

end Ash.OneShot.DeclaredClosingInvariant

#print axioms Ash.OneShot.ScopedActionInterfaces.stack_input_unique
#print axioms Ash.OneShot.ScopedActionInterfaces.resource_preserves_configuration
#print axioms Ash.OneShot.DeclaredClosingInvariant.resource_progress
#print axioms Ash.OneShot.ScopedActionInterfaces.handler_preserves_configuration
#print axioms Ash.OneShot.ScopedActionInterfaces.raw_handler_preserves_configuration
#print axioms Ash.OneShot.DeclaredClosingInvariant.handler_progress
