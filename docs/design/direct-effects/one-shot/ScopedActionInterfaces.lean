import ScopedActionUsage
import DeclaredSources

/-! Structural effect interfaces guarded by independently checked continuation
actions. This reuses existing expression, frame, port and closing-plan judgments.
A dormant computation needs an executable effect interface only if its clause
can resume it; a closing interface needs caller support only if it can dispose.
No runtime permission or declaration is rewritten. This is a replacement for
the unconditional live-boundary premise, not yet a full source progress theorem.
-/
namespace Ash.OneShot.ScopedActionInterfaces
open ScopedExpressions ScopedExecution ScopedPorts

inductive Connected (signature : Signature) (tickets : EffectTickets) (actions : Syntax.UsageTickets)
    (world : List Nat) : Stack → List Instance → List Instance → Prop where
  | nil (bound : incoming ⊆ outgoing) : Connected signature tickets actions world .nil incoming outgoing
  | push (frame : EffectFrame signature tickets world entry inner outer)
      (rest : Connected signature tickets actions world tail outer outgoing) (bound : incoming ⊆ inner) :
      Connected signature tickets actions world (.push entry tail) incoming outgoing
  | live (known : tickets owner = some contract) (actionKnown : actions owner = some rights)
      (scope : EffectScopeKnown tickets caller)
      (saved : rights.resume = true → Connected signature tickets actions world capture [] contract.resumeEffects)
      (rest : Connected signature tickets actions world tail boundary outgoing)
      (resume : rights.resume = true → contract.resumeEffects ⊆ boundary)
      (close : rights.dispose = true → contract.closeEffects ⊆ boundary)
      (bound : incoming ⊆ boundary) :
      Connected signature tickets actions world (.live owner input answer capture caller tail) incoming outgoing
  | spent (known : tickets owner = some contract) (scope : EffectScopeKnown tickets caller)
      (rest : Connected signature tickets actions world tail boundary outgoing) (bound : incoming ⊆ boundary) :
      Connected signature tickets actions world (.spent owner answer caller tail) incoming outgoing

theorem input_weaken (typed : Connected signature tickets actions world stack incoming outgoing)
    (bound : smaller ⊆ incoming) : Connected signature tickets actions world stack smaller outgoing := by
  cases typed with
  | nil old => exact .nil (List.Subset.trans bound old)
  | push frame rest old => exact .push frame rest (List.Subset.trans bound old)
  | live known actionKnown scope saved rest resume close old =>
      exact .live known actionKnown scope saved rest resume close (List.Subset.trans bound old)
  | spent known scope rest old => exact .spent known scope rest (List.Subset.trans bound old)

theorem output_weaken (typed : Connected signature tickets actions world stack incoming outgoing)
    (bound : outgoing ⊆ larger) : Connected signature tickets actions world stack incoming larger := by
  induction typed with
  | nil old => exact .nil (List.Subset.trans old bound)
  | push frame rest input ih => exact .push frame (ih bound) input
  | live known actionKnown scope saved rest resume close input ihSaved ihRest =>
      exact .live known actionKnown scope saved (ihRest bound) resume close input
  | spent known scope rest input ih => exact .spent known scope (ih bound) input

theorem append (front : Connected signature tickets actions world left incoming middle)
    (tail : Connected signature tickets actions world right middle outgoing) :
    Connected signature tickets actions world (left.append right) incoming outgoing := by
  induction front with
  | nil bound => exact input_weaken tail bound
  | push frame rest bound ih => exact .push frame (ih tail) bound
  | live known actionKnown scope saved rest resume close bound ihSaved ihRest =>
      exact .live known actionKnown scope saved (ihRest tail) resume close bound
  | spent known scope rest bound ih => exact .spent known scope (ih tail) bound

theorem decompose (front : Stack)
    (typed : Connected signature tickets actions world (front.append tail) incoming outgoing) :
    ∃ middle, Connected signature tickets actions world front incoming middle ∧
      Connected signature tickets actions world tail middle outgoing := by
  induction front generalizing incoming with
  | nil => exact ⟨incoming, .nil (List.Subset.refl _), typed⟩
  | push entry rest ih => cases typed with
      | push frame rest bound =>
          obtain ⟨middle, inside, outside⟩ := ih rest
          exact ⟨middle, .push frame inside bound, outside⟩
  | live owner input answer saved caller rest ihSaved ihRest => cases typed with
      | live known actionKnown scope saved rest resume close bound =>
          obtain ⟨middle, inside, outside⟩ := ihRest rest
          exact ⟨middle, .live known actionKnown scope saved inside resume close bound, outside⟩
  | spent owner answer caller rest ih => cases typed with
      | spent known scope rest bound =>
          obtain ⟨middle, inside, outside⟩ := ih rest
          exact ⟨middle, .spent known scope inside bound, outside⟩

/-- Every formerly connected stack remains connected. The new action registry
only needs to cover the existing owner registrations; it need not grant both actions. -/
theorem from_scoped (typed : EffectStack signature tickets world stack incoming outgoing)
    (registered : ∀ owner contract, tickets owner = some contract → ∃ rights, actions owner = some rights) :
    Connected signature tickets actions world stack incoming outgoing := by
  induction typed with
  | nil bound => exact .nil bound
  | push frame rest bound ih => exact .push frame ih bound
  | @live owner contract caller capture captured tail boundary outgoing incoming input answer
      known scope saved rest resume close bound ihSaved ihRest =>
      obtain ⟨rights, actionKnown⟩ := registered owner contract known
      exact .live known actionKnown scope (fun _ => input_weaken ihSaved (List.nil_subset _))
        ihRest (fun _ => resume) (fun _ => close) bound
  | spent known scope rest bound ih => exact .spent known scope ih bound

/-- Existing frame forwarding supplies nearest-provider resolution. Dormant
captures never participate in resolving an active request. -/
theorem provides_or_exports (typed : Connected signature tickets actions world stack incoming outgoing)
    (used : request ∈ incoming) :
    (∃ target, stack.erase.resolve request = some target) ∨ request ∈ outgoing := by
  induction typed with
  | nil bound => exact Or.inr (bound used)
  | @push entry inner outer tail outgoing incoming frame rest bound ih =>
      rcases effect_frame_forwards frame (bound used) with ⟨target, found⟩ | forwarded
      · exact Or.inl ⟨target, by simp [Stack.erase, Control.resolve, found]⟩
      · rcases ih forwarded with ⟨target, found⟩ | exported
        · cases first : entry.erase.resolve request with
          | none => exact Or.inl ⟨target, by simp [Stack.erase, Control.resolve, first, found]⟩
          | some nearer => exact Or.inl ⟨nearer, by simp [Stack.erase, Control.resolve, first]⟩
        · exact Or.inr exported
  | live known actionKnown scope saved rest resume close bound ihSaved ihRest => exact ihRest (bound used)
  | spent known scope rest bound ih => exact ih (bound used)

/-- Actual resumption selects the saved derivation using its independent action
check. The unused closing interface is absent from this proof. -/
theorem resume_recomposition {front capture tail : Stack}
    (known : tickets owner = some contract) (actionKnown : actions owner = some rights)
    (permitted : rights.resume = true)
    (typed : Connected signature tickets actions world
      (front.append (.live owner input answer capture caller tail)) incoming outgoing)
    (allowed : contract.resumeEffects ⊆ incoming) :
    Connected signature tickets actions world (capture.append (front.append (.spent owner answer caller tail))) [] outgoing := by
  obtain ⟨middle, inside, outside⟩ := decompose front typed
  cases outside with
  | live actual actualAction scope saved rest resume close bound =>
      have sameContract := Option.some.inj (known.symm.trans actual)
      have sameRights := Option.some.inj (actionKnown.symm.trans actualAction)
      cases sameContract
      cases sameRights
      exact append (output_weaken (saved permitted) allowed) (append inside (.spent actual scope rest bound))

/-- A disposing owner must have a supported closing interface at its own
boundary. Prefix frames can add nearer providers without invalidating resolution. -/
theorem closing_requests {front capture tail : Stack}
    (known : tickets owner = some contract) (actionKnown : actions owner = some rights)
    (permitted : rights.dispose = true)
    (typed : Connected signature tickets actions world
      (front.append (.live owner input answer capture caller tail)) incoming []) :
    RequestsResolved (front.append (.live owner input answer capture caller tail)).erase contract.closeEffects := by
  obtain ⟨middle, inside, outside⟩ := decompose front typed
  cases outside with
  | live actual actualAction scope saved rest resume close bound =>
      have sameContract := Option.some.inj (known.symm.trans actual)
      have sameRights := Option.some.inj (actionKnown.symm.trans actualAction)
      cases sameContract
      cases sameRights
      have resolved : RequestsResolved tail.erase contract.closeEffects := by
        intro request used
        rcases provides_or_exports rest (close permitted used) with found | impossible
        · exact found
        · cases impossible
      have liveResolved : RequestsResolved (Stack.live owner input answer capture caller tail).erase contract.closeEffects := resolved
      simpa only [erase_append] using Admission.requests_resolved_under_prefix liveResolved front.erase

/-- Actual runtime ports remain checked independently of effect connectivity. -/
def ConfigurationConnected (signature : Signature) (tickets : EffectTickets) (actions : Syntax.UsageTickets)
    (world : List Nat) (configuration : Configuration) (result : Port) (outgoing : List Instance) : Prop :=
  ∃ input effects, EffectAtType signature tickets world configuration.scope configuration.expression input effects ∧
    StackTyped signature tickets.types world configuration.stack input result ∧
    Connected signature tickets actions world configuration.stack effects outgoing

theorem configuration_has_types
    (typed : ConfigurationConnected signature tickets actions world configuration result outgoing) :
    ConfigurationTyped signature tickets.types world configuration result := by
  obtain ⟨input, effects, expression, stack, connected⟩ := typed
  cases expression with
  | checked scope expression => exact ⟨input, .checked (effect_scope_has_types scope) expression, stack⟩

theorem configuration_from_scoped
    (typed : EffectConfigurationTyped signature tickets world configuration result outgoing)
    (registered : ∀ owner contract, tickets owner = some contract → ∃ rights, actions owner = some rights) :
    ConfigurationConnected signature tickets actions world configuration result outgoing := by
  obtain ⟨input, effects, expression, stack, connected⟩ := typed
  exact ⟨input, effects, expression, stack, from_scoped connected registered⟩

theorem current_request_has_interpretation
    (typed : ConfigurationConnected signature tickets actions world
      ⟨.perform (Instantiation.freezeEffect requested) operation operand, scope, stack⟩ result []) :
    ∃ target, stack.erase.resolve requested = some target := by
  obtain ⟨input, effects, expression, ports, connected⟩ := typed
  cases expression with
  | checked scope expression =>
      obtain ⟨argument, known, available, operand⟩ := typed_perform_inversion expression
      rcases provides_or_exports connected available with found | impossible
      · exact found
      · cases impossible

/-- The existing port recomposition and value transport are reused. Only the
interface recomposition changes, using the independently checked resume action. -/
theorem resume_preserves_configuration {front capture tail : Stack}
    (resolved : scope.resolve binder = some owner) (actionKnown : actions owner = some rights)
    (permitted : rights.resume = true)
    (typed : ConfigurationConnected signature tickets actions world
      ⟨.resume binder value, scope, front.append (.live owner input answer capture caller tail)⟩ result outgoing)
    (isValue : value.IsValue) :
    ConfigurationConnected signature tickets actions world
      ⟨value, scope, capture.append (front.append (.spent owner answer caller tail))⟩ result outgoing := by
  obtain ⟨expressionType, effects, expression, stack, connected⟩ := typed
  cases expression with
  | checked scopeTyped expression => cases expression with
      | resume operand resumeEffects formed => cases scopeTyped with
          | bound known =>
              simp [Execution.Scope.resolve] at resolved
              subst owner
              obtain ⟨middle, frontTyped, outside⟩ := stack_typed_decompose front stack
              cases outside with
              | live actual caller saved rest =>
                  have projected := actual
                  simp only [EffectTickets.types, known, Option.map_some] at projected
                  obtain ⟨inputPort, answerPort⟩ := Prod.mk.inj (Option.some.inj projected)
                  rw [answerPort] at frontTyped
                  refine ⟨_, [], .checked (.bound known) (typed_value_transport operand isValue _ []), ?_,
                    resume_recomposition known actionKnown permitted connected resumeEffects⟩
                  rw [inputPort]
                  exact stack_typed_append saved (stack_typed_append frontTyped (.spent actual caller rest))

theorem live_to_spent
    (typed : Connected signature tickets actions world (.live owner input answer capture caller tail) incoming outgoing) :
    Connected signature tickets actions world (.spent owner answer caller tail) incoming outgoing := by
  cases typed with
  | live known actionKnown scope saved rest resume close bound => exact .spent known scope rest bound

/-- Plan construction, callback typing and runtime port preservation use the
existing disposal proofs. Permission and structural closing compatibility remain
separate; the certificate supplies the plan's declared effect interface. -/
theorem discard_preserves_configuration {front capture tail : Stack}
    (known : tickets owner = some contract) (resolved : scope.resolve binder = some owner)
    (typed : ConfigurationConnected signature tickets actions world
      ⟨.discard binder, scope, front.append (.live owner input answer capture caller tail)⟩ result outgoing)
    (built : makePlan capture = some plan) (planTyped : PlanTyped signature world contract.closeEffects plan)
    (registered : ∀ owner contract, tickets owner = some contract → ∃ rights, actions owner = some rights) :
    ConfigurationConnected signature tickets actions world
      ⟨.unit, scope, (closeControl scope plan).append
        (.push (.closing closeId scope) (front.append (.spent owner answer caller tail)))⟩ result outgoing := by
  have oldAfter := discard_preserves_configuration_typing (closeId := closeId) resolved built (configuration_has_types typed)
  obtain ⟨oldInput, oldExpression, oldStack⟩ := oldAfter
  cases oldExpression with
  | checked oldScope oldExpression => cases oldExpression with
      | unit =>
          obtain ⟨input, effects, expression, stack, connected⟩ := typed
          cases expression with
          | checked scopeTyped expression => cases expression with
              | discard closeAllowed => cases scopeTyped with
                  | bound actual =>
                      simp [Execution.Scope.resolve] at resolved
                      subst owner
                      have same := Option.some.inj (known.symm.trans actual)
                      cases same
                      obtain ⟨middleType, frontTypes, liveTypes⟩ := stack_typed_decompose front stack
                      cases liveTypes with
                      | live oldKnown oldCaller capturedTypes outsideTypes =>
                          have contents := make_plan_retains_types capturedTypes built
                          have closeEffects := from_scoped
                            (close_plan_has_effect_interface contents planTyped ⟨_, .bound (binder := binder) actual⟩) registered
                          obtain ⟨middle, inside, outside⟩ := decompose front connected
                          refine ⟨.unit, [], .checked (.bound actual) .unit, oldStack, ?_⟩
                          apply input_weaken (append (output_weaken closeEffects closeAllowed)
                            (.push (.closing ⟨_, .bound actual⟩) (append inside (live_to_spent outside)) (List.Subset.refl _)))
                          exact List.nil_subset _

theorem world_weaken (typed : Connected signature tickets actions world stack incoming outgoing)
    (larger : world ⊆ next) : Connected signature tickets actions next stack incoming outgoing := by
  induction typed with
  | nil bound => exact .nil bound
  | push frame rest bound ih => exact .push (effect_frame_world_weaken frame larger) ih bound
  | live known actionKnown scope saved rest resume close bound ihSaved ihRest =>
      exact .live known actionKnown scope ihSaved ihRest resume close bound
  | spent known scope rest bound ih => exact .spent known scope ih bound

theorem action_extension (typed : Connected signature tickets actions world stack incoming outgoing)
    (extension : Syntax.UsageExtension actions next) : Connected signature tickets next world stack incoming outgoing := by
  induction typed with
  | nil bound => exact .nil bound
  | push frame rest bound ih => exact .push frame ih bound
  | live known actionKnown scope saved rest resume close bound ihSaved ihRest =>
      exact .live known (extension _ _ actionKnown) scope ihSaved ihRest resume close bound
  | spent known scope rest bound ih => exact .spent known scope ih bound

theorem configuration_world_weaken
    (typed : ConfigurationConnected signature tickets actions world configuration result outgoing) (larger : world ⊆ next) :
    ConfigurationConnected signature tickets actions next configuration result outgoing := by
  obtain ⟨input, effects, expression, stack, connected⟩ := typed
  cases expression with
  | checked scope expression =>
      exact ⟨input, effects, .checked scope (typed_world_weaken expression next larger),
        stack_world_weaken stack larger, world_weaken connected larger⟩

theorem configuration_action_extension
    (typed : ConfigurationConnected signature tickets actions world configuration result outgoing)
    (extension : Syntax.UsageExtension actions next) :
    ConfigurationConnected signature tickets next world configuration result outgoing := by
  obtain ⟨input, effects, expression, stack, connected⟩ := typed
  exact ⟨input, effects, expression, stack, action_extension connected extension⟩

/-- Port, frame and value proofs are unchanged. The eight value transitions
inspect only active frames or a spent boundary, so the existing case construction
also preserves the action-guarded connections without inspecting dormant code. -/
theorem raw_value_preserves_configuration
    (step : RawStep before after created discharged) (closed : ClosedValue before.expression)
    (typed : ConfigurationConnected signature tickets actions world before result outgoing) :
    ConfigurationConnected signature tickets actions world after result outgoing := by
  obtain ⟨input, effects, expression, stack, effectStack⟩ := typed
  cases step with
  | focus plain focus tail => exact False.elim (ScopedPorts.focus_is_not_value focus closed.1)
  | bind | beta | ifTrue | ifFalse | enterHandler | enterCell | enterCleanup
  | capture | resume | discard | readCell | writeCell => cases closed.1
  | plug plain value valueClosed scope tail => cases stack with
      | push frame rest => cases effectStack with
          | push effectFrame effectRest bound => cases effectFrame with
              | plain scopeTyped context =>
                  have operand := effect_value_closed_type expression valueClosed.1
                  exact ⟨_, _, .checked scopeTyped (context_plug_typed context
                    (typed_value_transport operand valueClosed.1 _ _)), rest, effectRest⟩
  | leaveHandler handler value valueClosed scope tail => cases stack with
      | push frame rest => cases effectStack with
          | push effectFrame effectRest bound => cases effectFrame with
              | handler caller clauses coverage unique =>
                  exact ⟨_, _, effect_value_transport expression valueClosed.1 caller _, rest, effectRest⟩
  | leaveCell identity payload answer savedScope scope value valueClosed tail => cases stack with
      | push frame rest => cases effectStack with
          | push effectFrame effectRest bound => cases effectFrame with
              | cell caller noEscape =>
                  exact ⟨_, _, effect_value_transport expression valueClosed.1 caller _, rest, effectRest⟩
  | startCleanup action saved savedClosed scope tail => cases stack with
      | push frame rest => cases effectStack with
          | push effectFrame effectRest bound => cases effectFrame with
              | armed caller callable requests =>
                  have savedTyped := effect_value_closed_type expression savedClosed.1
                  exact ⟨.unit, _, .checked .none (.app
                    (typed_value_transport callable action.closed.1 .none _) .unit requests),
                    .push (.running (effect_scope_known_has_types caller) callable savedTyped) rest,
                    .push (.running caller callable savedTyped requests) effectRest (fun _ used => used)⟩
  | finishCleanup action saved savedClosed scope tail => cases stack with
      | push frame rest => cases effectStack with
          | push effectFrame effectRest bound => cases effectFrame with
              | running caller callable savedTyped requests =>
                  obtain ⟨ticket, caller⟩ := caller
                  exact ⟨_, _, .checked caller (typed_value_transport savedTyped savedClosed.1 ticket _), rest, effectRest⟩
  | leaveClause owner answer value valueClosed scope callerScope tail => cases stack with
      | spent known caller rest => cases effectStack with
          | spent actual effectCaller effectRest bound =>
              exact ⟨_, _, effect_value_transport expression valueClosed.1 effectCaller _, rest, effectRest⟩
  | finishClose identity scope callerScope tail => cases stack with
      | push frame rest => cases effectStack with
          | push effectFrame effectRest bound => cases effectFrame with
              | closing caller =>
                  exact ⟨_, _, effect_value_transport expression closed.1 caller _, rest, effectRest⟩
  | retire owner scope tail => cases stack with
      | push frame rest => cases effectStack with
          | push effectFrame effectRest bound => cases effectFrame with
              | retiring known => cases expression with
                  | checked scopeTyped typed =>
                      exact ⟨.unit, _, .checked scopeTyped (typed_value_transport typed closed.1 _ _), rest, effectRest⟩

/-- Both registries describe the same issued owner identities. Their stored
capabilities remain independent. -/
theorem registered_actions {registry : CoherentSourceTypes.Owners.Registry}
    (runtime : ScopedPortJoint.RegistryHistory registry.runtime.joint issued)
    (history : UsageRegistryHistory actions issued) :
    ∀ owner contract, registry.contracts.ports owner = some contract → ∃ rights, actions owner = some rights := by
  intro owner contract known
  rw [CoherentSourceTypes.Owners.registry_ports] at known
  cases actual : registry.runtime.joint owner with
  | none => simp [ScopedPortJoint.Registry.effects, actual] at known
  | some record => exact (history owner).mpr ((runtime owner).mp ⟨record, actual⟩)

theorem resume_requires_action
    (checked : CodeDemand policy actions scope (.resume binder value) demand)
    (resolved : scope.resolve binder = some owner) :
    ∃ rights, actions owner = some rights ∧ rights.resume = true := by
  cases checked with
  | idle scope checked => cases checked
  | consume known checked => cases checked with
      | resume permitted operand =>
          simp [Execution.Scope.resolve] at resolved
          subst owner
          exact ⟨_, known, permitted⟩

namespace Examples
open CoherentSourceTypes

def unused : Instance := .user 193 []
def contract : Owners.Contract := ⟨.unit, .unit, false, [], [], [], none, [], [unused]⟩
def records : Owners.Contracts := fun owner => if owner = 0 then some contract else none
def actions : Syntax.UsageTickets := fun owner => if owner = 0 then some ActionRequirements.resumeOnly else none

theorem resume_source : DeclaredSources.Expression SourceCallableExamples.operations
    SourceCallableExamples.policy records [] [] (.ticket 9 0) Environment.empty (.resume 9 .unit)
    .unit [0] (.sequence (.request [] []) (.invoke ⟨0, .resume⟩ [] [])) := by
  exact .resume (contract := contract) (by rfl) (by rfl) (by rfl) (.stable .unit)
    (List.nil_subset _) (by simp [contract, ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources])

theorem independent_offer (base : Owners.Contracts) (environment : Environment) (held : Bool) :
    DeclaredSources.Offer SourceCallableExamples.operations SourceCallableExamples.policy base [] environment []
      1 9 .unit .unit .unit [] [unused] (.resume 9 .unit) held false (some []) := by
  apply DeclaredSources.Offer.available (fun _ => rfl) (by intro impossible; cases impossible)
  intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
  have known : (base.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
  have operand : DeclaredSources.Expression SourceCallableExamples.operations SourceCallableExamples.policy
      (base.insert owner contract) [] [] (.ticket 9 owner) (environment.extend 1 .unit)
      .unit contract.input [] (.request [] []) := inputSame.symm ▸ .stable .unit
  have resumed := DeclaredSources.Expression.resume (binder := 9) known
    (by simp [Execution.Scope.resolve]) (by rfl) operand (resumeSame.symm ▸ List.Subset.refl [])
    (answerSame.symm ▸ (by simp [ScopedPorts.InWorld, Value.port, ScopedPorts.Port.resources]))
  exact .typed (answerSame ▸ resumed) ClauseRowAdmission.resume_rows

/-- The revised declaration rule also leaves an unused resume interface free
when the clause only disposes. -/
theorem independent_dispose_offer (base : Owners.Contracts) (environment : Environment) :
    DeclaredSources.Offer SourceCallableExamples.operations (fun _ => ⟨false, true⟩) base [] environment []
      1 9 .unit .unit .unit [unused] [] (.discard 9) false true (some []) := by
  apply DeclaredSources.Offer.available (by intro impossible; cases impossible) (fun _ => rfl)
  intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
  have known : (base.insert owner contract) owner = some contract := by simp [Owners.Contracts.insert]
  exact .typed (.discard known (by rfl) (by rfl) heldSame (closeSame.symm ▸ List.Subset.refl []))
    ClauseRowAdmission.discard_rows

theorem unused_closing_interface_connected :
    Connected signature records.ports actions [] (.live 0 .unit .unit .nil .none .nil) [] [] := by
  exact .live (by rfl) (by rfl) ⟨.none, .none⟩ (fun _ => .nil (List.nil_subset _))
    (.nil (List.Subset.refl [])) (fun _ => List.nil_subset _) (by intro impossible; cases impossible)
    (List.Subset.refl [])

theorem old_interface_rejects (incoming : List Instance) :
    ¬ EffectStack signature records.ports [] (.live 0 .unit .unit .nil .none .nil) incoming [] := by
  intro typed
  cases typed with
  | live known scope saved rest resume close bound =>
      have same : contract.ports = _ := Option.some.inj known
      cases same
      cases rest with
      | nil outside => exact List.not_mem_nil (outside (close (show unused ∈ contract.ports.closeEffects from List.mem_cons_self)))

theorem unused_interface_resumes :
    Connected signature records.ports actions [] (.spent 0 .unit .none .nil) [] [] := by
  exact resume_recomposition (front := .nil) (contract := contract.ports)
    (by rfl) (by rfl) (by rfl) unused_closing_interface_connected (List.nil_subset _)

/-- The regression checks current code and actual ports as well as its stack.
This is a local machine configuration, not a claimed initial-source trace. -/
theorem resume_configuration :
    ConfigurationConnected signature records.ports actions []
      ⟨.resume 9 .unit, .ticket 9 0, .live 0 .unit .unit .nil .none .nil⟩ .unit [] := by
  refine ⟨.unit, [], .checked (.bound (by rfl)) ?_, ?_, unused_closing_interface_connected⟩
  · exact .resume .unit (List.nil_subset _) (by simp [contract, Owners.Contract.ports, ScopedPorts.InWorld,
      CoherentSourceTypes.Value.port, ScopedPorts.Port.resources])
  · exact .live (by rfl) ⟨.none, .none⟩ .nil .nil

theorem configuration_usage :
    ConfigurationUsage SourceCallableExamples.policy actions
      ⟨.resume 9 .unit, .ticket 9 0, .live 0 .unit .unit .nil .none .nil⟩ := by
  exact ⟨[0], [], .consume (by rfl) (.resume rfl .unit),
    .live (by rfl) ⟨.none, .none⟩ .nil .nil, by decide, .refl _, by decide⟩

theorem resume_configuration_preserved :
    RawStep ⟨.resume 9 .unit, .ticket 9 0, .live 0 .unit .unit .nil .none .nil⟩
      ⟨.unit, .ticket 9 0, .spent 0 .unit .none .nil⟩ [] [.ticket 0] ∧
    ConfigurationConnected signature records.ports actions []
      ⟨.unit, .ticket 9 0, .spent 0 .unit .none .nil⟩ .unit [] := by
  refine ⟨.resume 9 0 (.ticket 9 0) .none .unit .unit .nil .nil .nil .unit
    ScopedExecution.Examples.unit_closed (by rfl), ?_⟩
  exact resume_preserves_configuration (front := .nil) (by rfl) (by rfl) (by rfl)
    resume_configuration trivial

end Examples
end Ash.OneShot.ScopedActionInterfaces

#print axioms Ash.OneShot.ScopedActionInterfaces.input_weaken
#print axioms Ash.OneShot.ScopedActionInterfaces.output_weaken
#print axioms Ash.OneShot.ScopedActionInterfaces.append
#print axioms Ash.OneShot.ScopedActionInterfaces.decompose
#print axioms Ash.OneShot.ScopedActionInterfaces.from_scoped
#print axioms Ash.OneShot.ScopedActionInterfaces.provides_or_exports
#print axioms Ash.OneShot.ScopedActionInterfaces.resume_recomposition
#print axioms Ash.OneShot.ScopedActionInterfaces.closing_requests
#print axioms Ash.OneShot.ScopedActionInterfaces.configuration_has_types
#print axioms Ash.OneShot.ScopedActionInterfaces.configuration_from_scoped
#print axioms Ash.OneShot.ScopedActionInterfaces.current_request_has_interpretation
#print axioms Ash.OneShot.ScopedActionInterfaces.resume_preserves_configuration
#print axioms Ash.OneShot.ScopedActionInterfaces.live_to_spent
#print axioms Ash.OneShot.ScopedActionInterfaces.discard_preserves_configuration
#print axioms Ash.OneShot.ScopedActionInterfaces.world_weaken
#print axioms Ash.OneShot.ScopedActionInterfaces.action_extension
#print axioms Ash.OneShot.ScopedActionInterfaces.configuration_world_weaken
#print axioms Ash.OneShot.ScopedActionInterfaces.configuration_action_extension
#print axioms Ash.OneShot.ScopedActionInterfaces.raw_value_preserves_configuration
#print axioms Ash.OneShot.ScopedActionInterfaces.registered_actions
#print axioms Ash.OneShot.ScopedActionInterfaces.resume_requires_action
#print axioms Ash.OneShot.ScopedActionInterfaces.Examples.resume_source
#print axioms Ash.OneShot.ScopedActionInterfaces.Examples.independent_offer
#print axioms Ash.OneShot.ScopedActionInterfaces.Examples.independent_dispose_offer
#print axioms Ash.OneShot.ScopedActionInterfaces.Examples.unused_closing_interface_connected
#print axioms Ash.OneShot.ScopedActionInterfaces.Examples.old_interface_rejects
#print axioms Ash.OneShot.ScopedActionInterfaces.Examples.unused_interface_resumes

#print axioms Ash.OneShot.ScopedActionInterfaces.Examples.resume_configuration
#print axioms Ash.OneShot.ScopedActionInterfaces.Examples.configuration_usage
#print axioms Ash.OneShot.ScopedActionInterfaces.Examples.resume_configuration_preserved
