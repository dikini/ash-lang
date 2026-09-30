import ClauseJoint

/-!
Declared argument resources follow the exact effect instance. Finite argument
support and the selected handler's retained access derive the actual capture
payload check. Callable payload contracts remain outside this finite fragment.
-/

namespace Ash.OneShot.PayloadBoundary
open Syntax Instantiation ScopedExpressions ScopedExecution ScopedPorts
open DeclarationResults (signature)

theorem parameter_environment_range
    (built : parameterEnvironment parameters arguments = some environment)
    (known : environment name = some identity) :
    identity ∈ arguments.flatMap TypeArgument.resources := by
  induction parameters generalizing arguments environment with
  | nil =>
      cases arguments with
      | nil => cases built; cases known
      | cons => cases built
  | cons parameter rest ih =>
      cases arguments with
      | nil => cases built
      | cons argument arguments => cases argument with
          | nominal | apply => cases built
          | resource key =>
              cases tail : parameterEnvironment rest arguments with
              | none => simp [parameterEnvironment, tail] at built
              | some preceding =>
                  simp only [parameterEnvironment, tail, Option.map_some, Option.some.injEq] at built
                  subst environment
                  by_cases same : name = parameter
                  · simp only [Environment.bind, same, ↓reduceIte, Option.some.injEq] at known
                    subst identity
                    simp [TypeArgument.resources]
                  · have old : preceding name = some identity := by simpa [Environment.bind, same] using known
                    exact List.mem_append_right _ (ih tail old)

theorem realized_declared_support
    (realized : TypeRealizes environment source target)
    (declared : ∀ name ∈ source.resources, DeclaredName parameters name)
    (built : parameterEnvironment parameters arguments = some environment) :
    target.resources ⊆ arguments.flatMap TypeArgument.resources := by
  apply realized_type_support realized
  intro name member identity known
  have inScope := declared name member
  cases name with
  | activation => cases inScope
  | bound parameter => cases known with
      | bound known => exact parameter_environment_range built known

theorem declared_operation_resources (declared : DeclaredOperation declarations entry) :
    (eraseType entry.input).resources ⊆ entry.effect.resources ∧
    (eraseType entry.output).resources ⊆ entry.effect.resources := by
  cases declared with
  | declared family valid operation arguments input output =>
      have inScope := valid.2.2 _ (List.mem_of_getElem? operation)
      exact ⟨(erasure_preserves_declared_resources _).trans (realized_declared_support input
          (fun name member => inScope name (List.mem_append_left _ member)) arguments),
        (erasure_preserves_declared_resources _).trans (realized_declared_support output
          (fun name member => inScope name (List.mem_append_right _ member)) arguments)⟩

/-- Port metadata follows the requested resource arguments. This does not
    bound a callable value's actual captures from its port alone. -/
theorem signature_resources
    (known : signature declarations requested operation = some (input, output)) :
    input.resources ⊆ requested.resources ∧ output.resources ⊆ requested.resources := by
  cases requested with
  | cell identity =>
      cases operation with
      | zero =>
          simp only [signature, withCellSignatures, Option.some.injEq, Prod.mk.injEq] at known
          obtain ⟨rfl, rfl⟩ := known
          exact ⟨List.Subset.refl _, List.nil_subset _⟩
      | succ operation => cases operation with
          | zero =>
              simp only [signature, withCellSignatures, Option.some.injEq, Prod.mk.injEq] at known
              obtain ⟨rfl, rfl⟩ := known
              exact ⟨by simp [Port.resources, Instance.resources], List.nil_subset _⟩
          | succ operation => cases known
  | user family arguments =>
      cases familyKnown : declarations family with
      | none => simp [signature, withCellSignatures, DeclarationResults.userSignature, familyKnown] at known
      | some declaration =>
          cases valid : checkFamily declaration with
          | false => simp [signature, withCellSignatures, DeclarationResults.userSignature, familyKnown, valid] at known
          | true =>
              cases operationKnown : declaration.operations[operation]? with
              | none => simp [signature, withCellSignatures, DeclarationResults.userSignature, familyKnown, valid, operationKnown] at known
              | some template =>
                  cases argumentsBound : parameterEnvironment declaration.parameters arguments with
                  | none => simp [signature, withCellSignatures, DeclarationResults.userSignature, familyKnown, valid, operationKnown, argumentsBound] at known
                  | some environment =>
                      obtain ⟨inputType, outputType, declared⟩ := declared_operation_exists familyKnown
                        ((check_family_iff _).mp valid) operationKnown argumentsBound
                      have actual := DeclarationResults.declared_signature_known declared
                      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (known.symm.trans actual))
                      exact declared_operation_resources declared

theorem typed_payload_bound
    (typed : Typed (signature declarations) world TypeEnv.empty ticket allowed operand input)
    (isValue : operand.IsValue) (finite : ClauseResults.PortBound input resources) :
    resourceDependencies operand.dependencies ⊆ input.resources := by
  obtain ⟨shape, same⟩ := ContinuationBounds.port_bound_finite input finite
  rw [typed_first_order_value_support typed isValue shape]
  exact List.Subset.refl _

theorem payload_crosses_selected_handler
    (cut : HandlerCut requested whole capture tail handler)
    (support : Supported whole.erase ambient)
    (known : signature declarations requested operation = some (input, output))
    (typed : Typed (signature declarations) world TypeEnv.empty ticket allowed operand input)
    (isValue : operand.IsValue) (finite : ClauseResults.PortBound input resources) :
    resourceDependencies operand.dependencies ⊆ tail.erase.visible ++ ambient := by
  have inside := (typed_payload_bound typed isValue finite).trans (signature_resources known).1
  have handlerAccess := selected_handler_access cut support
  rw [← ScopedTyping.handler_cut_instance cut] at inside
  exact inside.trans ((List.subset_append_left _ _).trans handlerAccess)

variable {capture tail : Stack} {issued completed : List Owner}

theorem current_payload_access
    (valid : ClauseJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩, activations⟩
      result outgoing bound)
    (cut : HandlerCut requested whole capture tail handler) (isValue : operand.IsValue) :
    resourceDependencies operand.dependencies ⊆ tail.erase.visible ++ ambient := by
  obtain ⟨inputPort, current, stackTyped⟩ := effect_configuration_has_types valid.joint.effects
  obtain ⟨environment, ticket, inputBound, scopeChecked, code, stack⟩ := valid.results
  obtain ⟨savedEnvironment, savedTicket, answer, handlerScope, clauses, saved, outside⟩ :=
    ClauseFrames.handler_cut_certificate cut stack
  cases current with
  | checked scopeTyped current =>
      obtain ⟨argumentPort, declared, available, operandTyped⟩ := typed_perform_inversion current
      obtain ⟨savedTyped, outsideTyped, handlerTyped⟩ := handler_cut_retains_typing cut stackTyped
      cases handlerTyped with
      | handler caller clausesTyped coverage unique =>
          have atHandler := declared
          rw [← ScopedTyping.handler_cut_instance cut] at atHandler
          obtain ⟨parameter, binder, body, selected⟩ := ScopedTyping.clause_at_of_key (coverage _ _ _ atHandler)
          obtain ⟨actualInput, actualOutput, argumentBound, resumeBound, known, inputFinite, outputFinite, bodyChecked⟩ :=
            ClauseResults.selected_clause selected clauses
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (known.symm.trans atHandler))
          exact payload_crosses_selected_handler cut valid.joint.support.control declared operandTyped isValue inputFinite

/-- Every actual source-handler cut receives the check derived from its own
    retained clauses and outside support. Non-value operands impose no current
    capture event; their evaluation remains governed by the ordinary machine. -/
theorem request_access_checks
    (valid : ClauseJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩, activations⟩
      result outgoing bound) :
    AccessChecks ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ ambient := by
  constructor
  · intro identity payload answer savedScope scope value tail same closed
    have impossible := congrArg Configuration.expression same
    dsimp only at impossible
    rw [← impossible] at closed
    cases closed.1
  · intro requested' operation' operand' scope' whole' cap tail handler same cut closed
    rw [same] at valid
    exact current_payload_access valid cut closed.1
  · intro binder ticket scope caller input answer front cap tail plan same resolved built
    cases congrArg Configuration.expression same

theorem capture_without_payload_premise
    (cut : HandlerCut requested whole capture tail handler)
    (valid : ClauseJoint.Valid declarations policy registry ambient
      ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩, issued, completed⟩, activations⟩
      result outgoing bound)
    (isValue : operand.IsValue)
    (fresh : (issued ++ [Owner.ticket owner]).Nodup) :
    ∃ (parameter binder : Nat) (body : Code) (output : Port) (residual : List Instance)
      (record : ClauseJoint.TicketRecord),
      record.joint = ⟨⟨output, eraseType handler.answer, residual, residual⟩, policy binder⟩ ∧
      ClauseAt operation handler.clauses parameter binder body ∧
      (∃ input, signature declarations requested operation = some (input, output)) ∧
      ClauseJoint.RegistryExtends registry (registry.insert owner record) ∧
      let before : NamedState := ⟨⟨⟨.perform (freezeEffect requested) operation operand, scope, whole⟩,
        issued, completed⟩, activations⟩
      let after : Configuration := ⟨body.subst parameter operand, .ticket binder owner,
        .live owner (embedPort output) handler.answer capture handler.scope tail⟩
      NamedAccessStep ambient before (ScopedPortJoint.advanceState before after [.ticket owner] []) ∧
      ClauseJoint.Valid declarations policy (registry.insert owner record) ambient
        (ScopedPortJoint.advanceState before after [.ticket owner] []) result outgoing bound :=
  ClauseJoint.capture_preserves cut valid isValue fresh (request_access_checks valid)

namespace Examples

def declarations : DeclarationRegistry := fun family =>
  if family = 84 then some ⟨[0], [⟨.reference (.bound 0), .integer⟩]⟩ else none

def family : Instance := .user 84 [.resource 7]
def clauses : ScopedExpressions.Clauses := .cons 0 5 9 (.resume 9 (.integer 17)) .nil
def handler : HandlerData := ⟨12, family, clauses, .none, .integer, rfl⟩
def outside : Stack := .push (.cell 7 10 .none .integer) .nil
def saved : Stack := .push (.cell 9 20 .none .integer) (.push (.handler handler) .nil)
def whole : Stack := saved.append outside
def request : Configuration := ⟨.perform (freezeEffect family) 0 (.resourceRef (.activation 7)), .none, whole⟩
def initial : NamedState := ⟨⟨request, [.resource 7, .resource 9], []⟩, [12]⟩
def final : NamedState := ⟨⟨⟨.integer 17, .none, .nil⟩, [.resource 7, .resource 9, .ticket 5],
  [.resource 7, .resource 9, .ticket 5]⟩, [12]⟩
def policy : TicketPolicy := fun _ => ActionRequirements.resumeOnly
def emptyRegistry : ClauseJoint.Registry := fun _ => none
def environment : ResultSummaries.Environment := fun _ => .unknown

theorem operation_known : signature declarations family 0 = some (.reference 7, .integer) := by decide

theorem selected_cut : HandlerCut family whole saved outside handler :=
  .push _ _ _ _ _ (by decide) (.hit handler outside rfl)

theorem clause_types : ClausesTyped (signature declarations) [7, 9] TypeEnv.empty family .integer [] clauses :=
  .cons operation_known (.resume .integer (List.nil_subset _) (List.nil_subset _)) .nil

theorem coverage : Covers (signature declarations) family clauses := by
  intro operation input output known
  cases operation with
  | zero => exact List.mem_cons_self
  | succ operation =>
      simp [signature, DeclarationResults.userSignature, withCellSignatures, declarations, family] at known

theorem control_effects : EffectStack (signature declarations) emptyRegistry.joint.effects [7, 9] whole [family] [] :=
  .push (.cell ⟨_, .none⟩ (by simp [eraseType, Port.resources]))
    (.push (.handler ⟨_, .none⟩ clause_types coverage (by decide))
      (.push (.cell ⟨_, .none⟩ (by simp [eraseType, Port.resources])) (.nil (List.Subset.refl _)) (List.nil_subset _))
      (List.Subset.refl _))
    (by simp [handler])

theorem control_types : StackTyped (signature declarations) emptyRegistry.joint.effects.types [7, 9] whole .integer .integer :=
  .push (.cell ⟨_, .none⟩ (by simp [eraseType, Port.resources]))
    (.push (.handler ⟨_, .none⟩ clause_types coverage (by decide))
      (.push (.cell ⟨_, .none⟩ (by simp [eraseType, Port.resources])) .nil))

theorem request_results : ClauseFrames.ConfigurationReturns declarations emptyRegistry.results [7, 9] request [] := by
  refine ⟨environment, .none, [], .none, .existing
    (.perform (operandBound := [7]) (.leaf (Or.inl trivial) rfl (by decide)) rfl (by decide)), ?_⟩
  exact .cell .none (by simp)
    (.handler (environment := environment) .none
      (.cons operation_known rfl rfl (.resume (.existing (.leaf (Or.inl trivial) rfl rfl))) .nil)
      (List.Subset.refl _) (.cell .none (by simp) (.nil (List.Subset.refl _))))

/-- The starting configuration already owns both cells. Acquisition from an
    initial source term is a separate construction from this boundary example. -/
theorem initial_valid : ClauseJoint.Valid declarations policy emptyRegistry [] initial .integer [] [] := by
  constructor
  · constructor
    · exact ⟨List.Perm.swap _ _ [], by decide⟩
    · constructor
      · intro owner; simp [initial, request, whole, saved, outside, Stack.append, Stack.erase, Control.ticketNames, ExecFrame.erase, HandlerData.erase]
      · intro activation; exact Nat.le_refl _
      · decide
    · constructor
      · exact .push _ _ _ (.push _ _ _ (.push _ _ _ (.nil _) (List.nil_subset _)) (by decide)) (List.nil_subset _)
      · decide
    · exact ⟨.integer, [family], .checked .none
        (.perform operation_known List.mem_cons_self (.reference (by decide)) (List.nil_subset _)), control_types, control_effects⟩
    · refine ⟨[], [], .idle .none (.perform .resourceRef), ?_, List.nil_subset _, .refl _, by decide⟩
      exact .push (.cell ⟨_, .none⟩) (List.nil_subset _)
        (.push (.handler ⟨_, .none⟩ (.cons (.resume rfl .integer) .nil)) (List.nil_subset _)
          (.push (.cell ⟨_, .none⟩) (List.nil_subset _) .nil))
    · intro owner; simp [initial, emptyRegistry, ClauseJoint.Registry.joint]
    · exact ⟨rfl, by trivial⟩
  · exact request_results

theorem nonempty_payload_crosses :
    resourceDependencies request.expression.dependencies ≠ [] ∧
    resourceDependencies (Code.resourceRef (.activation 7)).dependencies ⊆ outside.erase.visible := by
  constructor
  · decide
  · exact current_payload_access initial_valid selected_cut trivial

theorem capture_checks_are_derived : AccessChecks request [] := request_access_checks initial_valid

/-- A handle to outer cell 7 crosses a continuation owning inner cell 9.
    Capture, resume and both releases preserve the complete combined invariant. -/
theorem resource_capture_release_execution : ∃ record,
    ClauseJoint.CertifiedSteps declarations policy [] .integer [] [] emptyRegistry initial
      (emptyRegistry.insert 5 record) final := by
  have v0 := initial_valid
  obtain ⟨parameter, binder, body, output, residual, record, recordEq, selected, ⟨input, known⟩,
    extension, e0, v1⟩ := capture_without_payload_premise selected_cut v0 trivial (owner := 5) (by decide)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (known.symm.trans operation_known))
  change ClauseAt 0 clauses parameter binder body at selected
  cases selected with
  | pass different selected => exact False.elim (different rfl)
  | hit =>
      let state1 : NamedState := ⟨⟨⟨.resume 9 (.integer 17), .ticket 9 5,
        .live 5 .integer handler.answer saved handler.scope outside⟩,
        [.resource 7, .resource 9, .ticket 5], []⟩, [12]⟩
      have v1 : ClauseJoint.Valid declarations policy (emptyRegistry.insert 5 record) [] state1 .integer [] [] := by
        simpa [initial, request, state1, ScopedPortJoint.advanceState, enteredActivations, Code.subst, embedPort] using v1
      have e0 : NamedAccessStep [] initial state1 := by
        simpa [initial, request, state1, ScopedPortJoint.advanceState, enteredActivations, Code.subst, embedPort] using e0
      obtain ⟨e1, v2⟩ := ClauseJoint.resume_preserves (front := .nil) v1 rfl trivial
      obtain ⟨e2, v3⟩ := ClauseJoint.cell_return_preserves v2 trivial
      obtain ⟨e3, v4⟩ := ClauseJoint.handler_return_preserves v3 trivial
      obtain ⟨e4, v5⟩ := ClauseJoint.clause_return_preserves v4 trivial
      obtain ⟨e5, v6⟩ := ClauseJoint.cell_return_preserves v5 trivial
      have last : ClauseJoint.Valid declarations policy (emptyRegistry.insert 5 record) [] final .integer [] [] := by
        simpa [state1, final, saved, outside, handler, ScopedPortJoint.advanceState, enteredActivations, Stack.append] using v6
      let state5 : NamedState := ⟨⟨⟨.integer 17, .none, outside⟩, [.resource 7, .resource 9, .ticket 5],
        [.resource 9, .ticket 5]⟩, [12]⟩
      have e5 : NamedAccessStep [] state5 final := by
        simpa [state1, state5, final, saved, outside, handler, ScopedPortJoint.advanceState, enteredActivations, Stack.append] using e5
      exact ⟨record, .next v0 e0 extension (.next v1 e1 (ClauseJoint.registry_extends_refl _)
        (.next v2 e2 (ClauseJoint.registry_extends_refl _) (.next v3 e3 (ClauseJoint.registry_extends_refl _)
          (.next v4 e4 (ClauseJoint.registry_extends_refl _) (.next v5 e5 (ClauseJoint.registry_extends_refl _) (.refl last))))))⟩

theorem resource_capture_final_ledger : Ledger final.execution.erase := by
  obtain ⟨record, checked⟩ := resource_capture_release_execution
  exact (ClauseJoint.certified_final checked).joint.ledger

theorem captured_inner_handle_rejected :
    ¬ ClauseJoint.Valid declarations policy emptyRegistry []
      ⟨⟨⟨.perform (freezeEffect family) 0 (.resourceRef (.activation 9)), .none, whole⟩,
        [.resource 7, .resource 9], []⟩, [12]⟩ .integer [] [] := by
  intro valid
  have outsideOnly := current_payload_access valid selected_cut trivial
  have impossible := outsideOnly (List.mem_cons_self)
  have absent : 9 ∉ outside.erase.visible ++ [] := by decide
  exact absent impossible

theorem parameter_aliases_preserved : ∃ environment,
    parameterEnvironment [0, 1] [.resource 7, .resource 7] = some environment ∧
    environment 0 = some 7 ∧ environment 1 = some 7 :=
  ⟨_, rfl, rfl, rfl⟩

def hiddenAtom : DeclarationRegistry := fun family =>
  if family = 84 then some ⟨[], [⟨.reference (.activation 7), .integer⟩]⟩ else none

theorem hidden_declaration_atom_rejected : signature hiddenAtom (.user 84 []) 0 = none := by decide

end Examples

end Ash.OneShot.PayloadBoundary

#print axioms Ash.OneShot.PayloadBoundary.parameter_environment_range
#print axioms Ash.OneShot.PayloadBoundary.realized_declared_support
#print axioms Ash.OneShot.PayloadBoundary.declared_operation_resources
#print axioms Ash.OneShot.PayloadBoundary.signature_resources
#print axioms Ash.OneShot.PayloadBoundary.typed_payload_bound
#print axioms Ash.OneShot.PayloadBoundary.payload_crosses_selected_handler
#print axioms Ash.OneShot.PayloadBoundary.current_payload_access
#print axioms Ash.OneShot.PayloadBoundary.request_access_checks
#print axioms Ash.OneShot.PayloadBoundary.capture_without_payload_premise
#print axioms Ash.OneShot.PayloadBoundary.Examples.operation_known
#print axioms Ash.OneShot.PayloadBoundary.Examples.selected_cut
#print axioms Ash.OneShot.PayloadBoundary.Examples.clause_types
#print axioms Ash.OneShot.PayloadBoundary.Examples.coverage
#print axioms Ash.OneShot.PayloadBoundary.Examples.control_effects
#print axioms Ash.OneShot.PayloadBoundary.Examples.control_types
#print axioms Ash.OneShot.PayloadBoundary.Examples.request_results
#print axioms Ash.OneShot.PayloadBoundary.Examples.initial_valid
#print axioms Ash.OneShot.PayloadBoundary.Examples.nonempty_payload_crosses
#print axioms Ash.OneShot.PayloadBoundary.Examples.capture_checks_are_derived
#print axioms Ash.OneShot.PayloadBoundary.Examples.resource_capture_release_execution
#print axioms Ash.OneShot.PayloadBoundary.Examples.resource_capture_final_ledger
#print axioms Ash.OneShot.PayloadBoundary.Examples.captured_inner_handle_rejected
#print axioms Ash.OneShot.PayloadBoundary.Examples.parameter_aliases_preserved
#print axioms Ash.OneShot.PayloadBoundary.Examples.hidden_declaration_atom_rejected
