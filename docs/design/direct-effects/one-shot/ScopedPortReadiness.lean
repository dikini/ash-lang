import ScopedPortSubstitution

/-!
Lexical readiness and strict evaluation frames for declared port typing.
Actual machine metadata remains Ty; a canonical embedding supplies annotations
whose declared ports are proved equal to the inferred Port. No support claim is
inferred from the embedding's empty callable-retention fields.
-/

namespace Ash.OneShot.ScopedPorts
open Syntax (Dependency without mem_without)
open Instantiation ScopedExpressions ScopedExecution
open ScopedTyping (World fresh_world_name frozen_effect_no_free_names append_empty)

def embedPort : Port → Ty
  | .unit => .unit
  | .boolean => .boolean
  | .integer => .integer
  | .reference identity => .reference identity
  | .product left right => .product (embedPort left) (embedPort right)
  | .function input output requests => .function (embedPort input) (embedPort output) requests []

@[simp] theorem erase_embed_port (type : Port) : eraseType (embedPort type) = type := by
  induction type <;> simp_all [embedPort, eraseType]

theorem embedded_declared_resources (type : Port) : (embedPort type).resources = type.resources := by
  induction type <;> simp_all [embedPort, Ty.resources, Port.resources]

theorem typed_resource_closed (typed : Typed signature world environment ticket allowed code type) : code.ResourceClosed := by
  induction typed using Typed.rec (motive_2 := fun _ _ _ _ _ clauses _ => clauses.freeNames = []) with
  | unit | boolean | integer | «variable» | reference | discard => rfl
  | pair _ _ left right | app _ _ _ left right | bind _ _ left right | cleanup _ _ _ left right =>
      exact append_empty left right
  | lambda _ _ body | resume _ _ _ body => exact body
  | branch _ _ _ condition yes no => exact append_empty (append_empty condition yes) no
  | perform _ _ _ _ operand => exact append_empty (frozen_effect_no_free_names _) operand
  | handle _ _ _ _ _ body clauses =>
      exact append_empty (append_empty (frozen_effect_no_free_names _) body) clauses
  | @resource currentWorld currentEnvironment currentTicket currentAllowed init residual answer binder source
      initTyped bodyTyped resultBound effectsBound effects initializer body =>
      obtain ⟨identity, fresh⟩ := fresh_world_name currentWorld
      have closed := body identity fresh
      have covered := (source.instantiation_closes_iff (Environment.empty.bind binder identity)).mp closed
      apply append_empty initializer
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro name member
      obtain ⟨present, different⟩ := List.mem_filter.mp member
      obtain ⟨key, known⟩ := covered name present
      have unequal : name ≠ binder := by simpa using different
      simp [Environment.bind, Environment.empty, unequal] at known
  | nil => rfl
  | cons _ _ _ body rest => exact append_empty body rest

/-- A context derives input/output ports from its retained syntax. -/
inductive ContextTyped (signature : Signature) : World → TypeEnv → Ticket → List Instance → ScopedExecution.Context → Port → Port → Prop where
  | pairLeft : Typed signature world environment ticket allowed right rightType →
      ContextTyped signature world environment ticket allowed (.pairLeft right) leftType (.product leftType rightType)
  | pairRight : Typed signature world environment ticket allowed left leftType →
      ContextTyped signature world environment ticket allowed (.pairRight left) rightType (.product leftType rightType)
  | appFunction : Typed signature world environment ticket allowed argument input → latent ⊆ allowed →
      ContextTyped signature world environment ticket allowed (.appFunction argument) (.function input output latent) output
  | appArgument : Typed signature world environment ticket allowed function (.function input output latent) → latent ⊆ allowed →
      ContextTyped signature world environment ticket allowed (.appArgument function) input output
  | bind : Typed signature world (environment.extend parameter input) ticket allowed suffix output →
      ContextTyped signature world environment ticket allowed (.bind parameter suffix) input output
  | branch : Typed signature world environment ticket allowed yes type → Typed signature world environment ticket allowed no type →
      ContextTyped signature world environment ticket allowed (.branch yes no) .boolean type
  | perform : signature effectInst operation = some (input, output) → effectInst ∈ allowed → InWorld world output →
      ContextTyped signature world environment ticket allowed (.perform (freezeEffect effectInst) operation) input output
  | resume : residual ⊆ allowed → InWorld world answer →
      ContextTyped signature world environment (.bound binder input answer residual closing) allowed (.resume binder) input answer
  | resource : (∀ identity, identity ∉ world →
        Typed signature (world ++ [identity]) environment ticket (.cell identity :: residual)
          (body.instantiate (Environment.empty.bind binder identity)) answer) →
      InWorld world answer → residual.flatMap Instance.resources ⊆ world → residual ⊆ allowed →
      ContextTyped signature world environment ticket allowed (.resource binder body) .integer answer
  | cleanup : Typed signature world environment ticket allowed body answer → latent ⊆ allowed →
      ContextTyped signature world environment ticket allowed (.cleanup body) (.function .unit .unit latent) answer

theorem context_plug_typed (context : ContextTyped signature world environment ticket allowed frame input output)
    (child : Typed signature world environment ticket allowed expression input) :
    Typed signature world environment ticket allowed (frame.plug expression) output := by
  cases context with
  | pairLeft right => exact .pair child right
  | pairRight left => exact .pair left child
  | appFunction argument effects => exact .app child argument effects
  | appArgument function effects => exact .app function child effects
  | bind suffix => exact .bind child suffix
  | branch yes no => exact .branch child yes no
  | perform operation available formed => exact .perform operation available child formed
  | resume effects formed => exact .resume child effects formed
  | resource body noEscape noEffectEscape effects => exact .resource child body noEscape noEffectEscape effects
  | cleanup body effects => exact .cleanup child body effects

theorem typed_focus_decomposition (focus : ScopedExecution.Focus whole child context)
    (typed : Typed signature world environment ticket allowed whole output) :
    ∃ input, Typed signature world environment ticket allowed child input ∧
      ContextTyped signature world environment ticket allowed context input output := by
  cases focus with
  | pairLeft notValue => cases typed with
      | pair left right => exact ⟨_, left, .pairLeft right⟩
  | pairRight isValue notValue => cases typed with
      | pair left right => exact ⟨_, right, .pairRight left⟩
  | appFunction notValue => cases typed with
      | app function argument effects => exact ⟨_, function, .appFunction argument effects⟩
  | appArgument isValue notValue => cases typed with
      | app function argument effects => exact ⟨_, argument, .appArgument function effects⟩
  | bind notValue => cases typed with
      | bind initializer suffix => exact ⟨_, initializer, .bind suffix⟩
  | branch notValue => cases typed with
      | branch condition yes no => exact ⟨_, condition, .branch yes no⟩
  | perform notValue => cases typed with
      | perform operation available operand formed => exact ⟨_, operand, .perform operation available formed⟩
  | resume notValue => cases typed with
      | resume operand effects formed => exact ⟨_, operand, .resume effects formed⟩
  | resource notValue => cases typed with
      | resource initializer body noEscape noEffectEscape effects => exact ⟨_, initializer, .resource body noEscape noEffectEscape effects⟩
  | cleanup notValue => cases typed with
      | cleanup action body effects => exact ⟨_, action, .cleanup body effects⟩


def TicketNames : Ticket → List Nat
  | .none => []
  | .bound binder _ _ _ _ => [binder]

def BoundDependency (environment : TypeEnv) (ticket : Ticket) : Dependency → Prop
  | .resource _ => True
  | .variable name => ∃ type, environment name = some type
  | .ticket name => name ∈ TicketNames ticket

def LexicallyBound (environment : TypeEnv) (ticket : Ticket) (dependencies : List Dependency) : Prop :=
  ∀ dependency ∈ dependencies, BoundDependency environment ticket dependency

theorem lexical_nil : LexicallyBound environment ticket [] := by
  intro dependency member; cases member

theorem lexical_append (left : LexicallyBound environment ticket before)
    (right : LexicallyBound environment ticket after) : LexicallyBound environment ticket (before ++ after) := by
  intro dependency member
  rcases List.mem_append.mp member with here | there
  · exact left _ here
  · exact right _ there

theorem lexical_subset (bound : LexicallyBound environment ticket right) (subset : left ⊆ right) :
    LexicallyBound environment ticket left := fun dependency member => bound dependency (subset member)

theorem lexical_remove_variable
    (bound : LexicallyBound (environment.extend parameter input) ticket dependencies) :
    LexicallyBound environment ticket (without (.variable parameter) dependencies) := by
  intro dependency member
  obtain ⟨present, different⟩ := mem_without.mp member
  have known := bound dependency present
  cases dependency with
  | resource => trivial
  | ticket => exact known
  | «variable» name =>
      have unequal : name ≠ parameter := by simpa using different
      simpa only [BoundDependency, TypeEnv.extend, if_neg unequal] using known

theorem lexical_none_ticket
    (bound : LexicallyBound environment .none dependencies) (ticket : Ticket) :
    LexicallyBound environment ticket dependencies := by
  intro dependency member
  have known := bound dependency member
  cases dependency with
  | resource => trivial
  | «variable» => exact known
  | ticket => cases known

theorem lexical_remove_ticket
    (bound : LexicallyBound environment (.bound binder input answer residual closing) dependencies) :
    LexicallyBound environment .none (without (.ticket binder) dependencies) := by
  intro dependency member
  obtain ⟨present, different⟩ := mem_without.mp member
  have known := bound dependency present
  cases dependency with
  | resource => trivial
  | «variable» => exact known
  | ticket name =>
      have same : name = binder := List.mem_singleton.mp known
      exact False.elim (different (congrArg Dependency.ticket same))

theorem lexical_effect (effect : Effect) :
    LexicallyBound environment ticket ((effectAtoms effect).map Dependency.resource) := by
  intro dependency member
  obtain ⟨identity, present, rfl⟩ := List.mem_map.mp member
  trivial

theorem typed_lexical_dependencies (typed : Typed signature world environment ticket allowed code type) :
    LexicallyBound environment ticket code.dependencies := by
  induction typed using Typed.rec
    (motive_2 := fun _ environment _ _ _ clauses _ => LexicallyBound environment .none clauses.dependencies) with
  | unit | boolean | integer => exact lexical_nil
  | «variable» known formed =>
      intro dependency member
      obtain rfl := List.mem_singleton.mp member
      exact ⟨_, known⟩
  | reference =>
      intro dependency member
      obtain rfl := List.mem_singleton.mp member
      trivial
  | pair _ _ left right | app _ _ _ left right | cleanup _ _ _ left right => exact lexical_append left right
  | lambda _ _ body => exact lexical_none_ticket (lexical_remove_variable body) _
  | bind _ _ initializer suffix => exact lexical_append initializer (lexical_remove_variable suffix)
  | branch _ _ _ condition yes no => exact lexical_append (lexical_append condition yes) no
  | perform _ _ _ _ operand => exact lexical_append (lexical_effect _) operand
  | handle _ _ _ _ _ body clauses => exact lexical_append (lexical_append (lexical_effect _) body) (lexical_none_ticket clauses _)
  | resume _ _ _ operand =>
      intro dependency member
      rcases List.mem_cons.mp member with head | tail
      · subst dependency; exact List.mem_cons_self
      · exact operand _ tail
  | discard =>
      intro dependency member
      obtain rfl := List.mem_singleton.mp member
      exact List.mem_cons_self
  | @resource currentWorld currentEnvironment currentTicket currentAllowed init residual answer binder source
      initTyped bodyTyped resultBound effectsBound effects initializer body =>
      obtain ⟨identity, fresh⟩ := fresh_world_name currentWorld
      exact lexical_append initializer
        (lexical_subset (body identity fresh) (source.instantiation_keeps_dependencies _))
  | nil => exact lexical_nil
  | cons _ _ _ body rest => exact lexical_append (lexical_remove_ticket (lexical_remove_variable body)) rest


theorem typed_variable_known (typed : Typed signature world environment ticket allowed code type)
    (member : Dependency.variable name ∈ code.dependencies) : ∃ input, environment name = some input :=
  typed_lexical_dependencies typed _ member

theorem typed_ticket_known (typed : Typed signature world environment ticket allowed code type)
    (member : Dependency.ticket binder ∈ code.dependencies) : binder ∈ TicketNames ticket :=
  typed_lexical_dependencies typed _ member

/-- Closed runtime values follow from empty-environment typing and value form.
    Resource access is not part of ClosedValue and remains separately checked. -/
theorem typed_value_closed
    (typed : Typed signature world TypeEnv.empty ticket allowed value type) (isValue : value.IsValue) :
    ScopedExpressions.ClosedValue value := by
  refine ⟨isValue, typed_resource_closed typed, ?_⟩
  have noTicket := typed_value_transport typed isValue .none []
  intro dependency member
  cases dependency with
  | resource => trivial
  | «variable» name =>
      obtain ⟨input, known⟩ := typed_variable_known typed member
      cases known
  | ticket binder =>
      have impossible := typed_ticket_known noTicket member
      cases impossible

theorem typed_suffix_ready
    (typed : Typed signature world (TypeEnv.empty.extend parameter input) ticket allowed suffix type) :
    ScopedExpressions.ClosedExcept parameter suffix := by
  intro name member
  obtain ⟨type, known⟩ := typed_variable_known typed member
  by_cases same : name = parameter
  · exact same
  · simp [TypeEnv.extend, TypeEnv.empty, same] at known

/-- A value-form initializer suffices: typing supplies both raw lexical checks. -/
theorem typed_bind_value_progress
    (typed : Typed signature world TypeEnv.empty ticket allowed (.bind parameter value suffix) type)
    (isValue : value.IsValue) (scope : Scope) (tail : Stack) :
    RawStep ⟨.bind parameter value suffix, scope, tail⟩ ⟨suffix.subst parameter value, scope, tail⟩ [] [] ∧
      Typed signature world TypeEnv.empty ticket allowed (suffix.subst parameter value) type := by
  cases typed with
  | bind initializer suffix =>
      exact typed_bind_step (.bind initializer suffix) (typed_value_closed initializer isValue)
        (typed_suffix_ready suffix) scope tail

theorem typed_function_value (typed : Typed signature world environment ticket allowed value (.function input output latent))
    (isValue : value.IsValue) : ∃ parameter body, value = .lambda parameter body := by
  cases typed <;> simp_all [Code.IsValue]

theorem typed_boolean_value (typed : Typed signature world environment ticket allowed value .boolean)
    (isValue : value.IsValue) : ∃ boolean, value = .boolean boolean := by
  cases typed <;> simp_all [Code.IsValue]

theorem typed_integer_value (typed : Typed signature world environment ticket allowed value .integer)
    (isValue : value.IsValue) : ∃ number, value = .integer number := by
  cases typed <;> simp_all [Code.IsValue]

theorem typed_application_value_progress
    (typed : Typed signature world TypeEnv.empty ticket allowed (.app function argument) type)
    (functionValue : function.IsValue) (argumentValue : argument.IsValue) (scope : Scope) (tail : Stack) :
    ∃ after, RawStep ⟨.app function argument, scope, tail⟩ ⟨after, .none, tail⟩ [] [] ∧
      Typed signature world TypeEnv.empty .none allowed after type := by
  cases typed with
  | app function argument effects =>
      obtain ⟨parameter, body, rfl⟩ := typed_function_value function functionValue
      exact ⟨_, typed_beta_step (.app function argument effects) (typed_value_closed argument argumentValue)
        (typed_value_closed function functionValue) scope tail⟩

theorem typed_branch_value_progress
    (typed : Typed signature world TypeEnv.empty ticket allowed (.branch condition yes no) type)
    (isValue : condition.IsValue) (scope : Scope) (tail : Stack) :
    ∃ after, RawStep ⟨.branch condition yes no, scope, tail⟩ ⟨after, scope, tail⟩ [] [] ∧
      Typed signature world TypeEnv.empty ticket allowed after type := by
  cases typed with
  | branch condition yes no =>
      obtain ⟨boolean, rfl⟩ := typed_boolean_value condition isValue
      cases boolean with
      | false => exact ⟨_, .ifFalse _ _ _ _, no⟩
      | true => exact ⟨_, .ifTrue _ _ _ _, yes⟩

/-- Name correspondence only. The dynamic owner's existence, capability,
    ports, and consumption state remain separate configuration obligations. -/
inductive ScopeNamesMatch : Ticket → Scope → Prop where
  | none : ScopeNamesMatch .none .none
  | bound : ScopeNamesMatch (.bound binder input answer residual closing) (.ticket binder owner)

theorem lexical_translation_total
    (bound : LexicallyBound environment ticket dependencies) (matched : ScopeNamesMatch ticket scope) :
    ∃ pending, scope.translate dependencies = some pending := by
  induction dependencies with
  | nil => exact ⟨[], rfl⟩
  | cons dependency rest ih =>
      obtain ⟨pending, translated⟩ := ih (fun dep member => bound dep (List.mem_cons_of_mem _ member))
      cases dependency with
      | resource | «variable» => exact ⟨pending, translated⟩
      | ticket binder =>
          have known := bound (.ticket binder) List.mem_cons_self
          cases matched with
          | none => cases known
          | @bound localBinder input answer residual closing owner =>
              have same := List.mem_singleton.mp known
              subst binder
              exact ⟨owner :: pending, by simp [Execution.Scope.translate, Execution.Scope.resolve, translated]⟩

/-- An actual focus position gets its ports and pending-ticket translation
    from typing and structural scope-name correspondence. -/
theorem typed_focus_progress
    (focus : ScopedExecution.Focus whole child context)
    (typed : Typed signature world environment ticket allowed whole type)
    (matched : ScopeNamesMatch ticket scope) (tail : Stack) :
    ∃ plain : PlainData,
      RawStep ⟨whole, scope, tail⟩ ⟨child, scope, .push (.plain plain) tail⟩ [] [] ∧
      Typed signature world environment ticket allowed child (eraseType plain.input) ∧
      ContextTyped signature world environment ticket allowed plain.context (eraseType plain.input) type ∧
      eraseType plain.output = type ∧ plain.context = context ∧ plain.scope = scope := by
  obtain ⟨input, childTyped, contextTyped⟩ := typed_focus_decomposition focus typed
  have contextBound : LexicallyBound environment ticket context.dependencies := by
    apply lexical_subset (typed_lexical_dependencies typed)
    intro dependency member
    rw [← focus_reconstructs focus]
    exact (context_dependency_membership context child dependency).mpr (Or.inl member)
  obtain ⟨pending, translated⟩ := lexical_translation_total contextBound matched
  let plain : PlainData := ⟨context, scope, embedPort input, embedPort type, pending, translated⟩
  exact ⟨plain, .focus plain focus tail, by simpa [plain] using childTyped,
    by simpa [plain] using contextTyped, by simp [plain], rfl, rfl⟩


end Ash.OneShot.ScopedPorts

#print axioms Ash.OneShot.ScopedPorts.erase_embed_port
#print axioms Ash.OneShot.ScopedPorts.embedded_declared_resources
#print axioms Ash.OneShot.ScopedPorts.typed_resource_closed
#print axioms Ash.OneShot.ScopedPorts.context_plug_typed
#print axioms Ash.OneShot.ScopedPorts.typed_focus_decomposition
#print axioms Ash.OneShot.ScopedPorts.typed_lexical_dependencies
#print axioms Ash.OneShot.ScopedPorts.typed_value_closed
#print axioms Ash.OneShot.ScopedPorts.typed_suffix_ready
#print axioms Ash.OneShot.ScopedPorts.typed_bind_value_progress
#print axioms Ash.OneShot.ScopedPorts.typed_function_value
#print axioms Ash.OneShot.ScopedPorts.typed_boolean_value
#print axioms Ash.OneShot.ScopedPorts.typed_integer_value
#print axioms Ash.OneShot.ScopedPorts.typed_application_value_progress
#print axioms Ash.OneShot.ScopedPorts.typed_branch_value_progress
#print axioms Ash.OneShot.ScopedPorts.lexical_translation_total
#print axioms Ash.OneShot.ScopedPorts.typed_focus_progress
