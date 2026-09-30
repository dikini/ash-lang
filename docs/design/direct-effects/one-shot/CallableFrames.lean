import CallableContracts

/-!
Full callable contracts on the existing retained control forest. Composition
matches complete contracts. Historical records describe input/answer behavior;
they do not authorize ticket use or establish the independent joint invariant.
-/

namespace Ash.OneShot.CallableFrames
open Instantiation ScopedExpressions ScopedExecution
open CallableContracts (Contract Ticket Derives ClausesDerive)
open DeclarationResults (signature)

abbrev ContractEnvironment := CallableContracts.Environment

structure ResultRecord where
  input : Contract
  answer : Contract
  deriving DecidableEq, Repr

abbrev Registry := Nat → Option ResultRecord

def RegistryExtends (before after : Registry) : Prop :=
  ∀ owner record, before owner = some record → after owner = some record

def insert (registry : Registry) (owner : Nat) (record : ResultRecord) : Registry :=
  fun candidate => if candidate = owner then some record else registry candidate

theorem insert_extends (fresh : registry owner = none) :
    RegistryExtends registry (insert registry owner record) := by
  intro candidate previous known
  by_cases same : candidate = owner
  · subst candidate; rw [fresh] at known; contradiction
  · simp [insert, same, known]

inductive ScopeBound (registry : Registry) : Scope → Ticket → Prop where
  | none : ScopeBound registry .none .none
  | bound (known : registry owner = some record) :
      ScopeBound registry (.ticket binder owner) (.bound binder record.input record.answer)

theorem scope_extends (checked : ScopeBound before scope ticket)
    (extended : RegistryExtends before after) : ScopeBound after scope ticket := by
  cases checked with
  | none => exact .none
  | bound known => exact .bound (extended _ _ known)

theorem scope_resolves (checked : ScopeBound registry scope (.bound binder input answer))
    (resolved : scope.resolve binder = some owner) : registry owner = some ⟨input, answer⟩ := by
  cases checked with
  | bound known =>
      simp only [Execution.Scope.resolve, ↓reduceIte] at resolved
      cases Option.some.inj resolved
      exact known

theorem clauses_world_mono
    (checked : ClausesDerive declarations environment world requested answer clauses)
    (included : world ⊆ larger) : ClausesDerive declarations environment larger requested answer clauses := by
  revert larger
  induction checked using ClausesDerive.rec (motive_1 := fun _ _ _ _ _ _ => True) with
  | leaf | «variable» | pair | lambda | app | bind | branch | perform | handle | resume | resource => trivial
  | nil => intro larger included; exact .nil
  | cons known input output body rest ihBody ihRest =>
      intro larger included
      exact .cons known input output (CallableContracts.world_mono body _ included) (ihRest included)

inductive ContextReturns (declarations : DeclarationRegistry) (environment : ContractEnvironment)
    (world : List Nat) : Ticket → Context → Contract → Contract → Prop where
  | pairLeft (rightChecked : Derives declarations environment world ticket right b) :
      ContextReturns declarations environment world ticket (.pairLeft right) a (.pair a b)
  | pairRight (leftChecked : Derives declarations environment world ticket left a) :
      ContextReturns declarations environment world ticket (.pairRight left) b (.pair a b)
  | appFunction (argumentChecked : Derives declarations environment world ticket argument input) :
      ContextReturns declarations environment world ticket (.appFunction argument) (.function captures input output) output
  | appArgument (functionChecked : Derives declarations environment world ticket function (.function captures input output)) :
      ContextReturns declarations environment world ticket (.appArgument function) input output
  | bind (bodyChecked : Derives declarations (environment.extend name input) world ticket body output) :
      ContextReturns declarations environment world ticket (.bind name body) input output
  | branch (yesChecked : Derives declarations environment world ticket yes output)
      (noChecked : Derives declarations environment world ticket no output) :
      ContextReturns declarations environment world ticket (.branch yes no) condition output
  | perform (known : signature declarations requested operation = some (inputPort, outputPort))
      (finite : ClauseResults.PortBound outputPort bound) :
      ContextReturns declarations environment world ticket (.perform (freezeEffect requested) operation) operand (.storage bound)
  | resource (closed : (Code.resource binder .unit body).ResourceClosed)
      (bodyChecked : ∀ identity, identity ∉ world → Derives declarations environment (world ++ [identity]) ticket
        (body.instantiate (Environment.empty.bind binder identity)) output)
      (outward : output.storageOf ⊆ world) :
      ContextReturns declarations environment world ticket (.resource binder body) initializer output
  | resume : ContextReturns declarations environment world (.bound binder input answer) (.resume binder) input answer

theorem context_plug (context : ContextReturns declarations environment world ticket position input output)
    (child : Derives declarations environment world ticket code input) :
    Derives declarations environment world ticket (position.plug code) output := by
  cases context with
  | pairLeft right => exact .pair child right
  | pairRight left => exact .pair left child
  | appFunction argument => exact .app child argument
  | appArgument function => exact .app function child
  | bind body => exact .bind child body
  | branch yes no => exact .branch child yes no
  | perform known finite => exact .perform child known finite
  | resource closed body outward =>
      exact .resource child (GenerativeFrames.plug_resource_closed (.resource _ _) closed
        (CallableContracts.resource_closed child)) body outward
  | resume => exact .resume child

theorem returned_value_rebind
    (checked : Derives declarations environment world ticket value input) (closed : ClosedValue value) :
    Derives declarations savedEnvironment world savedTicket value input :=
  CallableContracts.value_ticket_transport
    (CallableContracts.closed_value_environment checked closed savedEnvironment) closed.1 savedTicket

theorem context_world_mono
    (context : ContextReturns declarations environment world ticket position input output)
    (included : world ⊆ larger) : ContextReturns declarations environment larger ticket position input output := by
  cases context with
  | pairLeft right => exact .pairLeft (CallableContracts.world_mono right larger included)
  | pairRight left => exact .pairRight (CallableContracts.world_mono left larger included)
  | appFunction argument => exact .appFunction (CallableContracts.world_mono argument larger included)
  | appArgument function => exact .appArgument (CallableContracts.world_mono function larger included)
  | bind body => exact .bind (CallableContracts.world_mono body larger included)
  | branch yes no => exact .branch (CallableContracts.world_mono yes larger included) (CallableContracts.world_mono no larger included)
  | perform known finite => exact .perform known finite
  | resource closed body outward =>
      exact .resource closed (fun identity fresh => CallableContracts.world_mono
        (body identity (fun member => fresh (included member))) (larger ++ [identity])
        (ScopedExpressions.append_subset included (List.Subset.refl _))) (outward.trans included)
  | resume => exact .resume

theorem focus_decompose (checked : Derives declarations environment world ticket whole output)
    (focus : Focus whole child position) :
    ∃ input, Derives declarations environment world ticket child input ∧
      ContextReturns declarations environment world ticket position input output := by
  cases checked with
  | leaf isValue => exact False.elim (ScopedExecution.focus_is_not_value focus isValue)
  | «variable» | lambda | handle => cases focus
  | pair left right => cases focus with
      | pairLeft => exact ⟨_, left, .pairLeft right⟩
      | pairRight => exact ⟨_, right, .pairRight left⟩
  | app function argument => cases focus with
      | appFunction => exact ⟨_, function, .appFunction argument⟩
      | appArgument => exact ⟨_, argument, .appArgument function⟩
  | bind initializer body => cases focus with
      | bind => exact ⟨_, initializer, .bind body⟩
  | branch condition yes no => cases focus with
      | branch => exact ⟨_, condition, .branch yes no⟩
  | perform operand known finite => cases focus with
      | perform => exact ⟨_, operand, .perform known finite⟩
  | resource initializer closed body outward => cases focus with
      | resource => exact ⟨_, initializer, .resource (List.append_eq_nil_iff.mp closed).2 body outward⟩
  | resume operand => cases focus with
      | resume => exact ⟨_, operand, .resume⟩

inductive StackReturns (declarations : DeclarationRegistry) (registry : Registry) (world : List Nat) :
    Stack → Contract → Contract → Prop where
  | nil : StackReturns declarations registry world .nil input input
  | plain (scope : ScopeBound registry plain.scope ticket)
      (context : ContextReturns declarations environment world ticket plain.context input middle)
      (rest : StackReturns declarations registry world tail middle output) :
      StackReturns declarations registry world (.push (.plain plain) tail) input output
  | cell (scope : ScopeBound registry caller ticket) (absent : identity ∉ input.storageOf)
      (rest : StackReturns declarations registry world tail input output) :
      StackReturns declarations registry world (.push (.cell identity payload caller answer) tail) input output
  | handler (scope : ScopeBound registry handler.scope ticket)
      (clauses : ClausesDerive declarations environment world handler.effectInst input handler.clauses)
      (rest : StackReturns declarations registry world tail input output) :
      StackReturns declarations registry world (.push (.handler handler) tail) input output
  | live (known : registry owner = some record) (scope : ScopeBound registry caller ticket)
      (saved : StackReturns declarations registry world capture record.input record.answer)
      (rest : StackReturns declarations registry world tail record.answer output) :
      StackReturns declarations registry world (.live owner operationInput answer capture caller tail) record.answer output
  | spent (known : registry owner = some record) (scope : ScopeBound registry caller ticket)
      (rest : StackReturns declarations registry world tail record.answer output) :
      StackReturns declarations registry world (.spent owner answer caller tail) record.answer output

variable {front capture tail : Stack}

theorem stack_append (front : StackReturns declarations registry world left input middle)
    (tail : StackReturns declarations registry world right middle output) :
    StackReturns declarations registry world (left.append right) input output := by
  induction front with
  | nil => exact tail
  | plain scope context rest ih => exact .plain scope context (ih tail)
  | cell scope absent rest ih => exact .cell scope absent (ih tail)
  | handler scope clauses rest ih => exact .handler scope clauses (ih tail)
  | live known scope saved rest ihSaved ihRest => exact .live known scope saved (ihRest tail)
  | spent known scope rest ih => exact .spent known scope (ih tail)

theorem stack_decompose
    (checked : StackReturns declarations registry world (front.append tail) input output) :
    ∃ middle, StackReturns declarations registry world front input middle ∧
      StackReturns declarations registry world tail middle output := by
  induction front generalizing input output with
  | nil => exact ⟨input, .nil, checked⟩
  | push frame rest ih => cases checked with
      | plain scope context next =>
          obtain ⟨middle, inside, outside⟩ := ih next
          exact ⟨middle, .plain scope context inside, outside⟩
      | cell scope absent next =>
          obtain ⟨middle, inside, outside⟩ := ih next
          exact ⟨middle, .cell scope absent inside, outside⟩
      | handler scope clauses next =>
          obtain ⟨middle, inside, outside⟩ := ih next
          exact ⟨middle, .handler scope clauses inside, outside⟩
  | live owner operationInput answer saved scope rest ihSaved ihRest => cases checked with
      | live known scope saved next =>
          obtain ⟨middle, inside, outside⟩ := ihRest next
          exact ⟨middle, .live known scope saved inside, outside⟩
  | spent owner answer scope rest ih => cases checked with
      | spent known scope next =>
          obtain ⟨middle, inside, outside⟩ := ih next
          exact ⟨middle, .spent known scope inside, outside⟩

theorem stack_registry_extends (checked : StackReturns declarations registry world stack input output)
    (extended : RegistryExtends registry larger) : StackReturns declarations larger world stack input output := by
  induction checked with
  | nil => exact .nil
  | plain scope context rest ih => exact .plain (scope_extends scope extended) context ih
  | cell scope absent rest ih => exact .cell (scope_extends scope extended) absent ih
  | handler scope clauses rest ih => exact .handler (scope_extends scope extended) clauses ih
  | live known scope saved rest ihSaved ihRest => exact .live (extended _ _ known) (scope_extends scope extended) ihSaved ihRest
  | spent known scope rest ih => exact .spent (extended _ _ known) (scope_extends scope extended) ih

theorem stack_world_mono (checked : StackReturns declarations registry world stack input output)
    (included : world ⊆ larger) : StackReturns declarations registry larger stack input output := by
  induction checked with
  | nil => exact .nil
  | plain scope context rest ih => exact .plain scope (context_world_mono context included) ih
  | cell scope absent rest ih => exact .cell scope absent ih
  | handler scope clauses rest ih => exact .handler scope (clauses_world_mono clauses included) ih
  | live known scope saved rest ihSaved ihRest => exact .live known scope ihSaved ihRest
  | spent known scope rest ih => exact .spent known scope ih

theorem handler_cut_certificate (cut : HandlerCut requested whole capture tail handler)
    (checked : StackReturns declarations registry world whole input output) :
    ∃ environment ticket answer,
      ScopeBound registry handler.scope ticket ∧
      ClausesDerive declarations environment world handler.effectInst answer handler.clauses ∧
      StackReturns declarations registry world capture input answer ∧
      StackReturns declarations registry world tail answer output := by
  induction cut generalizing input output with
  | hit handler tail same => cases checked with
      | handler scope clauses rest => exact ⟨_, _, _, scope, clauses, .handler scope clauses .nil, rest⟩
  | push frame rest capture tail handler miss next ih => cases checked with
      | plain scope context next =>
          obtain ⟨environment, ticket, answer, savedScope, clauses, inside, outside⟩ := ih next
          exact ⟨environment, ticket, answer, savedScope, clauses, .plain scope context inside, outside⟩
      | cell scope absent next =>
          obtain ⟨environment, ticket, answer, savedScope, clauses, inside, outside⟩ := ih next
          exact ⟨environment, ticket, answer, savedScope, clauses, .cell scope absent inside, outside⟩
      | handler scope clauses next =>
          obtain ⟨environment, ticket, answer, savedScope, savedClauses, inside, outside⟩ := ih next
          exact ⟨environment, ticket, answer, savedScope, savedClauses, .handler scope clauses inside, outside⟩
  | live owner operationInput answer saved scope rest capture tail handler next ih => cases checked with
      | live known scope saved next =>
          obtain ⟨environment, ticket, answer, savedScope, clauses, inside, outside⟩ := ih next
          exact ⟨environment, ticket, answer, savedScope, clauses, .live known scope saved inside, outside⟩
  | spent owner answer scope rest capture tail handler next ih => cases checked with
      | spent known scope next =>
          obtain ⟨environment, ticket, answer, savedScope, clauses, inside, outside⟩ := ih next
          exact ⟨environment, ticket, answer, savedScope, clauses, .spent known scope inside, outside⟩

theorem resume_recomposition (known : registry owner = some record)
    (checked : StackReturns declarations registry world
      (front.append (.live owner operationInput answer capture caller tail)) record.answer output) :
    StackReturns declarations registry world
      (capture.append (front.append (.spent owner answer caller tail))) record.input output := by
  obtain ⟨middle, frontChecked, boundary⟩ := stack_decompose checked
  cases boundary with
  | live actual scope saved rest =>
      have same := Option.some.inj (actual.symm.trans known)
      subst record
      exact stack_append saved (stack_append frontChecked (.spent actual scope rest))

def ConfigurationReturns (declarations : DeclarationRegistry) (registry : Registry) (world : List Nat)
    (configuration : Configuration) (output : Contract) : Prop :=
  ∃ environment ticket input, ScopeBound registry configuration.scope ticket ∧
    Derives declarations environment world ticket configuration.expression input ∧
    StackReturns declarations registry world configuration.stack input output

theorem focus_step (focus : Focus whole child plain.context)
    (checked : ConfigurationReturns declarations registry world ⟨whole, plain.scope, tail⟩ output) :
    RawStep ⟨whole, plain.scope, tail⟩ ⟨child, plain.scope, .push (.plain plain) tail⟩ [] [] ∧
    ConfigurationReturns declarations registry world ⟨child, plain.scope, .push (.plain plain) tail⟩ output := by
  obtain ⟨environment, ticket, contract, scope, code, stack⟩ := checked
  obtain ⟨input, childChecked, context⟩ := focus_decompose code focus
  exact ⟨.focus plain focus tail, environment, ticket, input, scope, childChecked, .plain scope context stack⟩

theorem plug_step
    (checked : ConfigurationReturns declarations registry world ⟨value, scope, .push (.plain plain) tail⟩ output)
    (closed : ClosedValue value) :
    RawStep ⟨value, scope, .push (.plain plain) tail⟩ ⟨plain.context.plug value, plain.scope, tail⟩ [] [] ∧
    ConfigurationReturns declarations registry world ⟨plain.context.plug value, plain.scope, tail⟩ output := by
  obtain ⟨environment, ticket, input, scopeChecked, code, stack⟩ := checked
  cases stack with
  | plain savedScope context rest =>
      exact ⟨.plug plain value closed scope tail, _, _, _, savedScope,
        context_plug context (returned_value_rebind code closed), rest⟩

theorem beta_step
    (checked : ConfigurationReturns declarations registry world ⟨.app (.lambda parameter body) argument, scope, tail⟩ output)
    (argumentClosed : ClosedValue argument) (functionClosed : ClosedValue (.lambda parameter body)) :
    RawStep ⟨.app (.lambda parameter body) argument, scope, tail⟩ ⟨body.subst parameter argument, .none, tail⟩ [] [] ∧
    ConfigurationReturns declarations registry world ⟨body.subst parameter argument, .none, tail⟩ output := by
  obtain ⟨environment, ticket, input, scopeChecked, code, stack⟩ := checked
  exact ⟨.beta _ _ _ _ _ argumentClosed functionClosed, environment, .none, input, .none,
    CallableContracts.beta_result code argumentClosed, stack⟩

theorem bind_step
    (checked : ConfigurationReturns declarations registry world ⟨.bind name value body, scope, tail⟩ output)
    (closed : ClosedValue value) (ready : ClosedExcept name body) :
    RawStep ⟨.bind name value body, scope, tail⟩ ⟨body.subst name value, scope, tail⟩ [] [] ∧
    ConfigurationReturns declarations registry world ⟨body.subst name value, scope, tail⟩ output := by
  obtain ⟨environment, ticket, input, scopeChecked, code, stack⟩ := checked
  exact ⟨.bind _ _ _ _ _ closed ready, environment, ticket, input, scopeChecked,
    CallableContracts.bind_result code closed, stack⟩

theorem resume_step (resolved : scope.resolve binder = some owner)
    (checked : ConfigurationReturns declarations registry world
      ⟨.resume binder value, scope, front.append (.live owner operationInput answer capture caller tail)⟩ output)
    (closed : ClosedValue value) :
    RawStep ⟨.resume binder value, scope, front.append (.live owner operationInput answer capture caller tail)⟩
      ⟨value, scope, capture.append (front.append (.spent owner answer caller tail))⟩ [] [.ticket owner] ∧
    ConfigurationReturns declarations registry world
      ⟨value, scope, capture.append (front.append (.spent owner answer caller tail))⟩ output := by
  obtain ⟨environment, ticket, bound, scopeChecked, code, stack⟩ := checked
  cases code with
  | leaf isValue => cases isValue
  | resume operand =>
      have known := scope_resolves scopeChecked resolved
      exact ⟨.resume binder owner scope caller operationInput answer front capture tail value closed resolved,
        environment, _, _, scopeChecked, operand, resume_recomposition known stack⟩

theorem handler_entry_step
    (checked : ConfigurationReturns declarations registry world
      ⟨.handle (freezeEffect handler.effectInst) body handler.clauses, handler.scope, tail⟩ output) :
    RawStep ⟨.handle (freezeEffect handler.effectInst) body handler.clauses, handler.scope, tail⟩
      ⟨body, handler.scope, .push (.handler handler) tail⟩ [] [] ∧
    ConfigurationReturns declarations registry world ⟨body, handler.scope, .push (.handler handler) tail⟩ output := by
  obtain ⟨environment, ticket, input, scopeChecked, code, stack⟩ := checked
  generalize same : freezeEffect handler.effectInst = effect at code
  cases code with
  | leaf isValue => cases isValue
  | handle body clauses closed =>
      have identical := freeze_effect_injective same
      cases identical
      exact ⟨.enterHandler handler _ tail, environment, ticket, input, scopeChecked, body, .handler scopeChecked clauses stack⟩

theorem handler_return_step
    (checked : ConfigurationReturns declarations registry world ⟨value, scope, .push (.handler handler) tail⟩ output)
    (closed : ClosedValue value) :
    RawStep ⟨value, scope, .push (.handler handler) tail⟩ ⟨value, handler.scope, tail⟩ [] [] ∧
    ConfigurationReturns declarations registry world ⟨value, handler.scope, tail⟩ output := by
  obtain ⟨environment, ticket, input, scopeChecked, code, stack⟩ := checked
  cases stack with
  | handler savedScope clauses rest =>
      exact ⟨.leaveHandler handler value closed scope tail, environment, _, input, savedScope, returned_value_rebind code closed, rest⟩

theorem clause_return_step
    (checked : ConfigurationReturns declarations registry world ⟨value, scope, .spent owner answer caller tail⟩ output)
    (closed : ClosedValue value) :
    RawStep ⟨value, scope, .spent owner answer caller tail⟩ ⟨value, caller, tail⟩ [] [] ∧
    ConfigurationReturns declarations registry world ⟨value, caller, tail⟩ output := by
  obtain ⟨environment, ticket, input, scopeChecked, code, stack⟩ := checked
  cases stack with
  | spent known savedScope rest =>
      exact ⟨.leaveClause owner answer value closed scope caller tail, environment, _, _, savedScope, returned_value_rebind code closed, rest⟩

theorem resource_step
    (checked : ConfigurationReturns declarations registry world ⟨.resource binder (.integer payload) body, scope, tail⟩ output)
    (fresh : identity ∉ world) :
    RawStep ⟨.resource binder (.integer payload) body, scope, tail⟩
      ⟨body.instantiate (Environment.empty.bind binder identity), scope, .push (.cell identity payload scope answer) tail⟩
      [.resource identity] [] ∧
    ConfigurationReturns declarations registry (world ++ [identity])
      ⟨body.instantiate (Environment.empty.bind binder identity), scope, .push (.cell identity payload scope answer) tail⟩ output := by
  obtain ⟨environment, ticket, input, scopeChecked, code, stack⟩ := checked
  cases code with
  | leaf isValue => cases isValue
  | resource initializer closed bodyChecked outward =>
      exact ⟨.enterCell binder identity payload body scope answer tail closed, environment, ticket, input, scopeChecked,
        bodyChecked identity fresh, .cell scopeChecked (fun member => fresh (outward member))
          (stack_world_mono stack (List.subset_append_left _ _))⟩

theorem cell_return_step
    (checked : ConfigurationReturns declarations registry world
      ⟨value, scope, .push (.cell identity payload caller answer) tail⟩ output)
    (closed : ClosedValue value) :
    RawStep ⟨value, scope, .push (.cell identity payload caller answer) tail⟩ ⟨value, caller, tail⟩ [] [.resource identity] ∧
    identity ∉ Syntax.resourceDependencies value.dependencies ∧
    ConfigurationReturns declarations registry world ⟨value, caller, tail⟩ output := by
  obtain ⟨environment, ticket, input, scopeChecked, code, stack⟩ := checked
  cases stack with
  | cell savedScope absent rest =>
      exact ⟨.leaveCell identity payload answer caller scope value closed tail,
        fun member => absent (CallableContracts.value_support code closed.1 member),
        environment, _, input, savedScope, returned_value_rebind code closed, rest⟩

theorem selected_clause (selected : ClauseAt operation clauses parameter binder body)
    (checked : ClausesDerive declarations environment world requested answer clauses) :
    ∃ inputPort outputPort argumentBound resumeBound,
      signature declarations requested operation = some (inputPort, outputPort) ∧
      ClauseResults.PortBound inputPort argumentBound ∧ ClauseResults.PortBound outputPort resumeBound ∧
      Derives declarations (environment.extend parameter (.storage argumentBound)) world
        (.bound binder (.storage resumeBound) answer) body answer := by
  induction selected with
  | hit => cases checked with
      | cons known input output body rest => exact ⟨_, _, _, _, known, input, output, body⟩
  | pass different selected ih => cases checked with
      | cons known input output body rest => exact ih rest

theorem typed_value_storage_contract
    (typed : ScopedPorts.Typed (signature declarations) world ScopedPorts.TypeEnv.empty ticket allowed value port)
    (isValue : value.IsValue) (finite : ClauseResults.PortBound port bound) :
    Derives declarations environment world contractTicket value (.storage bound) := by
  obtain ⟨shape, rfl⟩ := ContinuationBounds.port_bound_finite port finite
  have closed := ScopedPorts.typed_value_closed typed isValue
  exact .leaf isValue closed.2.1 (CallableContracts.captures_closed closed (by
    rw [ScopedPorts.typed_first_order_value_support typed isValue shape]
    exact List.Subset.refl _))

theorem selected_clause_substitution
    (selected : ClauseAt operation clauses parameter binder body)
    (checked : ClausesDerive declarations environment world requested answer clauses)
    (known : signature declarations requested operation = some (inputPort, outputPort))
    (typed : ScopedPorts.Typed (signature declarations) world ScopedPorts.TypeEnv.empty ticket allowed operand inputPort)
    (isValue : operand.IsValue) :
    ClosedValue operand ∧ ∃ argumentBound resumeBound,
      ClauseResults.PortBound inputPort argumentBound ∧ ClauseResults.PortBound outputPort resumeBound ∧
      Derives declarations environment world (.bound binder (.storage resumeBound) answer)
        (body.subst parameter operand) answer := by
  obtain ⟨actualInput, actualOutput, argumentBound, resumeBound, declared, input, output, bodyChecked⟩ :=
    selected_clause selected checked
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (declared.symm.trans known))
  have closed := ScopedPorts.typed_value_closed typed isValue
  exact ⟨closed, argumentBound, resumeBound, input, output,
    CallableContracts.substitution bodyChecked (typed_value_storage_contract typed isValue input) closed⟩

theorem declared_output_contract
    (checked : Derives declarations environment world ticket (.perform (freezeEffect requested) operation operand) result)
    (known : signature declarations requested operation = some (inputPort, outputPort))
    (finite : ClauseResults.PortBound outputPort bound) : result = .storage bound := by
  generalize same : freezeEffect requested = effect at checked
  cases checked with
  | leaf isValue => cases isValue
  | perform operand actual output =>
      have identical := freeze_effect_injective same
      cases identical
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (actual.symm.trans known))
      exact congrArg Contract.storage (Option.some.inj (output.symm.trans finite))

theorem capture_step
    (cut : HandlerCut requested whole capture tail handler)
    (selected : ClauseAt operation handler.clauses parameter binder body)
    (typed : ScopedPorts.ConfigurationTyped (signature declarations) tickets world
      ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ result)
    (known : signature declarations requested operation = some (inputPort, outputPort))
    (isValue : operand.IsValue)
    (checked : ConfigurationReturns declarations registry world
      ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ output)
    (fresh : registry owner = none) :
    let after : Configuration := ⟨body.subst parameter operand, .ticket binder owner,
      .live owner (ScopedPorts.embedPort outputPort) handler.answer capture handler.scope tail⟩
    RawStep ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
    ∃ record inputBound, record.input = .storage inputBound ∧ ClauseResults.PortBound outputPort inputBound ∧
      RegistryExtends registry (insert registry owner record) ∧
      ConfigurationReturns declarations (insert registry owner record) world after output := by
  obtain ⟨environment, ticket, contract, currentScope, code, stack⟩ := checked
  obtain ⟨savedEnvironment, savedTicket, answerContract, savedScope, clauses, saved, outside⟩ :=
    handler_cut_certificate cut stack
  obtain ⟨resultPort, current, stackTyped⟩ := typed
  cases current with
  | checked scopeTyped currentTyped =>
      obtain ⟨actualInput, declared, available, operandTyped⟩ := ScopedPorts.typed_perform_inversion currentTyped
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (known.symm.trans declared))
      have handlerKnown := known
      rw [← ScopedTyping.handler_cut_instance cut] at handlerKnown
      obtain ⟨closed, argumentBound, resumeBound, inputFinite, outputFinite, substituted⟩ :=
        selected_clause_substitution selected clauses handlerKnown operandTyped isValue
      have resultSame := declared_output_contract code known outputFinite
      subst contract
      let record : ResultRecord := ⟨.storage resumeBound, answerContract⟩
      have extended : RegistryExtends registry (insert registry owner record) := insert_extends fresh
      have recorded : insert registry owner record owner = some record := by simp [insert]
      obtain ⟨savedTyped, outsideTyped, handlerTyped⟩ := ScopedPorts.handler_cut_retains_typing cut stackTyped
      cases handlerTyped with
      | handler caller clausesTyped coverage unique =>
          obtain ⟨clauseInput, clauseOutput, clauseKnown, bodyTyped⟩ := ScopedPorts.selected_clause_typed selected clausesTyped
          exact ⟨.capture requested operation parameter binder owner operand body scope whole capture tail handler
              (ScopedPorts.embedPort _) cut selected closed (ScopedPorts.typed_suffix_ready bodyTyped),
            record, resumeBound, rfl, outputFinite, extended, savedEnvironment, _, answerContract, .bound recorded,
            substituted, .live recorded (scope_extends savedScope extended)
              (stack_registry_extends saved extended) (stack_registry_extends outside extended)⟩

namespace Examples
open CallableContracts.Examples (scalar identityContract identity)
open GenerativeFrames.Examples (declarations)
open ContinuationBounds.Examples (family)

def emptyRegistry : Registry := fun _ => none
def functionType : Ty := .function .integer .integer [] []
def clauseBody : Code := .bind 4 (.resume 10 (.integer 17)) (.variable 4)
def clauses : Clauses := .cons 0 5 10 clauseBody .nil
def handler : HandlerData := ⟨12, family, clauses, .none, functionType, rfl⟩
def pendingFunction : PlainData := ⟨.bind 2 identity, .none, .integer, functionType, [], rfl⟩
def outsideCall : PlainData := ⟨.appFunction (.integer 17), .none, functionType, .integer, [], rfl⟩
def clauseBinding : PlainData := ⟨.bind 4 (.variable 4), .ticket 10 5, functionType, functionType, [], rfl⟩
def captured : Stack := .push (.plain pendingFunction) (.push (.handler handler) .nil)
def outside : Stack := .push (.plain outsideCall) .nil
def spent : Stack := .spent 5 functionType .none outside
def clauseFront : Stack := .push (.plain clauseBinding) .nil

def s0 : Configuration := ⟨.perform (freezeEffect family) 0 .unit, .none, captured.append outside⟩
def s1 : Configuration := ⟨clauseBody, .ticket 10 5, .live 5 .integer functionType captured .none outside⟩
def s2 : Configuration := ⟨.resume 10 (.integer 17), .ticket 10 5,
  clauseFront.append (.live 5 .integer functionType captured .none outside)⟩
def s3 : Configuration := ⟨.integer 17, .ticket 10 5, captured.append (clauseFront.append spent)⟩
def s4 : Configuration := ⟨.bind 2 (.integer 17) identity, .none, .push (.handler handler) (clauseFront.append spent)⟩
def s5 : Configuration := ⟨identity, .none, .push (.handler handler) (clauseFront.append spent)⟩
def s6 : Configuration := ⟨identity, .none, clauseFront.append spent⟩
def s7 : Configuration := ⟨.bind 4 identity (.variable 4), .ticket 10 5, spent⟩
def s8 : Configuration := ⟨identity, .ticket 10 5, spent⟩
def s9 : Configuration := ⟨identity, .none, outside⟩
def s10 : Configuration := ⟨.app identity (.integer 17), .none, .nil⟩
def s11 : Configuration := ⟨.integer 17, .none, .nil⟩

theorem identity_contract (environment : ContractEnvironment) (ticket : Ticket) :
    Derives declarations environment [] ticket identity identityContract := .lambda (.variable rfl) .nil

theorem clauses_contract : ClausesDerive declarations CallableContracts.Environment.empty [] family identityContract clauses :=
  .cons rfl rfl rfl (.bind (.resume (.leaf trivial rfl .nil)) (.variable rfl)) .nil

theorem request_contract : ConfigurationReturns declarations emptyRegistry [] s0 scalar :=
  ⟨CallableContracts.Environment.empty, .none, scalar, .none, .perform (operandContract := scalar) (.leaf trivial rfl .nil) rfl rfl,
    .plain (environment := CallableContracts.Environment.empty) .none (.bind (identity_contract _ _)) (.handler .none clauses_contract
      (.plain (environment := CallableContracts.Environment.empty) .none (.appFunction (.leaf trivial rfl .nil)) .nil))⟩

theorem request_typed : ScopedPorts.ConfigurationTyped (signature declarations) (fun _ => none) [] s0 .integer := by
  refine ⟨.integer, .checked (allowed := [family]) .none (.perform rfl (by simp) .unit (List.nil_subset _)), ?_⟩
  refine .push (.plain (allowed := []) .none (.bind (.lambda (.variable rfl (List.nil_subset _)) (List.nil_subset _)))) ?_
  refine .push (.handler ⟨.none, .none⟩
    (.cons (residual := []) rfl (.bind (.resume .integer (List.nil_subset _) (List.nil_subset _)) (.variable rfl (List.nil_subset _))) .nil)
    (ClauseResults.Examples.single_coverage _ _ _) (by decide)) ?_
  exact .push (.plain (allowed := []) .none (.appFunction .integer (List.nil_subset _))) .nil

theorem selected_cut : HandlerCut family s0.stack captured outside handler :=
  .push (.plain pendingFunction) _ _ _ _ (by decide) (.hit handler outside rfl)

theorem capture_returns_callable : RawStep s0 s1 [.ticket 5] [] ∧
    ∃ registry, ConfigurationReturns declarations registry [] s1 scalar := by
  obtain ⟨step, record, inputBound, inputSame, finite, extension, after⟩ :=
    capture_step selected_cut .hit request_typed (by rfl) trivial request_contract (owner := 5) rfl
  refine ⟨?_, insert emptyRegistry 5 record, ?_⟩
  · simpa [s0, s1, clauses, clauseBody, handler, Code.subst, ScopedPorts.embedPort, ScopedPorts.eraseType] using step
  · simpa [s1, clauses, clauseBody, handler, Code.subst, ScopedPorts.embedPort, ScopedPorts.eraseType] using after

theorem identity_closed : ClosedValue identity := by
  simp [identity, ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Code.dependencies, Syntax.without]

theorem continue_after_capture
    (initial : ConfigurationReturns declarations registry [] s1 scalar) :
    RawTrace s1 s11 [] [.ticket 5] ∧ ConfigurationReturns declarations registry [] s11 scalar := by
  have integerClosed : ClosedValue (.integer 17) := by simp [ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Code.dependencies]
  have firstFocus : Focus clauseBody (.resume 10 (.integer 17)) clauseBinding.context :=
    .bind (by intro impossible; cases impossible)
  obtain ⟨e1, c2⟩ := focus_step (plain := clauseBinding) firstFocus initial
  change ConfigurationReturns declarations registry [] s2 scalar at c2
  obtain ⟨e2, c3⟩ := resume_step (front := clauseFront) (capture := captured) (tail := outside) rfl c2 integerClosed
  obtain ⟨e3, c4⟩ := plug_step c3 integerClosed
  have readyIdentity : ClosedExcept 2 identity := by
    intro dependency member
    simp [identity, Code.dependencies, Syntax.without] at member
  obtain ⟨e4, c5⟩ := bind_step c4 integerClosed readyIdentity
  change ConfigurationReturns declarations registry [] s5 scalar at c5
  obtain ⟨e5, c6⟩ := handler_return_step c5 identity_closed
  obtain ⟨e6, c7⟩ := plug_step c6 identity_closed
  have readyVariable : ClosedExcept 4 (.variable 4) := by intro dependency member; simpa [Code.dependencies] using member
  obtain ⟨e7, c8⟩ := bind_step c7 identity_closed readyVariable
  change ConfigurationReturns declarations registry [] s8 scalar at c8
  obtain ⟨e8, c9⟩ := clause_return_step c8 identity_closed
  obtain ⟨e9, c10⟩ := plug_step c9 identity_closed
  obtain ⟨e10, c11⟩ := beta_step c10 integerClosed identity_closed
  exact ⟨.next e1 (.next e2 (.next e3 (.next e4 (.next e5 (.next e6 (.next e7 (.next e8
    (.next e9 (.next e10 (.refl s11)))))))))), c11⟩

theorem captured_callable_is_invoked : RawTrace s0 s11 [.ticket 5] [.ticket 5] ∧
    ∃ registry, ConfigurationReturns declarations registry [] s11 scalar := by
  obtain ⟨capture, registry, after⟩ := capture_returns_callable
  obtain ⟨execution, final⟩ := continue_after_capture after
  exact ⟨.next capture execution, registry, final⟩

theorem storage_cannot_fill_callable_frame :
    ¬ StackReturns declarations registry [] outside scalar scalar := by
  intro checked
  cases checked with
  | plain scope context rest => cases context

end Examples

end Ash.OneShot.CallableFrames

#print axioms Ash.OneShot.CallableFrames.insert_extends
#print axioms Ash.OneShot.CallableFrames.scope_extends
#print axioms Ash.OneShot.CallableFrames.scope_resolves
#print axioms Ash.OneShot.CallableFrames.clauses_world_mono
#print axioms Ash.OneShot.CallableFrames.context_plug
#print axioms Ash.OneShot.CallableFrames.returned_value_rebind
#print axioms Ash.OneShot.CallableFrames.context_world_mono
#print axioms Ash.OneShot.CallableFrames.focus_decompose
#print axioms Ash.OneShot.CallableFrames.stack_append
#print axioms Ash.OneShot.CallableFrames.stack_decompose
#print axioms Ash.OneShot.CallableFrames.stack_registry_extends
#print axioms Ash.OneShot.CallableFrames.stack_world_mono
#print axioms Ash.OneShot.CallableFrames.handler_cut_certificate
#print axioms Ash.OneShot.CallableFrames.resume_recomposition
#print axioms Ash.OneShot.CallableFrames.focus_step
#print axioms Ash.OneShot.CallableFrames.plug_step
#print axioms Ash.OneShot.CallableFrames.beta_step
#print axioms Ash.OneShot.CallableFrames.bind_step
#print axioms Ash.OneShot.CallableFrames.resume_step
#print axioms Ash.OneShot.CallableFrames.handler_entry_step
#print axioms Ash.OneShot.CallableFrames.handler_return_step
#print axioms Ash.OneShot.CallableFrames.clause_return_step
#print axioms Ash.OneShot.CallableFrames.resource_step
#print axioms Ash.OneShot.CallableFrames.cell_return_step
#print axioms Ash.OneShot.CallableFrames.selected_clause
#print axioms Ash.OneShot.CallableFrames.typed_value_storage_contract
#print axioms Ash.OneShot.CallableFrames.selected_clause_substitution
#print axioms Ash.OneShot.CallableFrames.declared_output_contract
#print axioms Ash.OneShot.CallableFrames.capture_step
#print axioms Ash.OneShot.CallableFrames.Examples.identity_contract
#print axioms Ash.OneShot.CallableFrames.Examples.clauses_contract
#print axioms Ash.OneShot.CallableFrames.Examples.request_contract
#print axioms Ash.OneShot.CallableFrames.Examples.request_typed
#print axioms Ash.OneShot.CallableFrames.Examples.selected_cut
#print axioms Ash.OneShot.CallableFrames.Examples.capture_returns_callable
#print axioms Ash.OneShot.CallableFrames.Examples.identity_closed
#print axioms Ash.OneShot.CallableFrames.Examples.continue_after_capture
#print axioms Ash.OneShot.CallableFrames.Examples.captured_callable_is_invoked
#print axioms Ash.OneShot.CallableFrames.Examples.storage_cannot_fill_callable_frame
