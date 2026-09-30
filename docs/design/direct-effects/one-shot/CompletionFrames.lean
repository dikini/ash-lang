import CompletionContracts

/-!
Full callable contracts on the existing retained control forest. Composition
matches complete contracts. Historical records describe input/answer behavior;
they do not authorize ticket use or establish the independent joint invariant.
-/

namespace Ash.OneShot.CompletionFrames
open Instantiation ScopedExpressions ScopedExecution
open CompletionContracts (Contract Ticket Derives ClausesDerive)
open DeclarationResults (signature)

abbrev ContractEnvironment := CompletionContracts.Environment

open CallableFrames (ResultRecord Registry RegistryExtends insert insert_extends ScopeBound scope_extends scope_resolves)

theorem clauses_world_mono
    (checked : ClausesDerive declarations environment world requested answer clauses)
    (included : world ⊆ larger) : ClausesDerive declarations environment larger requested answer clauses := by
  revert larger
  induction checked using ClausesDerive.rec (motive_1 := fun _ _ _ _ _ _ => True) with
  | leaf | «variable» | pair | lambda | app | bind | branch | perform | handle | resume | resource | discard | cleanup => trivial
  | nil => intro larger included; exact .nil
  | cons known input output body rest ihBody ihRest =>
      intro larger included
      exact .cons known input output (CompletionContracts.world_mono body _ included) (ihRest included)

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
  | cleanup (bodyChecked : Derives declarations environment world ticket body output) :
      ContextReturns declarations environment world ticket (.cleanup body) (.function captures (.storage []) (.storage [])) output
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
        (CompletionContracts.resource_closed child)) body outward
  | cleanup body => exact .cleanup child body
  | resume => exact .resume child

theorem returned_value_rebind
    (checked : Derives declarations environment world ticket value input) (closed : ClosedValue value) :
    Derives declarations savedEnvironment world savedTicket value input :=
  CompletionContracts.value_ticket_transport
    (CompletionContracts.closed_value_environment checked closed savedEnvironment) closed.1 savedTicket

theorem context_world_mono
    (context : ContextReturns declarations environment world ticket position input output)
    (included : world ⊆ larger) : ContextReturns declarations environment larger ticket position input output := by
  cases context with
  | pairLeft right => exact .pairLeft (CompletionContracts.world_mono right larger included)
  | pairRight left => exact .pairRight (CompletionContracts.world_mono left larger included)
  | appFunction argument => exact .appFunction (CompletionContracts.world_mono argument larger included)
  | appArgument function => exact .appArgument (CompletionContracts.world_mono function larger included)
  | bind body => exact .bind (CompletionContracts.world_mono body larger included)
  | branch yes no => exact .branch (CompletionContracts.world_mono yes larger included) (CompletionContracts.world_mono no larger included)
  | perform known finite => exact .perform known finite
  | resource closed body outward =>
      exact .resource closed (fun identity fresh => CompletionContracts.world_mono
        (body identity (fun member => fresh (included member))) (larger ++ [identity])
        (ScopedExpressions.append_subset included (List.Subset.refl _))) (outward.trans included)
  | cleanup body => exact .cleanup (CompletionContracts.world_mono body larger included)
  | resume => exact .resume

theorem focus_decompose (checked : Derives declarations environment world ticket whole output)
    (focus : Focus whole child position) :
    ∃ input, Derives declarations environment world ticket child input ∧
      ContextReturns declarations environment world ticket position input output := by
  cases checked with
  | leaf isValue => exact False.elim (ScopedExecution.focus_is_not_value focus isValue)
  | «variable» | lambda | handle | discard => cases focus
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
  | cleanup callback body => cases focus with
      | cleanup => exact ⟨_, callback, .cleanup body⟩

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
  | armed (scope : ScopeBound registry action.scope ticket)
      (callback : Derives declarations environment world .none action.action (.function captures (.storage []) (.storage [])))
      (rest : StackReturns declarations registry world tail input output) :
      StackReturns declarations registry world (.push (.armed action) tail) input output
  | running (scope : ScopeBound registry action.scope ticket)
      (callback : Derives declarations environment world .none action.action (.function captures (.storage []) (.storage [])))
      (saved : Derives declarations savedEnvironment world savedTicket value input)
      (rest : StackReturns declarations registry world tail input output) :
      StackReturns declarations registry world (.push (.running action value closed) tail) (.storage []) output
  | closing (scope : ScopeBound registry caller ticket)
      (rest : StackReturns declarations registry world tail (.storage []) output) :
      StackReturns declarations registry world (.push (.closing identity caller) tail) (.storage []) output
  | retiring (rest : StackReturns declarations registry world tail (.storage []) output) :
      StackReturns declarations registry world (.push (.retiring owner) tail) (.storage []) output
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
  | armed scope callback rest ih => exact .armed scope callback (ih tail)
  | running scope callback saved rest ih => exact .running scope callback saved (ih tail)
  | closing scope rest ih => exact .closing scope (ih tail)
  | retiring rest ih => exact .retiring (ih tail)
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
      | armed scope callback next =>
          obtain ⟨middle, inside, outside⟩ := ih next
          exact ⟨middle, .armed scope callback inside, outside⟩
      | running scope callback saved next =>
          obtain ⟨middle, inside, outside⟩ := ih next
          exact ⟨middle, .running scope callback saved inside, outside⟩
      | closing scope next =>
          obtain ⟨middle, inside, outside⟩ := ih next
          exact ⟨middle, .closing scope inside, outside⟩
      | retiring next =>
          obtain ⟨middle, inside, outside⟩ := ih next
          exact ⟨middle, .retiring inside, outside⟩
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
  | armed scope callback rest ih => exact .armed (scope_extends scope extended) callback ih
  | running scope callback saved rest ih => exact .running (scope_extends scope extended) callback saved ih
  | closing scope rest ih => exact .closing (scope_extends scope extended) ih
  | retiring rest ih => exact .retiring ih
  | live known scope saved rest ihSaved ihRest => exact .live (extended _ _ known) (scope_extends scope extended) ihSaved ihRest
  | spent known scope rest ih => exact .spent (extended _ _ known) (scope_extends scope extended) ih

theorem stack_world_mono (checked : StackReturns declarations registry world stack input output)
    (included : world ⊆ larger) : StackReturns declarations registry larger stack input output := by
  induction checked with
  | nil => exact .nil
  | plain scope context rest ih => exact .plain scope (context_world_mono context included) ih
  | cell scope absent rest ih => exact .cell scope absent ih
  | handler scope clauses rest ih => exact .handler scope (clauses_world_mono clauses included) ih
  | armed scope callback rest ih => exact .armed scope (CompletionContracts.world_mono callback larger included) ih
  | running scope callback saved rest ih =>
      exact .running scope (CompletionContracts.world_mono callback larger included)
        (CompletionContracts.world_mono saved larger included) ih
  | closing scope rest ih => exact .closing scope ih
  | retiring rest ih => exact .retiring ih
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
      | armed scope callback next =>
          obtain ⟨environment, ticket, answer, savedScope, clauses, inside, outside⟩ := ih next
          exact ⟨environment, ticket, answer, savedScope, clauses, .armed scope callback inside, outside⟩
      | running scope callback saved next =>
          obtain ⟨environment, ticket, answer, savedScope, clauses, inside, outside⟩ := ih next
          exact ⟨environment, ticket, answer, savedScope, clauses, .running scope callback saved inside, outside⟩
      | closing scope next =>
          obtain ⟨environment, ticket, answer, savedScope, clauses, inside, outside⟩ := ih next
          exact ⟨environment, ticket, answer, savedScope, clauses, .closing scope inside, outside⟩
      | retiring next =>
          obtain ⟨environment, ticket, answer, savedScope, clauses, inside, outside⟩ := ih next
          exact ⟨environment, ticket, answer, savedScope, clauses, .retiring inside, outside⟩
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
    CompletionContracts.beta_result code argumentClosed, stack⟩

theorem bind_step
    (checked : ConfigurationReturns declarations registry world ⟨.bind name value body, scope, tail⟩ output)
    (closed : ClosedValue value) (ready : ClosedExcept name body) :
    RawStep ⟨.bind name value body, scope, tail⟩ ⟨body.subst name value, scope, tail⟩ [] [] ∧
    ConfigurationReturns declarations registry world ⟨body.subst name value, scope, tail⟩ output := by
  obtain ⟨environment, ticket, input, scopeChecked, code, stack⟩ := checked
  exact ⟨.bind _ _ _ _ _ closed ready, environment, ticket, input, scopeChecked,
    CompletionContracts.bind_result code closed, stack⟩

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
        fun member => absent (CompletionContracts.value_support code closed.1 member),
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
    CompletionContracts.substitution bodyChecked (typed_value_storage_contract typed isValue input) closed⟩

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
      exact congrArg CallableContracts.Contract.storage (Option.some.inj (output.symm.trans finite))

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
      have recorded : insert registry owner record owner = some record := by simp [CallableFrames.insert]
      obtain ⟨savedTyped, outsideTyped, handlerTyped⟩ := ScopedPorts.handler_cut_retains_typing cut stackTyped
      cases handlerTyped with
      | handler caller clausesTyped coverage unique =>
          obtain ⟨clauseInput, clauseOutput, clauseKnown, bodyTyped⟩ := ScopedPorts.selected_clause_typed selected clausesTyped
          exact ⟨.capture requested operation parameter binder owner operand body scope whole capture tail handler
              (ScopedPorts.embedPort _) cut selected closed (ScopedPorts.typed_suffix_ready bodyTyped),
            record, resumeBound, rfl, outputFinite, extended, savedEnvironment, _, answerContract, .bound recorded,
            substituted, .live recorded (scope_extends savedScope extended)
              (stack_registry_extends saved extended) (stack_registry_extends outside extended)⟩


theorem cleanup_entry_step
    (checked : ConfigurationReturns declarations registry world ⟨.cleanup action.action body, action.scope, tail⟩ output) :
    RawStep ⟨.cleanup action.action body, action.scope, tail⟩
      ⟨body, action.scope, .push (.armed action) tail⟩ [.cleanup action.identity] [] ∧
    ConfigurationReturns declarations registry world ⟨body, action.scope, .push (.armed action) tail⟩ output := by
  obtain ⟨environment, ticket, input, scopeChecked, code, stack⟩ := checked
  obtain ⟨captures, callback, bodyChecked⟩ := CompletionContracts.cleanup_contract code
  exact ⟨.enterCleanup action body tail, environment, ticket, input, scopeChecked, bodyChecked,
    .armed scopeChecked (CompletionContracts.value_ticket_transport callback action.closed.1 .none) stack⟩

theorem cleanup_start_step
    (checked : ConfigurationReturns declarations registry world ⟨value, scope, .push (.armed action) tail⟩ output)
    (closed : ClosedValue value) :
    RawStep ⟨value, scope, .push (.armed action) tail⟩
      ⟨.app action.action .unit, .none, .push (.running action value closed) tail⟩ [] [] ∧
    ConfigurationReturns declarations registry world
      ⟨.app action.action .unit, .none, .push (.running action value closed) tail⟩ output := by
  obtain ⟨environment, ticket, input, scopeChecked, code, stack⟩ := checked
  cases stack with
  | armed savedScope callback rest =>
      exact ⟨.startCleanup action value closed scope tail, _, .none, .storage [], .none,
        .app callback (.leaf trivial rfl .nil), .running savedScope callback code rest⟩

theorem cleanup_finish_step
    (checked : ConfigurationReturns declarations registry world ⟨.unit, scope, .push (.running action value closed) tail⟩ output) :
    RawStep ⟨.unit, scope, .push (.running action value closed) tail⟩
      ⟨value, action.scope, tail⟩ [] [.cleanup action.identity] ∧
    ConfigurationReturns declarations registry world ⟨value, action.scope, tail⟩ output := by
  obtain ⟨environment, ticket, input, scopeChecked, code, stack⟩ := checked
  cases stack with
  | running savedScope callback saved rest =>
      exact ⟨.finishCleanup action value closed scope tail, environment, _, _, savedScope, returned_value_rebind saved closed, rest⟩

theorem closing_finish_step
    (checked : ConfigurationReturns declarations registry world ⟨.unit, scope, .push (.closing identity caller) tail⟩ output) :
    RawStep ⟨.unit, scope, .push (.closing identity caller) tail⟩ ⟨.unit, caller, tail⟩ [] [.close identity] ∧
    ConfigurationReturns declarations registry world ⟨.unit, caller, tail⟩ output := by
  obtain ⟨environment, ticket, input, scopeChecked, code, stack⟩ := checked
  cases stack with
  | closing savedScope rest =>
      exact ⟨.finishClose identity scope caller tail, environment, _, _, savedScope, .leaf trivial rfl .nil, rest⟩

theorem retiring_step
    (checked : ConfigurationReturns declarations registry world ⟨.unit, scope, .push (.retiring owner) tail⟩ output) :
    RawStep ⟨.unit, scope, .push (.retiring owner) tail⟩ ⟨.unit, scope, tail⟩ [] [.ticket owner] ∧
    ConfigurationReturns declarations registry world ⟨.unit, scope, tail⟩ output := by
  obtain ⟨environment, ticket, input, scopeChecked, code, stack⟩ := checked
  cases stack with
  | retiring rest => exact ⟨.retire owner scope tail, environment, ticket, _, scopeChecked, code, rest⟩

inductive PlanReturns (declarations : DeclarationRegistry) (world : List Nat) : List CloseEntry → Prop where
  | nil : PlanReturns declarations world []
  | release (rest : PlanReturns declarations world entries) : PlanReturns declarations world (.release identity payload :: entries)
  | invoke (callback : Derives declarations environment world .none action.action (.function captures (.storage []) (.storage [])))
      (rest : PlanReturns declarations world entries) : PlanReturns declarations world (.invoke action :: entries)
  | retire (rest : PlanReturns declarations world entries) : PlanReturns declarations world (.retire owner :: entries)

theorem plan_append (first : PlanReturns declarations world left) (second : PlanReturns declarations world right) :
    PlanReturns declarations world (left ++ right) := by
  induction first with
  | nil => exact second
  | release rest ih => exact .release ih
  | invoke callback rest ih => exact .invoke callback ih
  | retire rest ih => exact .retire ih

theorem make_plan_returns
    (checked : StackReturns declarations registry world stack input output) (built : makePlan stack = some plan) :
    PlanReturns declarations world plan := by
  induction stack generalizing input output plan with
  | nil => cases Option.some.inj built; exact .nil
  | push frame tail ih =>
      cases frame with
      | plain plain => cases checked with
          | plain scope context rest => exact ih rest built
      | handler handler => cases checked with
          | handler scope clauses rest => exact ih rest built
      | cell identity payload caller answer => cases checked with
          | cell scope absent rest =>
              cases h : makePlan tail with
              | none => simp [makePlan, h] at built
              | some entries =>
                  have same : .release identity payload :: entries = plan := by simpa [makePlan, h] using built
                  subst plan
                  exact .release (ih rest h)
      | armed action => cases checked with
          | armed scope callback rest =>
              cases h : makePlan tail with
              | none => simp [makePlan, h] at built
              | some entries =>
                  have same : .invoke action :: entries = plan := by simpa [makePlan, h] using built
                  subst plan
                  exact .invoke callback (ih rest h)
      | running | unwinding | closing | retiring => simp [makePlan] at built
  | live owner operationInput answer capture caller tail ihSaved ihRest => cases checked with
      | live known scope saved rest =>
          cases hs : makePlan capture with
          | none => simp [makePlan, hs] at built
          | some inside => cases ht : makePlan tail with
              | none => simp [makePlan, hs, ht] at built
              | some outside =>
                  have same : inside ++ .retire owner :: outside = plan := by simpa [makePlan, hs, ht] using built
                  subst plan
                  exact plan_append (ihSaved saved hs) (.retire (ihRest rest ht))
  | spent owner answer caller tail ih => cases checked with
      | spent known scope rest => exact ih rest built

theorem close_control_returns (checked : PlanReturns declarations world plan)
    (scopeChecked : ScopeBound registry scope ticket) :
    StackReturns declarations registry world (closeControl scope plan) (.storage []) (.storage []) := by
  induction checked with
  | nil => exact .nil
  | release rest ih => exact .cell scopeChecked (by simp [CallableContracts.Contract.storageOf]) ih
  | invoke callback rest ih => exact .armed scopeChecked callback ih
  | retire rest ih => exact .retiring ih

theorem discard_step (resolved : scope.resolve binder = some owner)
    (built : makePlan capture = some plan)
    (checked : ConfigurationReturns declarations registry world
      ⟨.discard binder, scope, front.append (.live owner operationInput answer capture caller tail)⟩ output) :
    let after : Configuration := ⟨.unit, scope, (closeControl scope plan).append
      (.push (.closing closeId scope) (front.append (.spent owner answer caller tail)))⟩
    RawStep ⟨.discard binder, scope, front.append (.live owner operationInput answer capture caller tail)⟩
      after [.close closeId] [.ticket owner] ∧
    ConfigurationReturns declarations registry world after output := by
  obtain ⟨environment, ticket, input, scopeChecked, code, stack⟩ := checked
  obtain ⟨rfl, operationContract, answerContract, rfl⟩ := CompletionContracts.discard_contract code
  have known := scope_resolves scopeChecked resolved
  obtain ⟨middle, inside, boundary⟩ := stack_decompose stack
  cases boundary with
  | live actual savedScope saved rest =>
      have same := Option.some.inj (actual.symm.trans known)
      subst_vars
      have planChecked := make_plan_returns saved built
      exact ⟨.discard binder owner closeId scope caller operationInput answer front capture tail plan resolved built,
        environment, _, .storage [], scopeChecked, .leaf trivial rfl .nil,
        stack_append (close_control_returns planChecked scopeChecked)
          (.closing scopeChecked (stack_append inside (.spent actual savedScope rest)))⟩

theorem callable_context_included
    (checked : CallableFrames.ContextReturns declarations environment world ticket position input output) :
    ContextReturns declarations environment world ticket position input output := by
  cases checked with
  | pairLeft right => exact .pairLeft (CompletionContracts.callable_derivation_included right)
  | pairRight left => exact .pairRight (CompletionContracts.callable_derivation_included left)
  | appFunction argument => exact .appFunction (CompletionContracts.callable_derivation_included argument)
  | appArgument function => exact .appArgument (CompletionContracts.callable_derivation_included function)
  | bind body => exact .bind (CompletionContracts.callable_derivation_included body)
  | branch yes no => exact .branch (CompletionContracts.callable_derivation_included yes) (CompletionContracts.callable_derivation_included no)
  | perform known finite => exact .perform known finite
  | resource closed body outward =>
      exact .resource closed (fun identity fresh => CompletionContracts.callable_derivation_included (body identity fresh)) outward
  | resume => exact .resume

theorem callable_stack_included
    (checked : CallableFrames.StackReturns declarations registry world stack input output) :
    StackReturns declarations registry world stack input output := by
  induction checked with
  | nil => exact .nil
  | plain scope context rest ih => exact .plain scope (callable_context_included context) ih
  | cell scope absent rest ih => exact .cell scope absent ih
  | handler scope clauses rest ih => exact .handler scope (CompletionContracts.callable_clauses_included clauses) ih
  | live known scope saved rest ihSaved ihRest => exact .live known scope ihSaved ihRest
  | spent known scope rest ih => exact .spent known scope ih

theorem callable_configuration_included
    (checked : CallableFrames.ConfigurationReturns declarations registry world configuration output) :
    ConfigurationReturns declarations registry world configuration output := by
  obtain ⟨environment, ticket, input, scope, code, stack⟩ := checked
  exact ⟨environment, ticket, input, scope, CompletionContracts.callable_derivation_included code, callable_stack_included stack⟩

namespace DisposalExample
open CallableContracts.Examples (identity identityContract scalar)
open GenerativeFrames.Examples (declarations)
open CallableFrames.Examples (handler pendingFunction functionType)
open CompletionContracts.Examples (callback)

def action : ActionData := ⟨7, callback, ⟨trivial, rfl, by intro dependency member; cases member⟩, .none, functionType, []⟩
def captured : Stack := .push (.plain pendingFunction)
  (.push (.armed action) (.push (.cell 42 0 .none functionType) (.push (.handler handler) .nil)))
def record : ResultRecord := ⟨scalar, identityContract⟩
def registry : Registry := insert (fun _ => none) 5 record
def suffix : PlainData := ⟨.bind 4 identity, .ticket 10 5, .unit, functionType, [], rfl⟩
def before : Configuration := ⟨.discard 10, .ticket 10 5,
  (Stack.push (.plain suffix) .nil).append (.live 5 .integer functionType captured .none .nil)⟩
def plan : List CloseEntry := [.invoke action, .release 42 0]
def closingAction : ActionData := { action with scope := .ticket 10 5, answer := .unit }
def spent : Stack := .spent 5 functionType .none .nil
def remaining : Stack := .push (.cell 42 0 (.ticket 10 5) .unit)
  (.push (.closing 31 (.ticket 10 5)) (.push (.plain suffix) spent))
def after : Configuration := ⟨.unit, .ticket 10 5, .push (.armed closingAction) remaining⟩
def final : Configuration := ⟨identity, .none, .nil⟩

theorem captured_results : StackReturns declarations registry [42] captured scalar identityContract := by
  have identityChecked (environment : CompletionContracts.Environment) (ticket : Ticket) : Derives declarations environment [42] ticket identity identityContract :=
    .lambda (.variable rfl) .nil
  have callbackChecked (environment : CompletionContracts.Environment) : Derives declarations environment [42] .none callback (.function [] scalar scalar) :=
    .lambda (.leaf trivial rfl .nil) .nil
  have clauses := CompletionContracts.callable_clauses_included CallableFrames.Examples.clauses_contract
  have larger := clauses_world_mono clauses (show ([] : List Nat) ⊆ [42] from List.nil_subset _)
  exact .plain (environment := CallableContracts.Environment.empty) .none (.bind (identityChecked _ _))
    (.armed .none (callbackChecked CallableContracts.Environment.empty) (.cell .none (by simp [identityContract, CallableContracts.Contract.storageOf])
      (.handler .none larger .nil)))

theorem initial_results : ConfigurationReturns declarations registry [42] before identityContract := by
  have known : registry 5 = some record := by simp [registry, CallableFrames.insert]
  refine ⟨CallableContracts.Environment.empty, .bound 10 scalar identityContract, scalar, .bound known, .discard, ?_⟩
  exact .plain (environment := CallableContracts.Environment.empty) (.bound known) (.bind (.lambda (.variable rfl) .nil)) (.live known .none captured_results .nil)

theorem actual_plan : makePlan captured = some plan := rfl

theorem disposal_execution : RawTrace before final [.close 31] [.close 31, .resource 42, .cleanup 7, .ticket 5] ∧
    ConfigurationReturns declarations registry [42] final identityContract := by
  obtain ⟨e0, c1⟩ := discard_step (closeId := 31) rfl actual_plan initial_results
  change ConfigurationReturns declarations registry [42] after identityContract at c1
  obtain ⟨e1, c2⟩ := cleanup_start_step c1 (show ClosedValue .unit from ⟨trivial, rfl, by intro dependency member; cases member⟩)
  obtain ⟨e2, c3⟩ := beta_step c2
    (show ClosedValue .unit from ⟨trivial, rfl, by intro dependency member; cases member⟩) closingAction.closed
  obtain ⟨e3, c4⟩ := cleanup_finish_step c3
  obtain ⟨e4, absent, c5⟩ := cell_return_step c4
    (show ClosedValue .unit from ⟨trivial, rfl, by intro dependency member; cases member⟩)
  obtain ⟨e5, c6⟩ := closing_finish_step c5
  obtain ⟨e6, c7⟩ := plug_step c6 (show ClosedValue .unit from ⟨trivial, rfl, by intro dependency member; cases member⟩)
  obtain ⟨e7, c8⟩ := bind_step c7
    (show ClosedValue .unit from ⟨trivial, rfl, by intro dependency member; cases member⟩)
    (by intro name member; cases member)
  obtain ⟨e8, c9⟩ := clause_return_step c8
    (show ClosedValue identity from ⟨trivial, rfl, by intro dependency member; cases member⟩)
  constructor
  · simpa [before, final, identity, Code.subst, closingAction, action] using
      (RawTrace.next e0 (.next e1 (.next e2 (.next e3 (.next e4 (.next e5 (.next e6 (.next e7 (.next e8 (.refl _))))))))))
  · simpa [final, identity, Code.subst] using c9

theorem running_cleanup_cannot_be_planned (tail : Stack) :
    makePlan (.push (.running action .unit ⟨trivial, rfl, by intro dependency member; cases member⟩) tail) = none := by
  simp [makePlan]

end DisposalExample

end Ash.OneShot.CompletionFrames

#print axioms Ash.OneShot.CompletionFrames.clauses_world_mono
#print axioms Ash.OneShot.CompletionFrames.context_plug
#print axioms Ash.OneShot.CompletionFrames.returned_value_rebind
#print axioms Ash.OneShot.CompletionFrames.context_world_mono
#print axioms Ash.OneShot.CompletionFrames.focus_decompose
#print axioms Ash.OneShot.CompletionFrames.stack_append
#print axioms Ash.OneShot.CompletionFrames.stack_decompose
#print axioms Ash.OneShot.CompletionFrames.stack_registry_extends
#print axioms Ash.OneShot.CompletionFrames.stack_world_mono
#print axioms Ash.OneShot.CompletionFrames.handler_cut_certificate
#print axioms Ash.OneShot.CompletionFrames.resume_recomposition
#print axioms Ash.OneShot.CompletionFrames.focus_step
#print axioms Ash.OneShot.CompletionFrames.plug_step
#print axioms Ash.OneShot.CompletionFrames.beta_step
#print axioms Ash.OneShot.CompletionFrames.bind_step
#print axioms Ash.OneShot.CompletionFrames.resume_step
#print axioms Ash.OneShot.CompletionFrames.handler_entry_step
#print axioms Ash.OneShot.CompletionFrames.handler_return_step
#print axioms Ash.OneShot.CompletionFrames.clause_return_step
#print axioms Ash.OneShot.CompletionFrames.resource_step
#print axioms Ash.OneShot.CompletionFrames.cell_return_step
#print axioms Ash.OneShot.CompletionFrames.selected_clause
#print axioms Ash.OneShot.CompletionFrames.typed_value_storage_contract
#print axioms Ash.OneShot.CompletionFrames.selected_clause_substitution
#print axioms Ash.OneShot.CompletionFrames.declared_output_contract
#print axioms Ash.OneShot.CompletionFrames.capture_step
#print axioms Ash.OneShot.CompletionFrames.cleanup_entry_step
#print axioms Ash.OneShot.CompletionFrames.cleanup_start_step
#print axioms Ash.OneShot.CompletionFrames.cleanup_finish_step
#print axioms Ash.OneShot.CompletionFrames.closing_finish_step
#print axioms Ash.OneShot.CompletionFrames.retiring_step
#print axioms Ash.OneShot.CompletionFrames.plan_append
#print axioms Ash.OneShot.CompletionFrames.make_plan_returns
#print axioms Ash.OneShot.CompletionFrames.close_control_returns
#print axioms Ash.OneShot.CompletionFrames.discard_step

#print axioms Ash.OneShot.CompletionFrames.callable_context_included
#print axioms Ash.OneShot.CompletionFrames.callable_stack_included
#print axioms Ash.OneShot.CompletionFrames.callable_configuration_included

#print axioms Ash.OneShot.CompletionFrames.DisposalExample.captured_results
#print axioms Ash.OneShot.CompletionFrames.DisposalExample.initial_results
#print axioms Ash.OneShot.CompletionFrames.DisposalExample.actual_plan
#print axioms Ash.OneShot.CompletionFrames.DisposalExample.disposal_execution
#print axioms Ash.OneShot.CompletionFrames.DisposalExample.running_cleanup_cannot_be_planned
