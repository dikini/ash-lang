import ClauseResults

/-!
Retained lexical result contracts for the existing one-shot machine. A result
record is historical metadata, not permission to resume. Synchronization with
the joint type/usage registry and cleanup frames remains a separate obligation.
-/

namespace Ash.OneShot.ClauseFrames
open Instantiation ScopedExpressions ScopedExecution
open ClauseResults (Derives TicketBound HandlerResults)
open ResultSummaries (extendAnalysis)
open GenerativeResults (summary)

structure ResultRecord where
  input : List Nat
  answer : List Nat
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
  · subst candidate
    rw [fresh] at known
    contradiction
  · simp [insert, same, known]

inductive ScopeBound (registry : Registry) : Scope → TicketBound → Prop where
  | none : ScopeBound registry .none .none
  | bound (known : registry owner = some record) :
      ScopeBound registry (.ticket binder owner) (.bound binder record.input record.answer)

theorem scope_extends (checked : ScopeBound before scope ticket)
    (extended : RegistryExtends before after) : ScopeBound after scope ticket := by
  cases checked with
  | none => exact .none
  | bound known => exact .bound (extended _ _ known)

theorem scope_resolves (checked : ScopeBound registry scope (.bound binder input answer))
    (resolved : scope.resolve binder = some owner) :
    registry owner = some ⟨input, answer⟩ := by
  cases checked with
  | bound known =>
      simp only [Execution.Scope.resolve, ↓reduceIte] at resolved
      cases Option.some.inj resolved
      exact known

inductive ContextReturns (declarations : DeclarationRegistry) (environment : ResultSummaries.Environment)
    (world : List Nat) (ticket : TicketBound) : Context → List Nat → List Nat → Prop where
  | pairLeft (rightChecked : Derives declarations environment world ticket right rightBound) :
      ContextReturns declarations environment world ticket (.pairLeft right) leftBound (leftBound ++ rightBound)
  | pairRight (leftChecked : Derives declarations environment world ticket left leftBound) :
      ContextReturns declarations environment world ticket (.pairRight left) rightBound (leftBound ++ rightBound)
  | bind (bodyChecked : Derives declarations (extendAnalysis environment name (summary input)) world ticket body output) :
      ContextReturns declarations environment world ticket (.bind name body) input output
  | branch (yesChecked : Derives declarations environment world ticket yes bound)
      (noChecked : Derives declarations environment world ticket no bound) :
      ContextReturns declarations environment world ticket (.branch yes no) conditionBound bound
  | perform (closed : (Code.perform effect operation .unit).ResourceClosed)
      (checked : DeclarationTemplates.check declarations environment bound (.perform effect operation .unit) = true) :
      ContextReturns declarations environment world ticket (.perform effect operation) operandBound bound
  | resource (closed : (Code.resource binder .unit body).ResourceClosed)
      (bodyChecked : ∀ identity, identity ∉ world → Derives declarations environment (world ++ [identity]) ticket
        (body.instantiate (Environment.empty.bind binder identity)) bound)
      (outward : bound ⊆ world) :
      ContextReturns declarations environment world ticket (.resource binder body) initializerBound bound
  | resume (same : ticket = .bound binder input answer) :
      ContextReturns declarations environment world ticket (.resume binder) input answer

theorem context_embeds
    (checked : GenerativeFrames.ContextReturns declarations environment world position input output) :
    ContextReturns declarations environment world ticket position input output := by
  cases checked with
  | pairLeft right => exact .pairLeft (.existing right)
  | pairRight left => exact .pairRight (.existing left)
  | bind body => exact .bind (.existing body)
  | branch yes no => exact .branch (.existing yes) (.existing no)
  | perform closed finite => exact .perform closed finite
  | resource closed body outward => exact .resource closed (fun id fresh => .existing (body id fresh)) outward

theorem context_plug (context : ContextReturns declarations environment world ticket position input output)
    (child : Derives declarations environment world ticket code input) :
    Derives declarations environment world ticket (position.plug code) output := by
  cases context with
  | pairLeft right => exact .pair child right
  | pairRight left => exact .pair left child
  | bind body => exact .bind child body
  | branch yes no => exact .branch child yes no
  | perform closed finite =>
      exact .perform child (GenerativeFrames.plug_resource_closed (.perform _ _) closed (ClauseResults.resource_closed child)) finite
  | resource closed body outward =>
      exact .resource child (GenerativeFrames.plug_resource_closed (.resource _ _) closed (ClauseResults.resource_closed child)) body outward
  | resume same => subst ticket; exact .resume child

theorem returned_value_rebind
    (checked : Derives declarations environment world ticket value input)
    (closed : ClosedValue value) (included : input ⊆ expected) :
    Derives declarations savedEnvironment savedWorld savedTicket value expected :=
  .existing (.leaf (Or.inl closed.1) closed.2.1
    (GenerativeFrames.closed_value_check closed ((ClauseResults.value_support checked closed).trans included)))

theorem context_plug_returned_value
    (context : ContextReturns declarations savedEnvironment world savedTicket position expected output)
    (child : Derives declarations environment currentWorld ticket value input)
    (closed : ClosedValue value) (included : input ⊆ expected) :
    Derives declarations savedEnvironment world savedTicket (position.plug value) output :=
  context_plug context (returned_value_rebind child closed included)

theorem context_world_mono
    (context : ContextReturns declarations environment world ticket position input output)
    (included : world ⊆ larger) : ContextReturns declarations environment larger ticket position input output := by
  cases context with
  | pairLeft right => exact .pairLeft (ClauseResults.world_mono right included)
  | pairRight left => exact .pairRight (ClauseResults.world_mono left included)
  | bind body => exact .bind (ClauseResults.world_mono body included)
  | branch yes no => exact .branch (ClauseResults.world_mono yes included) (ClauseResults.world_mono no included)
  | perform closed finite => exact .perform closed finite
  | resource closed body outward =>
      exact .resource closed (fun identity fresh => ClauseResults.world_mono
        (body identity (fun member => fresh (included member)))
        (ScopedExpressions.append_subset included (List.Subset.refl _))) (outward.trans included)
  | resume same => exact .resume same

theorem focus_decompose (checked : Derives declarations environment world ticket whole output)
    (focus : Focus whole child position) :
    ∃ input, Derives declarations environment world ticket child input ∧
      ContextReturns declarations environment world ticket position input output := by
  cases checked with
  | existing checked =>
      obtain ⟨input, child, context⟩ := GenerativeFrames.focus_decompose checked focus
      exact ⟨input, .existing child, context_embeds context⟩
  | pair left right => cases focus with
      | pairLeft => exact ⟨_, left, .pairLeft right⟩
      | pairRight => exact ⟨_, right, .pairRight left⟩
  | bind initializer body => cases focus with
      | bind => exact ⟨_, initializer, .bind body⟩
  | branch condition yes no => cases focus with
      | branch => exact ⟨_, condition, .branch yes no⟩
  | perform operand closed finite => cases focus with
      | perform =>
          refine ⟨_, operand, .perform ?_ finite⟩
          simpa only [Code.ResourceClosed, Code.freeNames, List.append_nil] using (List.append_eq_nil_iff.mp closed).1
  | resource initializer closed body outward => cases focus with
      | resource => exact ⟨_, initializer, .resource (List.append_eq_nil_iff.mp closed).2 body outward⟩
  | resume operand => cases focus with
      | resume => exact ⟨_, operand, .resume rfl⟩
  | handle => cases focus

/-- Incoming support may be smaller than a frame's saved expectation. Saved
    environments and historical answer bounds remain fixed under that change. -/
inductive StackReturns (declarations : DeclarationRegistry) (registry : Registry) (world : List Nat) :
    Stack → List Nat → List Nat → Prop where
  | nil (included : input ⊆ output) : StackReturns declarations registry world .nil input output
  | plain (scope : ScopeBound registry plain.scope ticket)
      (context : ContextReturns declarations environment world ticket plain.context expected middle)
      (included : input ⊆ expected) (rest : StackReturns declarations registry world tail middle output) :
      StackReturns declarations registry world (.push (.plain plain) tail) input output
  | cell (scope : ScopeBound registry caller ticket) (absent : identity ∉ input)
      (rest : StackReturns declarations registry world tail input output) :
      StackReturns declarations registry world (.push (.cell identity payload caller answer) tail) input output
  | handler (scope : ScopeBound registry handler.scope ticket)
      (clauses : HandlerResults declarations environment world handler answerBound)
      (included : input ⊆ answerBound) (rest : StackReturns declarations registry world tail answerBound output) :
      StackReturns declarations registry world (.push (.handler handler) tail) input output
  | live (known : registry owner = some record) (scope : ScopeBound registry caller ticket)
      (saved : StackReturns declarations registry world capture record.input record.answer)
      (included : input ⊆ record.answer) (rest : StackReturns declarations registry world tail record.answer output) :
      StackReturns declarations registry world (.live owner operationInput answer capture caller tail) input output
  | spent (known : registry owner = some record) (scope : ScopeBound registry caller ticket)
      (included : input ⊆ record.answer) (rest : StackReturns declarations registry world tail record.answer output) :
      StackReturns declarations registry world (.spent owner answer caller tail) input output

variable {front capture tail : Stack}

theorem stack_input_weaken (checked : StackReturns declarations registry world stack input output)
    (included : smaller ⊆ input) : StackReturns declarations registry world stack smaller output := by
  induction checked generalizing smaller with
  | nil next => exact .nil (included.trans next)
  | plain scope context next rest ih => exact .plain scope context (included.trans next) rest
  | cell scope absent rest ih => exact .cell scope (fun member => absent (included member)) (ih included)
  | handler scope clauses next rest ih => exact .handler scope clauses (included.trans next) rest
  | live known scope saved next rest ihSaved ihRest => exact .live known scope saved (included.trans next) rest
  | spent known scope next rest ih => exact .spent known scope (included.trans next) rest

theorem stack_append (front : StackReturns declarations registry world left input middle)
    (tail : StackReturns declarations registry world right middle output) :
    StackReturns declarations registry world (left.append right) input output := by
  induction front with
  | nil included => exact stack_input_weaken tail included
  | plain scope context included rest ih => exact .plain scope context included (ih tail)
  | cell scope absent rest ih => exact .cell scope absent (ih tail)
  | handler scope clauses included rest ih => exact .handler scope clauses included (ih tail)
  | live known scope saved included rest ihSaved ihRest => exact .live known scope saved included (ihRest tail)
  | spent known scope included rest ih => exact .spent known scope included (ih tail)

theorem stack_decompose
    (checked : StackReturns declarations registry world (front.append tail) input output) :
    ∃ middle, StackReturns declarations registry world front input middle ∧
      StackReturns declarations registry world tail middle output := by
  induction front generalizing input output with
  | nil => exact ⟨input, .nil (List.Subset.refl _), checked⟩
  | push frame rest ih => cases checked with
      | plain scope context included next =>
          obtain ⟨middle, inside, outside⟩ := ih next
          exact ⟨middle, .plain scope context included inside, outside⟩
      | cell scope absent next =>
          obtain ⟨middle, inside, outside⟩ := ih next
          exact ⟨middle, .cell scope absent inside, outside⟩
      | handler scope clauses included next =>
          obtain ⟨middle, inside, outside⟩ := ih next
          exact ⟨middle, .handler scope clauses included inside, outside⟩
  | live owner operationInput answer saved scope rest ihSaved ihRest => cases checked with
      | live known scope saved included next =>
          obtain ⟨middle, inside, outside⟩ := ihRest next
          exact ⟨middle, .live known scope saved included inside, outside⟩
  | spent owner answer scope rest ih => cases checked with
      | spent known scope included next =>
          obtain ⟨middle, inside, outside⟩ := ih next
          exact ⟨middle, .spent known scope included inside, outside⟩

theorem stack_registry_extends (checked : StackReturns declarations registry world stack input output)
    (extended : RegistryExtends registry larger) : StackReturns declarations larger world stack input output := by
  induction checked with
  | nil included => exact .nil included
  | plain scope context included rest ih => exact .plain (scope_extends scope extended) context included ih
  | cell scope absent rest ih => exact .cell (scope_extends scope extended) absent ih
  | handler scope clauses included rest ih => exact .handler (scope_extends scope extended) clauses included ih
  | live known scope saved included rest ihSaved ihRest =>
      exact .live (extended _ _ known) (scope_extends scope extended) ihSaved included ihRest
  | spent known scope included rest ih => exact .spent (extended _ _ known) (scope_extends scope extended) included ih

theorem stack_world_mono (checked : StackReturns declarations registry world stack input output)
    (included : world ⊆ larger) : StackReturns declarations registry larger stack input output := by
  induction checked with
  | nil next => exact .nil next
  | plain scope context next rest ih => exact .plain scope (context_world_mono context included) next ih
  | cell scope absent rest ih => exact .cell scope absent ih
  | handler scope clauses next rest ih => exact .handler scope (ClauseResults.clauses_world_mono clauses included) next ih
  | live known scope saved next rest ihSaved ihRest => exact .live known scope ihSaved next ihRest
  | spent known scope next rest ih => exact .spent known scope next ih

theorem handler_cut_certificate (cut : HandlerCut requested whole capture tail handler)
    (checked : StackReturns declarations registry world whole input output) :
    ∃ environment ticket answer,
      ScopeBound registry handler.scope ticket ∧ HandlerResults declarations environment world handler answer ∧
      StackReturns declarations registry world capture input answer ∧
      StackReturns declarations registry world tail answer output := by
  induction cut generalizing input output with
  | hit handler tail same => cases checked with
      | handler scope clauses included rest =>
          exact ⟨_, _, _, scope, clauses, .handler scope clauses included (.nil (List.Subset.refl _)), rest⟩
  | push frame rest capture tail handler miss next ih => cases checked with
      | plain scope context included next =>
          obtain ⟨environment, ticket, answer, savedScope, clauses, inside, outside⟩ := ih next
          exact ⟨environment, ticket, answer, savedScope, clauses, .plain scope context included inside, outside⟩
      | cell scope absent next =>
          obtain ⟨environment, ticket, answer, savedScope, clauses, inside, outside⟩ := ih next
          exact ⟨environment, ticket, answer, savedScope, clauses, .cell scope absent inside, outside⟩
      | handler scope clauses included next =>
          obtain ⟨environment, ticket, answer, savedScope, savedClauses, inside, outside⟩ := ih next
          exact ⟨environment, ticket, answer, savedScope, savedClauses, .handler scope clauses included inside, outside⟩
  | live owner operationInput answer saved scope rest capture tail handler next ih => cases checked with
      | live known scope saved included next =>
          obtain ⟨environment, ticket, answer, savedScope, clauses, inside, outside⟩ := ih next
          exact ⟨environment, ticket, answer, savedScope, clauses, .live known scope saved included inside, outside⟩
  | spent owner answer scope rest capture tail handler next ih => cases checked with
      | spent known scope included next =>
          obtain ⟨environment, ticket, answer, savedScope, clauses, inside, outside⟩ := ih next
          exact ⟨environment, ticket, answer, savedScope, clauses, .spent known scope included inside, outside⟩

/-- The shared historical record determines the saved output and the current
    prefix input. No separate equality between those interfaces is assumed. -/
theorem resume_recomposition
    (known : registry owner = some record)
    (checked : StackReturns declarations registry world
      (front.append (.live owner operationInput answer capture caller tail)) record.answer output) :
    StackReturns declarations registry world
      (capture.append (front.append (.spent owner answer caller tail))) record.input output := by
  obtain ⟨middle, frontChecked, boundary⟩ := stack_decompose checked
  cases boundary with
  | live actual scope saved included rest =>
      have same := Option.some.inj (actual.symm.trans known)
      subst record
      exact stack_append saved (stack_append frontChecked (.spent actual scope included rest))

def ConfigurationReturns (declarations : DeclarationRegistry) (registry : Registry) (world : List Nat)
    (configuration : Configuration) (output : List Nat) : Prop :=
  ∃ environment ticket input, ScopeBound registry configuration.scope ticket ∧
    Derives declarations environment world ticket configuration.expression input ∧
    StackReturns declarations registry world configuration.stack input output

theorem focus_step (focus : Focus whole child plain.context)
    (checked : ConfigurationReturns declarations registry world ⟨whole, plain.scope, tail⟩ output) :
    RawStep ⟨whole, plain.scope, tail⟩ ⟨child, plain.scope, .push (.plain plain) tail⟩ [] [] ∧
    ConfigurationReturns declarations registry world ⟨child, plain.scope, .push (.plain plain) tail⟩ output := by
  obtain ⟨environment, ticket, bound, scope, code, stack⟩ := checked
  obtain ⟨input, childChecked, context⟩ := focus_decompose code focus
  exact ⟨.focus plain focus tail, environment, ticket, input, scope, childChecked,
    .plain scope context (List.Subset.refl _) stack⟩

theorem plug_step
    (checked : ConfigurationReturns declarations registry world ⟨value, scope, .push (.plain plain) tail⟩ output)
    (closed : ClosedValue value) :
    RawStep ⟨value, scope, .push (.plain plain) tail⟩ ⟨plain.context.plug value, plain.scope, tail⟩ [] [] ∧
    ConfigurationReturns declarations registry world ⟨plain.context.plug value, plain.scope, tail⟩ output := by
  obtain ⟨environment, ticket, input, scopeChecked, code, stack⟩ := checked
  cases stack with
  | plain savedScope context included rest =>
      exact ⟨.plug plain value closed scope tail, _, _, _, savedScope,
        context_plug_returned_value context code closed included, rest⟩

theorem resume_step
    (resolved : scope.resolve binder = some owner)
    (checked : ConfigurationReturns declarations registry world
      ⟨.resume binder value, scope, front.append (.live owner operationInput answer capture caller tail)⟩ output)
    (closed : ClosedValue value) :
    RawStep ⟨.resume binder value, scope, front.append (.live owner operationInput answer capture caller tail)⟩
      ⟨value, scope, capture.append (front.append (.spent owner answer caller tail))⟩ [] [.ticket owner] ∧
    ConfigurationReturns declarations registry world
      ⟨value, scope, capture.append (front.append (.spent owner answer caller tail))⟩ output := by
  obtain ⟨environment, ticket, bound, scopeChecked, code, stack⟩ := checked
  obtain ⟨input, rfl, operand⟩ := ClauseResults.resume_inversion code
  have known := scope_resolves scopeChecked resolved
  exact ⟨.resume binder owner scope caller operationInput answer front capture tail value closed resolved,
    environment, _, input, scopeChecked, operand, resume_recomposition known stack⟩

theorem perform_check
    (checked : Derives declarations environment world ticket (.perform effect operation operand) bound) :
    DeclarationTemplates.check declarations environment bound (.perform effect operation operand) = true := by
  cases checked with
  | existing checked => cases checked with
      | leaf shape closed finite =>
          rcases shape with value | ⟨name, same⟩
          · cases value
          · cases same
      | perform operand closed finite => exact finite
  | perform operand closed finite => exact finite

theorem declared_output_included
    (checked : Derives declarations environment world ticket (.perform (freezeEffect effect) operation operand) bound)
    (known : DeclarationResults.signature declarations effect operation = some (inputPort, outputPort))
    (finite : ClauseResults.PortBound outputPort input) : input ⊆ bound := by
  obtain ⟨resources, actual, included⟩ := DeclarationTemplates.check_iff_source_bound.mp (perform_check checked)
  rw [DeclarationTemplates.runtime_agreement _ (ClauseResults.resource_closed checked),
    OperationResults.analyze_perform_known known, finite] at actual
  have same : input = resources := Option.some.inj (TemplateSupport.lift_injective actual)
  exact same ▸ included

/-- Capture obtains both checked clauses and their answer bound from the
    selected runtime handler. Its declared result narrows the saved input;
    fresh historical metadata connects the new lexical ticket to that capture. -/
theorem capture_step
    (cut : HandlerCut requested whole capture tail handler)
    (selected : ClauseAt operation handler.clauses parameter binder body)
    (typed : ScopedPorts.ConfigurationTyped (DeclarationResults.signature declarations) tickets world
      ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ result)
    (known : DeclarationResults.signature declarations requested operation = some (inputPort, outputPort))
    (isValue : operand.IsValue)
    (checked : ConfigurationReturns declarations registry world
      ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ output)
    (fresh : registry owner = none) :
    let after : Configuration := ⟨body.subst parameter operand, .ticket binder owner,
      .live owner (ScopedPorts.embedPort outputPort) handler.answer capture handler.scope tail⟩
    RawStep ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
    ∃ record, ClauseResults.PortBound outputPort record.input ∧
      RegistryExtends registry (insert registry owner record) ∧
      ConfigurationReturns declarations (insert registry owner record) world after output := by
  obtain ⟨environment, ticket, bound, currentScope, code, stack⟩ := checked
  obtain ⟨savedEnvironment, savedTicket, answerBound, savedScope, clauses, saved, outside⟩ :=
    handler_cut_certificate cut stack
  obtain ⟨resultPort, current, stackTyped⟩ := typed
  cases current with
  | checked scopeTyped currentTyped =>
      obtain ⟨actualInput, declared, available, operandTyped⟩ := ScopedPorts.typed_perform_inversion currentTyped
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (known.symm.trans declared))
      have handlerKnown := known
      rw [← ScopedTyping.handler_cut_instance cut] at handlerKnown
      obtain ⟨closed, argumentBound, resumeBound, inputFinite, outputFinite, substituted⟩ :=
        ClauseResults.selected_clause_substitution selected clauses handlerKnown operandTyped isValue
      have savedNarrow := stack_input_weaken saved (declared_output_included code known outputFinite)
      let record : ResultRecord := ⟨resumeBound, answerBound⟩
      have extended : RegistryExtends registry (insert registry owner record) := insert_extends fresh
      have recorded : insert registry owner record owner = some record := by simp [insert]
      obtain ⟨savedTyped, outsideTyped, handlerTyped⟩ := ScopedPorts.handler_cut_retains_typing cut stackTyped
      cases handlerTyped with
      | handler caller clausesTyped coverage unique =>
          obtain ⟨clauseInput, clauseOutput, clauseKnown, bodyTyped⟩ := ScopedPorts.selected_clause_typed selected clausesTyped
          refine ⟨.capture requested operation parameter binder owner operand body scope whole capture tail handler
            (ScopedPorts.embedPort _) cut selected closed (ScopedPorts.typed_suffix_ready bodyTyped),
            record, outputFinite, extended, _, _, answerBound, .bound recorded, substituted, ?_⟩
          exact .live recorded (scope_extends savedScope extended)
            (stack_registry_extends savedNarrow extended) (List.Subset.refl _)
            (stack_registry_extends outside extended)

theorem bind_step
    (checked : ConfigurationReturns declarations registry world ⟨.bind name value body, scope, tail⟩ output)
    (closed : ClosedValue value) (suffixClosed : ClosedExcept name body) :
    RawStep ⟨.bind name value body, scope, tail⟩ ⟨body.subst name value, scope, tail⟩ [] [] ∧
    ConfigurationReturns declarations registry world ⟨body.subst name value, scope, tail⟩ output := by
  obtain ⟨environment, ticket, bound, scopeChecked, code, stack⟩ := checked
  refine ⟨.bind name value body scope tail closed suffixClosed, ?_⟩
  cases code with
  | existing code =>
      obtain ⟨input, substituted⟩ := GenerativeResults.bind_value_derivation code closed
      exact ⟨_, ticket, bound, scopeChecked, .existing substituted, stack⟩
  | bind initializer body =>
      refine ⟨_, ticket, bound, scopeChecked, ClauseResults.substitution body closed ?_, stack⟩
      intro resources bounded
      simp only [extendAnalysis, ↓reduceIte, GenerativeResults.summary_support] at bounded
      cases bounded
      have old := ClauseResults.actual_value_derivation initializer closed
      exact GenerativeResults.value_below_summary old closed _ (GenerativeResults.summary_support _)

theorem handler_entry_step
    (checked : ConfigurationReturns declarations registry world
      ⟨.handle (freezeEffect handler.effectInst) body handler.clauses, handler.scope, tail⟩ output) :
    RawStep ⟨.handle (freezeEffect handler.effectInst) body handler.clauses, handler.scope, tail⟩
      ⟨body, handler.scope, .push (.handler handler) tail⟩ [] [] ∧
    ConfigurationReturns declarations registry world ⟨body, handler.scope, .push (.handler handler) tail⟩ output := by
  obtain ⟨environment, ticket, bound, scopeChecked, code, stack⟩ := checked
  generalize same : freezeEffect handler.effectInst = effect at code
  cases code with
  | existing code => exact False.elim (GenerativeProgress.supported_head code)
  | handle body clauses closed =>
      have identical := freeze_effect_injective same
      cases identical
      exact ⟨.enterHandler handler _ tail, environment, ticket, bound, scopeChecked, body,
        .handler scopeChecked clauses (List.Subset.refl _) stack⟩

theorem handler_return_step
    (checked : ConfigurationReturns declarations registry world ⟨value, scope, .push (.handler handler) tail⟩ output)
    (closed : ClosedValue value) :
    RawStep ⟨value, scope, .push (.handler handler) tail⟩ ⟨value, handler.scope, tail⟩ [] [] ∧
    ConfigurationReturns declarations registry world ⟨value, handler.scope, tail⟩ output := by
  obtain ⟨environment, ticket, bound, currentScope, code, stack⟩ := checked
  cases stack with
  | handler savedScope clauses included rest =>
      exact ⟨.leaveHandler handler value closed scope tail, environment, _, _, savedScope,
        returned_value_rebind code closed included, rest⟩

theorem clause_return_step
    (checked : ConfigurationReturns declarations registry world ⟨value, scope, .spent owner answer caller tail⟩ output)
    (closed : ClosedValue value) :
    RawStep ⟨value, scope, .spent owner answer caller tail⟩ ⟨value, caller, tail⟩ [] [] ∧
    ConfigurationReturns declarations registry world ⟨value, caller, tail⟩ output := by
  obtain ⟨environment, ticket, bound, currentScope, code, stack⟩ := checked
  cases stack with
  | spent known savedScope included rest =>
      exact ⟨.leaveClause owner answer value closed scope caller tail, environment, _, _, savedScope,
        returned_value_rebind code closed included, rest⟩

theorem cell_return_step
    (checked : ConfigurationReturns declarations registry world
      ⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩ output)
    (closed : ClosedValue value) :
    RawStep ⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩
      ⟨value, savedScope, tail⟩ [] [.resource identity] ∧
    AccessChecks ⟨value, scope, .push (.cell identity payload savedScope answer) tail⟩ ambient ∧
    ConfigurationReturns declarations registry world ⟨value, savedScope, tail⟩ output := by
  obtain ⟨environment, ticket, bound, currentScope, code, stack⟩ := checked
  cases stack with
  | cell savedScopeChecked absent rest =>
      exact ⟨.leaveCell identity payload answer savedScope scope value closed tail,
        GenerativeResults.value_return_access (ClauseResults.actual_value_derivation code closed) closed absent,
        environment, _, bound, savedScopeChecked, returned_value_rebind code closed (List.Subset.refl _), rest⟩

theorem resource_step
    (checked : ConfigurationReturns declarations registry world ⟨.resource binder (.integer payload) body, scope, tail⟩ output)
    (fresh : identity ∉ world) :
    RawStep ⟨.resource binder (.integer payload) body, scope, tail⟩
      ⟨body.instantiate (Environment.empty.bind binder identity), scope, .push (.cell identity payload scope answer) tail⟩
      [.resource identity] [] ∧
    ConfigurationReturns declarations registry (world ++ [identity])
      ⟨body.instantiate (Environment.empty.bind binder identity), scope, .push (.cell identity payload scope answer) tail⟩ output := by
  obtain ⟨environment, ticket, bound, scopeChecked, code, stack⟩ := checked
  cases code with
  | existing code =>
      obtain ⟨step, bodyChecked, absent⟩ := GenerativeResults.resource_entry code fresh
      exact ⟨step, environment, ticket, bound, scopeChecked, .existing bodyChecked, .cell scopeChecked absent
        (stack_world_mono stack (List.subset_append_left _ _))⟩
  | resource initializer closed bodyChecked outward =>
      exact ⟨.enterCell binder identity payload body scope answer tail closed,
        environment, ticket, bound, scopeChecked, bodyChecked identity fresh,
        .cell scopeChecked (fun member => fresh (outward member))
          (stack_world_mono stack (List.subset_append_left _ _))⟩

namespace Examples
open ClauseResults.Examples
open GenerativeFrames.Examples (declarations environment)
open ContinuationBounds.Examples (family)
open DeclarationResults (signature)

def emptyRegistry : Registry := fun _ => none

theorem initial_results : ConfigurationReturns declarations emptyRegistry [] s0 [] :=
  ⟨environment, .none, [], .none, nested_handlers_checked, .nil (List.Subset.refl _)⟩

theorem outer_request_typed :
    ScopedPorts.ConfigurationTyped (signature declarations) (fun _ => none) [] s1 .integer := by
  refine ⟨.integer, .checked (allowed := [family]) .none
    (.perform rfl (by simp) .unit (List.nil_subset _)), .push ?_ .nil⟩
  exact .handler ⟨_, .none⟩
    (.cons (residual := []) rfl
      (.bind (.resume .integer (List.nil_subset _) (List.nil_subset _)) (inner_handler_typed _ _ _ _)) .nil)
    (single_coverage _ _ _) (by decide)

def outerTypes : ScopedPorts.TicketSignatures := fun owner =>
  if owner = 5 then some (.integer, .integer) else none

theorem inner_request_typed :
    ScopedPorts.ConfigurationTyped (signature declarations) outerTypes [] s8 .integer := by
  refine ⟨.integer, .checked (allowed := [family])
    (.bound (residual := []) (closing := []) rfl)
    (.perform rfl (by simp) .unit (List.nil_subset _)),
    .push ?_ (.spent rfl ⟨_, .none⟩ .nil)⟩
  exact .handler ⟨_, .bound (residual := []) (closing := []) rfl⟩
    (.cons (residual := []) rfl (.resume .integer (List.nil_subset _) (List.nil_subset _)) .nil)
    (single_coverage _ _ _) (by decide)

/-- Every intermediate state of the existing thirteen-step run carries the
    new result component. Type/usage/history synchronization is not asserted. -/
theorem nested_results : ∃ outer inner,
    let first := insert emptyRegistry 5 outer
    let second := insert first 6 inner
    ConfigurationReturns declarations emptyRegistry [] s0 [] ∧
    ConfigurationReturns declarations emptyRegistry [] s1 [] ∧
    ConfigurationReturns declarations first [] s2 [] ∧
    ConfigurationReturns declarations first [] s3 [] ∧
    ConfigurationReturns declarations first [] s4 [] ∧
    ConfigurationReturns declarations first [] s5 [] ∧
    ConfigurationReturns declarations first [] s6 [] ∧
    ConfigurationReturns declarations first [] s7 [] ∧
    ConfigurationReturns declarations first [] s8 [] ∧
    ConfigurationReturns declarations second [] s9 [] ∧
    ConfigurationReturns declarations second [] s10 [] ∧
    ConfigurationReturns declarations second [] s11 [] ∧
    ConfigurationReturns declarations second [] s12 [] ∧
    ConfigurationReturns declarations second [] s13 [] := by
  have c0 := initial_results
  have c1 : ConfigurationReturns declarations emptyRegistry [] s1 [] :=
    (handler_entry_step (handler := outerRuntime) c0).2
  obtain ⟨step1, outer, outerPort, firstExtends, c2⟩ := capture_step
    (owner := 5) (.hit outerRuntime .nil rfl) (ClauseAt.hit (rest := .nil))
    outer_request_typed (inputPort := .unit) (outputPort := .integer) rfl trivial c1 rfl
  have c2 : ConfigurationReturns declarations (insert emptyRegistry 5 outer) [] s2 [] := by
    simpa [s2, outerCapture, outerRuntime, outerClauses, outerBody, innerHandler, innerClauses, Code.subst, Clauses.subst, ScopedPorts.embedPort] using c2
  have c3 : ConfigurationReturns declarations (insert emptyRegistry 5 outer) [] s3 [] :=
    (focus_step (plain := waiting) (.bind (by simp [Code.IsValue])) c2).2
  have c4 : ConfigurationReturns declarations (insert emptyRegistry 5 outer) [] s4 [] :=
    (resume_step (front := .push (.plain waiting) .nil) (capture := outerCapture) rfl c3 (integer_closed 42)).2
  have c5 : ConfigurationReturns declarations (insert emptyRegistry 5 outer) [] s5 [] :=
    (handler_return_step c4 (integer_closed 42)).2
  have c6 : ConfigurationReturns declarations (insert emptyRegistry 5 outer) [] s6 [] :=
    (plug_step c5 (integer_closed 42)).2
  have c7 : ConfigurationReturns declarations (insert emptyRegistry 5 outer) [] s7 [] := by
    have result := (bind_step c6 (integer_closed 42) (by intro name member; cases member)).2
    simpa [s7, s6, innerHandler, innerClauses, Code.subst, Clauses.subst] using result
  have c8 : ConfigurationReturns declarations (insert emptyRegistry 5 outer) [] s8 [] :=
    (handler_entry_step (handler := innerRuntime) c7).2
  obtain ⟨step8, inner, innerPort, secondExtends, c9⟩ := capture_step
    (owner := 6) (.hit innerRuntime spentOuter rfl) (ClauseAt.hit (rest := .nil))
    inner_request_typed (inputPort := .unit) (outputPort := .integer) rfl trivial c8 (by simp [insert, emptyRegistry])
  have c9 : ConfigurationReturns declarations (insert (insert emptyRegistry 5 outer) 6 inner) [] s9 [] := c9
  have c10 : ConfigurationReturns declarations (insert (insert emptyRegistry 5 outer) 6 inner) [] s10 [] :=
    (resume_step (front := .nil) (capture := innerCapture) rfl c9 (integer_closed 17)).2
  have c11 : ConfigurationReturns declarations (insert (insert emptyRegistry 5 outer) 6 inner) [] s11 [] :=
    (handler_return_step c10 (integer_closed 17)).2
  have c12 : ConfigurationReturns declarations (insert (insert emptyRegistry 5 outer) 6 inner) [] s12 [] :=
    (clause_return_step c11 (integer_closed 17)).2
  have c13 : ConfigurationReturns declarations (insert (insert emptyRegistry 5 outer) 6 inner) [] s13 [] :=
    (clause_return_step c12 (integer_closed 17)).2
  exact ⟨outer, inner, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩

/-- The existing resource-owning capture also carries actual checked handler
    clauses. Resumption retains its cell and pending ordinary context. -/
theorem resource_request_results : ConfigurationReturns declarations emptyRegistry [7]
    ContinuationBounds.Examples.requesting [] := by
  refine ⟨environment, .none, [], .none,
    .existing (.perform (operandBound := []) (.leaf (Or.inl trivial) rfl rfl) rfl rfl), ?_⟩
  exact .plain (environment := environment) .none
    (.bind (.existing (.leaf (Or.inl trivial) rfl rfl))) (List.Subset.refl _)
    (.cell .none (by simp) (.handler .none clauses_checked (List.Subset.refl _) (.nil (List.Subset.refl _))))

theorem resource_capture_resume_results : ∃ record,
    RawStep ContinuationBounds.Examples.requesting ContinuationBounds.Examples.captured [.ticket 5] [] ∧
    ConfigurationReturns declarations (insert emptyRegistry 5 record) [7] ContinuationBounds.Examples.captured [] ∧
    RawStep ContinuationBounds.Examples.captured ContinuationBounds.Examples.resumed [] [.ticket 5] ∧
    ConfigurationReturns declarations (insert emptyRegistry 5 record) [7] ContinuationBounds.Examples.resumed [] := by
  obtain ⟨captureEvent, record, finite, extended, captured⟩ := capture_step (owner := 5)
    ContinuationBounds.Examples.saved_cut (ClauseAt.hit (rest := .nil)) request_typed
    (inputPort := .unit) (outputPort := .integer) rfl trivial resource_request_results rfl
  have captured : ConfigurationReturns declarations (insert emptyRegistry 5 record) [7]
      ContinuationBounds.Examples.captured [] := captured
  obtain ⟨resumeEvent, resumed⟩ := resume_step (front := .nil) (capture := ContinuationBounds.Examples.saved)
    rfl captured (integer_closed 42)
  exact ⟨record, captureEvent, captured, resumeEvent, resumed⟩

theorem wrong_historical_answer_rejected
    (known : registry 5 = some ⟨[], [7]⟩) :
    ¬ ScopeBound registry (.ticket 9 5) (.bound 9 [] []) := by
  intro checked
  have actual := scope_resolves checked (by rfl)
  have impossible := Option.some.inj (known.symm.trans actual)
  cases impossible

theorem smaller_closed_value_restores_saved_environment :
    Derives declarations environment [7] (.bound 9 [] [])
      (.bind 3 (.integer 42) (.variable 3)) [7] := by
  have context : ContextReturns declarations environment [7] (.bound 9 [] []) (.bind 3 (.variable 3)) [7] [7] :=
    .bind (.existing (.leaf (Or.inr ⟨3, rfl⟩) rfl (by decide)))
  have value : Derives declarations environment [] .none (.integer 42) [] :=
    .existing (.leaf (Or.inl trivial) rfl rfl)
  exact context_plug_returned_value context value (integer_closed 42) (List.nil_subset _)

theorem resource_support_cannot_be_erased :
    ¬ StackReturns declarations registry [7] .nil [7] [] := by
  intro checked
  cases checked with
  | nil included => exact List.not_mem_nil (included (List.mem_cons_self))

end Examples

end Ash.OneShot.ClauseFrames

#print axioms Ash.OneShot.ClauseFrames.insert_extends
#print axioms Ash.OneShot.ClauseFrames.scope_extends
#print axioms Ash.OneShot.ClauseFrames.scope_resolves
#print axioms Ash.OneShot.ClauseFrames.context_embeds
#print axioms Ash.OneShot.ClauseFrames.context_plug
#print axioms Ash.OneShot.ClauseFrames.returned_value_rebind
#print axioms Ash.OneShot.ClauseFrames.context_plug_returned_value
#print axioms Ash.OneShot.ClauseFrames.context_world_mono
#print axioms Ash.OneShot.ClauseFrames.focus_decompose
#print axioms Ash.OneShot.ClauseFrames.stack_input_weaken
#print axioms Ash.OneShot.ClauseFrames.stack_append
#print axioms Ash.OneShot.ClauseFrames.stack_decompose
#print axioms Ash.OneShot.ClauseFrames.stack_registry_extends
#print axioms Ash.OneShot.ClauseFrames.stack_world_mono
#print axioms Ash.OneShot.ClauseFrames.handler_cut_certificate
#print axioms Ash.OneShot.ClauseFrames.resume_recomposition
#print axioms Ash.OneShot.ClauseFrames.focus_step
#print axioms Ash.OneShot.ClauseFrames.plug_step
#print axioms Ash.OneShot.ClauseFrames.resume_step
#print axioms Ash.OneShot.ClauseFrames.perform_check
#print axioms Ash.OneShot.ClauseFrames.declared_output_included
#print axioms Ash.OneShot.ClauseFrames.capture_step
#print axioms Ash.OneShot.ClauseFrames.bind_step
#print axioms Ash.OneShot.ClauseFrames.handler_entry_step
#print axioms Ash.OneShot.ClauseFrames.handler_return_step
#print axioms Ash.OneShot.ClauseFrames.clause_return_step
#print axioms Ash.OneShot.ClauseFrames.cell_return_step
#print axioms Ash.OneShot.ClauseFrames.resource_step
#print axioms Ash.OneShot.ClauseFrames.Examples.initial_results
#print axioms Ash.OneShot.ClauseFrames.Examples.outer_request_typed
#print axioms Ash.OneShot.ClauseFrames.Examples.inner_request_typed
#print axioms Ash.OneShot.ClauseFrames.Examples.nested_results
#print axioms Ash.OneShot.ClauseFrames.Examples.wrong_historical_answer_rejected
#print axioms Ash.OneShot.ClauseFrames.Examples.smaller_closed_value_restores_saved_environment
#print axioms Ash.OneShot.ClauseFrames.Examples.resource_support_cannot_be_erased

#print axioms Ash.OneShot.ClauseFrames.Examples.resource_request_results
#print axioms Ash.OneShot.ClauseFrames.Examples.resource_capture_resume_results
