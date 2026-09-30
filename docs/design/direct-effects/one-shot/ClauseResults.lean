import GenerativeProgress

/-!
Lexical continuation-result contracts and structural handler-clause checks on
Code. Stored result support is independent of value types and one-shot usage.
-/

namespace Ash.OneShot.ClauseResults
open Instantiation ScopedExpressions ScopedExecution
open ResultSummaries (extendAnalysis)
open GenerativeResults (summary)
open DeclarationResults (signature)
open ReturnSupport (Below)

inductive TicketBound where
  | none
  | bound (binder : Nat) (input answer : List Nat)
  deriving DecidableEq, Repr

def PortBound (port : ScopedPorts.Port) (bound : List Nat) : Prop :=
  (ContinuationBounds.portBound port).support = some bound

mutual
inductive Derives (declarations : DeclarationRegistry) :
    ResultSummaries.Environment → List Nat → TicketBound → Code → List Nat → Prop where
  | existing (checked : GenerativeResults.Derives declarations environment world code bound) :
      Derives declarations environment world ticket code bound
  | pair (leftChecked : Derives declarations environment world ticket left leftBound)
      (rightChecked : Derives declarations environment world ticket right rightBound) :
      Derives declarations environment world ticket (.pair left right) (leftBound ++ rightBound)
  | bind (initializerChecked : Derives declarations environment world ticket initializer inputBound)
      (bodyChecked : Derives declarations (extendAnalysis environment name (summary inputBound)) world ticket body outputBound) :
      Derives declarations environment world ticket (.bind name initializer body) outputBound
  | branch (conditionChecked : Derives declarations environment world ticket condition conditionBound)
      (yesChecked : Derives declarations environment world ticket yes bound)
      (noChecked : Derives declarations environment world ticket no bound) :
      Derives declarations environment world ticket (.branch condition yes no) bound
  | perform (operandChecked : Derives declarations environment world ticket operand operandBound)
      (closed : (Code.perform effect operation operand).ResourceClosed)
      (checked : DeclarationTemplates.check declarations environment bound (.perform effect operation operand) = true) :
      Derives declarations environment world ticket (.perform effect operation operand) bound
  | resource (initializerChecked : Derives declarations environment world ticket initializer initializerBound)
      (closed : (Code.resource binder initializer body).ResourceClosed)
      (bodyChecked : ∀ identity, identity ∉ world →
        Derives declarations environment (world ++ [identity]) ticket
          (body.instantiate (Environment.empty.bind binder identity)) bound)
      (outward : bound ⊆ world) :
      Derives declarations environment world ticket (.resource binder initializer body) bound
  | resume (operandChecked : Derives declarations environment world (.bound binder input answer) operand input) :
      Derives declarations environment world (.bound binder input answer) (.resume binder operand) answer
  | handle (bodyChecked : Derives declarations environment world ticket body answer)
      (clausesChecked : ClausesDerive declarations environment world effect answer clauses)
      (closed : (Code.handle (freezeEffect effect) body clauses).ResourceClosed) :
      Derives declarations environment world ticket (.handle (freezeEffect effect) body clauses) answer

inductive ClausesDerive (declarations : DeclarationRegistry) :
    ResultSummaries.Environment → List Nat → Instance → List Nat → Clauses → Prop where
  | nil : ClausesDerive declarations environment world effect answer .nil
  | cons (known : signature declarations effect operation = some (inputPort, outputPort))
      (input : PortBound inputPort argumentBound) (output : PortBound outputPort resumeBound)
      (bodyChecked : Derives declarations (extendAnalysis environment parameter (summary argumentBound)) world
        (.bound binder resumeBound answer) body answer)
      (restChecked : ClausesDerive declarations environment world effect answer rest) :
      ClausesDerive declarations environment world effect answer (.cons operation parameter binder body rest)
end

theorem resource_closed (checked : Derives declarations environment world ticket code bound) : code.ResourceClosed := by
  induction checked using Derives.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | existing checked => exact GenerativeResults.resource_closed checked
  | pair left right ihLeft ihRight | bind initializer body ihLeft ihRight =>
      exact List.append_eq_nil_iff.mpr ⟨ihLeft, ihRight⟩
  | branch condition yes no ihCondition ihYes ihNo =>
      exact List.append_eq_nil_iff.mpr ⟨List.append_eq_nil_iff.mpr ⟨ihCondition, ihYes⟩, ihNo⟩
  | perform operand closed finite ih | resource initializer closed body outward ihInit ihBody | handle body clauses closed ihBody ihClauses => exact closed
  | resume operand ih => exact ih
  | nil | cons => trivial

theorem actual_value_derivation
    (checked : Derives declarations environment world ticket value bound) (closed : ClosedValue value) :
    GenerativeResults.Derives declarations environment world value bound := by
  induction checked using Derives.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | existing checked => exact checked
  | pair left right ihLeft ihRight =>
      have leftClosed : ClosedValue _ := ⟨closed.1.1, (List.append_eq_nil_iff.mp closed.2.1).1,
        fun dependency member => closed.2.2 dependency (List.mem_append_left _ member)⟩
      have rightClosed : ClosedValue _ := ⟨closed.1.2, (List.append_eq_nil_iff.mp closed.2.1).2,
        fun dependency member => closed.2.2 dependency (List.mem_append_right _ member)⟩
      exact .pair (ihLeft leftClosed) (ihRight rightClosed)
  | bind | branch | perform | resource | resume | handle => cases closed.1
  | nil | cons => trivial

theorem value_support (checked : Derives declarations environment world ticket value bound)
    (closed : ClosedValue value) : Syntax.resourceDependencies value.dependencies ⊆ bound :=
  GenerativeResults.value_support (actual_value_derivation checked closed) closed

theorem world_mono (checked : Derives declarations environment world ticket code bound)
    (included : world ⊆ larger) : Derives declarations environment larger ticket code bound := by
  revert larger
  induction checked using Derives.rec
    (motive_2 := fun environment world effect bound clauses _ => ∀ {larger}, world ⊆ larger →
      ClausesDerive declarations environment larger effect bound clauses) with
  | existing checked =>
      intro larger included
      exact .existing (GenerativeResults.world_mono checked included)
  | pair left right ihLeft ihRight =>
      intro larger included
      exact .pair (ihLeft included) (ihRight included)
  | bind initializer body ihInit ihBody =>
      intro larger included
      exact .bind (ihInit included) (ihBody included)
  | branch condition yes no ihCondition ihYes ihNo =>
      intro larger included
      exact .branch (ihCondition included) (ihYes included) (ihNo included)
  | perform operand closed finite ih =>
      intro larger included
      exact .perform (ih included) closed finite
  | resource initializer closed body outward ihInit ihBody =>
      intro larger included
      exact .resource (ihInit included) closed
        (fun identity fresh => ihBody identity (fun member => fresh (included member))
          (ScopedExpressions.append_subset included (List.Subset.refl _))) (outward.trans included)
  | resume operand ih =>
      intro larger included
      exact .resume (ih included)
  | handle body clauses closed ihBody ihClauses =>
      intro larger included
      exact .handle (ihBody included) (ihClauses included) closed
  | nil => exact .nil
  | cons known input output body rest ihBody ihRest included =>
      exact .cons known input output (ihBody included) (ihRest included)

theorem clauses_world_mono (checked : ClausesDerive declarations environment world effect bound clauses)
    (included : world ⊆ larger) : ClausesDerive declarations environment larger effect bound clauses := by
  revert larger
  induction checked using ClausesDerive.rec
    (motive_1 := fun environment world ticket code bound _ => ∀ {larger}, world ⊆ larger →
      Derives declarations environment larger ticket code bound) with
  | existing checked included =>
      exact .existing (GenerativeResults.world_mono checked included)
  | pair left right ihLeft ihRight included =>
      exact .pair (ihLeft included) (ihRight included)
  | bind initializer body ihInit ihBody included =>
      exact .bind (ihInit included) (ihBody included)
  | branch condition yes no ihCondition ihYes ihNo included =>
      exact .branch (ihCondition included) (ihYes included) (ihNo included)
  | perform operand closed finite ih included =>
      exact .perform (ih included) closed finite
  | resource initializer closed body outward ihInit ihBody included =>
      exact .resource (ihInit included) closed
        (fun identity fresh => ihBody identity (fun member => fresh (included member))
          (ScopedExpressions.append_subset included (List.Subset.refl _))) (outward.trans included)
  | resume operand ih included =>
      exact .resume (ih included)
  | handle body clauses closed ihBody ihClauses included =>
      exact .handle (ihBody included) (ihClauses included) closed
  | nil => intro larger included; exact .nil
  | cons known input output body rest ihBody ihRest =>
      intro larger included
      exact .cons known input output (ihBody included) (ihRest included)

/-- Ordinary binders do not rename a lexical continuation contract. -/
theorem replacement_under_binding (closed : ClosedValue value)
    (bounded : Below (OperationResults.analyze (signature declarations) environment value) (environment name))
    (different : name ≠ binder) :
    Below (OperationResults.analyze (signature declarations) (extendAnalysis environment binder bound) value)
      ((extendAnalysis environment binder bound) name) := by
  intro resources known
  simp only [extendAnalysis, if_neg different] at known
  obtain ⟨retained, actual, included⟩ := bounded resources known
  exact ⟨retained, (OperationResults.closed_value_environment_support closed).trans actual, included⟩


theorem substitution_all (checked : Derives declarations environment world ticket code bound) :
    ∀ (value : Code) (name : Nat), ClosedValue value →
      Below (OperationResults.analyze (signature declarations) environment value) (environment name) →
      Derives declarations environment world ticket (code.subst name value) bound := by
  induction checked using Derives.rec
    (motive_2 := fun environment world effect bound clauses _ => ∀ (value : Code) (name : Nat), ClosedValue value →
      Below (OperationResults.analyze (signature declarations) environment value) (environment name) →
      ClausesDerive declarations environment world effect bound (clauses.subst name value)) with
  | existing checked =>
      intro value name closed valueBound
      exact .existing (GenerativeResults.substitution checked closed valueBound)
  | pair left right ihLeft ihRight =>
      intro value name closed valueBound
      exact .pair (ihLeft value name closed valueBound) (ihRight value name closed valueBound)
  | @bind environment world ticket initializer inputBound binder body outputBound initializerChecked bodyChecked ihInit ihBody =>
      intro value name closed valueBound
      change Derives _ _ _ _ (.bind binder (initializer.subst name value)
        (if name = binder then body else body.subst name value)) _
      by_cases same : name = binder
      · rw [if_pos same]
        exact .bind (ihInit value name closed valueBound) bodyChecked
      · rw [if_neg same]
        exact .bind (ihInit value name closed valueBound)
          (ihBody value name closed (replacement_under_binding closed valueBound same))
  | branch condition yes no ihCondition ihYes ihNo =>
      intro value name closed valueBound
      exact .branch (ihCondition value name closed valueBound)
        (ihYes value name closed valueBound) (ihNo value name closed valueBound)
  | perform operand codeClosed finite ih =>
      intro value name closed valueBound
      exact .perform (ih value name closed valueBound)
        (Code.subst_resource_closed _ _ _ codeClosed closed.2.1)
        (GenerativeResults.checked_substitution finite codeClosed closed valueBound)
  | resource initializer codeClosed body outward ihInit ihBody =>
      intro value name closed valueBound
      apply Derives.resource (ihInit value name closed valueBound)
        (Code.subst_resource_closed _ _ _ codeClosed closed.2.1) _ outward
      intro identity fresh
      rw [Code.instantiation_subst _ name value _ closed.2.1]
      exact ihBody identity fresh value name closed valueBound
  | resume operand ih =>
      intro value name closed valueBound
      exact .resume (ih value name closed valueBound)
  | handle body clauses codeClosed ihBody ihClauses =>
      intro value name closed valueBound
      exact .handle (ihBody value name closed valueBound) (ihClauses value name closed valueBound)
        (Code.subst_resource_closed _ _ _ codeClosed closed.2.1)
  | nil => exact .nil
  | @cons effect operation inputPort outputPort argumentBound resumeBound environment parameter world binder answer body rest known input output bodyChecked restChecked ihBody ihRest value name closed valueBound =>
      change ClausesDerive _ _ _ _ _ (.cons operation parameter binder
        (if name = parameter then body else body.subst name value) (rest.subst name value))
      by_cases same : name = parameter
      · rw [if_pos same]
        exact .cons known input output bodyChecked (ihRest value name closed valueBound)
      · rw [if_neg same]
        exact .cons known input output (ihBody value name closed (replacement_under_binding closed valueBound same))
          (ihRest value name closed valueBound)

theorem clauses_substitution_all (checked : ClausesDerive declarations environment world effect bound clauses) :
    ∀ (value : Code) (name : Nat), ClosedValue value →
      Below (OperationResults.analyze (signature declarations) environment value) (environment name) →
      ClausesDerive declarations environment world effect bound (clauses.subst name value) := by
  induction checked using ClausesDerive.rec
    (motive_1 := fun environment world ticket code bound _ => ∀ (value : Code) (name : Nat), ClosedValue value →
      Below (OperationResults.analyze (signature declarations) environment value) (environment name) →
      Derives declarations environment world ticket (code.subst name value) bound) with
  | existing checked value name closed valueBound =>
      exact .existing (GenerativeResults.substitution checked closed valueBound)
  | pair left right ihLeft ihRight value name closed valueBound =>
      exact .pair (ihLeft value name closed valueBound) (ihRight value name closed valueBound)
  | @bind environment world ticket initializer inputBound binder body outputBound initializerChecked bodyChecked ihInit ihBody value name closed valueBound =>
      change Derives _ _ _ _ (.bind binder (initializer.subst name value)
        (if name = binder then body else body.subst name value)) _
      by_cases same : name = binder
      · rw [if_pos same]
        exact .bind (ihInit value name closed valueBound) bodyChecked
      · rw [if_neg same]
        exact .bind (ihInit value name closed valueBound)
          (ihBody value name closed (replacement_under_binding closed valueBound same))
  | branch condition yes no ihCondition ihYes ihNo value name closed valueBound =>
      exact .branch (ihCondition value name closed valueBound)
        (ihYes value name closed valueBound) (ihNo value name closed valueBound)
  | perform operand codeClosed finite ih value name closed valueBound =>
      exact .perform (ih value name closed valueBound)
        (Code.subst_resource_closed _ _ _ codeClosed closed.2.1)
        (GenerativeResults.checked_substitution finite codeClosed closed valueBound)
  | resource initializer codeClosed body outward ihInit ihBody value name closed valueBound =>
      apply Derives.resource (ihInit value name closed valueBound)
        (Code.subst_resource_closed _ _ _ codeClosed closed.2.1) _ outward
      intro identity fresh
      rw [Code.instantiation_subst _ name value _ closed.2.1]
      exact ihBody identity fresh value name closed valueBound
  | resume operand ih value name closed valueBound =>
      exact .resume (ih value name closed valueBound)
  | handle body clauses codeClosed ihBody ihClauses value name closed valueBound =>
      exact .handle (ihBody value name closed valueBound) (ihClauses value name closed valueBound)
        (Code.subst_resource_closed _ _ _ codeClosed closed.2.1)
  | nil => intro value name closed valueBound; exact .nil
  | @cons effect operation inputPort outputPort argumentBound resumeBound environment parameter world binder answer body rest known input output bodyChecked restChecked ihBody ihRest =>
      intro value name closed valueBound
      change ClausesDerive _ _ _ _ _ (.cons operation parameter binder
        (if name = parameter then body else body.subst name value) (rest.subst name value))
      by_cases same : name = parameter
      · rw [if_pos same]
        exact .cons known input output bodyChecked (ihRest value name closed valueBound)
      · rw [if_neg same]
        exact .cons known input output (ihBody value name closed (replacement_under_binding closed valueBound same))
          (ihRest value name closed valueBound)

theorem substitution (checked : Derives declarations environment world ticket code bound)
    (closed : ClosedValue value)
    (valueBound : Below (OperationResults.analyze (signature declarations) environment value) (environment name)) :
    Derives declarations environment world ticket (code.subst name value) bound :=
  substitution_all checked value name closed valueBound

theorem clauses_substitution (checked : ClausesDerive declarations environment world effect bound clauses)
    (closed : ClosedValue value)
    (valueBound : Below (OperationResults.analyze (signature declarations) environment value) (environment name)) :
    ClausesDerive declarations environment world effect bound (clauses.subst name value) :=
  clauses_substitution_all checked value name closed valueBound

theorem selected_clause (selected : ClauseAt operation clauses parameter binder body)
    (checked : ClausesDerive declarations environment world effect answer clauses) :
    ∃ inputPort outputPort argumentBound resumeBound,
      signature declarations effect operation = some (inputPort, outputPort) ∧
      PortBound inputPort argumentBound ∧ PortBound outputPort resumeBound ∧
      Derives declarations (extendAnalysis environment parameter (summary argumentBound)) world
        (.bound binder resumeBound answer) body answer := by
  induction selected with
  | hit => cases checked with
      | cons known input output body rest => exact ⟨_, _, _, _, known, input, output, body⟩
  | pass different selected ih => cases checked with
      | cons known input output body rest => exact ih rest

/-- The parameter bound comes from the same operation lookup as actual value
    typing. Finite declared ports do not replace outward payload access checks. -/
theorem selected_clause_substitution
    (selected : ClauseAt operation clauses parameter binder body)
    (checked : ClausesDerive declarations environment world effect answer clauses)
    (known : signature declarations effect operation = some (inputPort, outputPort))
    (typed : ScopedPorts.Typed (signature declarations) world ScopedPorts.TypeEnv.empty ticket allowed operand inputPort)
    (isValue : operand.IsValue) :
    ClosedValue operand ∧ ∃ argumentBound resumeBound,
      PortBound inputPort argumentBound ∧ PortBound outputPort resumeBound ∧
      Derives declarations (extendAnalysis environment parameter (summary argumentBound)) world
        (.bound binder resumeBound answer) (body.subst parameter operand) answer := by
  obtain ⟨actualInput, actualOutput, argumentBound, resumeBound, declared, input, output, bodyChecked⟩ :=
    selected_clause selected checked
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (declared.symm.trans known))
  have closed := ScopedPorts.typed_value_closed typed isValue
  refine ⟨closed, argumentBound, resumeBound, input, output, substitution bodyChecked closed ?_⟩
  have below := OperationResults.typed_value_below_port
    (environment := extendAnalysis environment parameter (summary argumentBound)) typed isValue
  intro resources bounded
  simp only [extendAnalysis, ↓reduceIte, GenerativeResults.summary_support] at bounded
  cases bounded
  exact below argumentBound input

theorem resume_inversion
    (checked : Derives declarations environment world ticket (.resume binder operand) answer) :
    ∃ input, ticket = .bound binder input answer ∧
      Derives declarations environment world (.bound binder input answer) operand input := by
  cases checked with
  | existing checked => exact False.elim (GenerativeProgress.supported_head checked)
  | resume operand => exact ⟨_, rfl, operand⟩

/-- The runtime boundary retains the actual clause derivations at one shared
    answer bound. The old handler pass-through certificate alone supplies none. -/
def HandlerResults (declarations : DeclarationRegistry) (environment : ResultSummaries.Environment)
    (world : List Nat) (handler : HandlerData) (answer : List Nat) : Prop :=
  ClausesDerive declarations environment world handler.effectInst answer handler.clauses

theorem capture_result
    (cut : HandlerCut requested whole capture tail handler)
    (selected : ClauseAt operation handler.clauses parameter binder body)
    (typed : ScopedPorts.ConfigurationTyped (signature declarations) tickets world
      ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ result)
    (known : signature declarations requested operation = some (inputPort, outputPort))
    (isValue : operand.IsValue) (output : PortBound outputPort resumeBound)
    (clauses : HandlerResults declarations environment world handler answerBound)
    (saved : GenerativeFrames.StackReturns declarations world capture resumeBound answerBound)
    (outside : GenerativeFrames.StackReturns declarations world tail answerBound finalBound) :
    let after : Configuration := ⟨body.subst parameter operand, .ticket binder owner,
      .live owner (ScopedPorts.embedPort outputPort) handler.answer capture handler.scope tail⟩
    RawStep ⟨.perform (freezeEffect requested) operation operand, scope, whole⟩ after [.ticket owner] [] ∧
    (∃ argumentBound, PortBound inputPort argumentBound ∧
      Derives declarations (extendAnalysis environment parameter (summary argumentBound)) world
        (.bound binder resumeBound answerBound) after.expression answerBound) ∧
    GenerativeFrames.StackReturns declarations world after.stack answerBound finalBound := by
  obtain ⟨resultPort, current, stackTyped⟩ := typed
  cases current with
  | checked scopeTyped currentTyped =>
      obtain ⟨actualInput, declared, available, operandTyped⟩ := ScopedPorts.typed_perform_inversion currentTyped
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (known.symm.trans declared))
      have handlerKnown := known
      rw [← ScopedTyping.handler_cut_instance cut] at handlerKnown
      obtain ⟨closed, argumentBound, actualResume, input, actualOutput, substituted⟩ :=
        selected_clause_substitution selected clauses handlerKnown operandTyped isValue
      have same : actualResume = resumeBound := Option.some.inj (actualOutput.symm.trans output)
      subst actualResume
      obtain ⟨savedTyped, outsideTyped, handlerTyped⟩ := ScopedPorts.handler_cut_retains_typing cut stackTyped
      cases handlerTyped with
      | handler caller clausesTyped coverage unique =>
          obtain ⟨clauseInput, clauseOutput, clauseKnown, bodyTyped⟩ := ScopedPorts.selected_clause_typed selected clausesTyped
          have ready := ScopedPorts.typed_suffix_ready bodyTyped
          refine ⟨.capture requested operation parameter binder owner operand body scope whole capture tail handler
            (ScopedPorts.embedPort _) cut selected closed ready, ⟨argumentBound, input, substituted⟩, ?_⟩
          apply GenerativeFrames.StackReturns.live _ saved outside
          refine ⟨resumeBound, ?_, List.Subset.refl _⟩
          simpa only [ScopedPorts.erase_embed_port, PortBound] using output

/-- A source-derived operand bound can be used directly on resumption. The
    saved output still has to match the actual active prefix's input. -/
theorem resume_result {front capture tail : Stack}
    (resolved : scope.resolve binder = some owner)
    (typed : ScopedPorts.ConfigurationTyped (signature declarations) tickets world
      ⟨.resume binder value, scope, front.append (.live owner input answer capture caller tail)⟩ result)
    (isValue : value.IsValue)
    (checked : Derives declarations environment world (.bound binder inputBound answerBound)
      (.resume binder value) answerBound)
    (saved : GenerativeFrames.StackReturns declarations world capture inputBound answerBound)
    (frontChecked : GenerativeFrames.StackReturns declarations world front answerBound clauseBound)
    (outside : GenerativeFrames.StackReturns declarations world tail clauseBound finalBound) :
    RawStep ⟨.resume binder value, scope, front.append (.live owner input answer capture caller tail)⟩
      ⟨value, scope, capture.append (front.append (.spent owner answer caller tail))⟩ [] [.ticket owner] ∧
    GenerativeFrames.ConfigurationReturns declarations world
      ⟨value, scope, capture.append (front.append (.spent owner answer caller tail))⟩ finalBound := by
  obtain ⟨closed, bounded⟩ := ContinuationBounds.resume_operand_bound (environment := environment) resolved typed isValue
  obtain ⟨actualInput, same, operand⟩ := resume_inversion checked
  cases same
  exact ⟨.resume binder owner scope caller input answer front capture tail value closed resolved,
    environment, inputBound, actual_value_derivation operand closed,
    GenerativeFrames.stack_append saved (GenerativeFrames.stack_append frontChecked (.spent outside))⟩

namespace Examples
open GenerativeFrames.Examples (declarations environment answer)
open ContinuationBounds.Examples (family)

theorem clauses_checked : HandlerResults declarations environment [7] ContinuationBounds.Examples.handler [] :=
  .cons rfl rfl rfl (.resume (.existing (.leaf (Or.inl trivial) rfl rfl))) .nil

theorem request_typed : ScopedPorts.ConfigurationTyped (signature declarations) ContinuationBounds.Examples.tickets [7]
    ContinuationBounds.Examples.requesting (ScopedPorts.eraseType answer) := by
  refine ⟨.integer, .checked (allowed := [family]) .none ?_, GenerativeFrames.Examples.saved_capture_typed _⟩
  exact .perform rfl (by simp) .unit (List.nil_subset _)

theorem actual_capture_checks_clause :
    RawStep ContinuationBounds.Examples.requesting ContinuationBounds.Examples.captured [.ticket 5] [] ∧
    (∃ argumentBound, PortBound .unit argumentBound ∧
      Derives declarations (extendAnalysis environment 5 (summary argumentBound)) [7]
        (.bound 9 [] []) ContinuationBounds.Examples.captured.expression []) ∧
    GenerativeFrames.StackReturns declarations [7] ContinuationBounds.Examples.captured.stack [] [] :=
  capture_result ContinuationBounds.Examples.saved_cut .hit request_typed rfl trivial rfl clauses_checked
    GenerativeFrames.Examples.saved_capture_returns .nil

theorem actual_clause_resume :
    RawStep ContinuationBounds.Examples.captured ContinuationBounds.Examples.resumed [] [.ticket 5] ∧
    GenerativeFrames.ConfigurationReturns declarations [7] ContinuationBounds.Examples.resumed [] := by
  obtain ⟨argumentBound, input, checked⟩ := actual_capture_checks_clause.2.1
  exact resume_result (front := .nil) rfl GenerativeFrames.Examples.declared_capture_state_typed trivial checked
    GenerativeFrames.Examples.saved_capture_returns .nil .nil

def innerClauses : Clauses := .cons 0 5 10 (.resume 10 (.integer 17)) .nil
def innerHandler : Code := .handle (freezeEffect family) (.perform (freezeEffect family) 0 .unit) innerClauses
def outerBody : Code := .bind 3 (.resume 9 (.integer 42)) innerHandler
def outerClauses : Clauses := .cons 0 5 9 outerBody .nil
def nestedHandlers : Code := .handle (freezeEffect family) (.perform (freezeEffect family) 0 .unit) outerClauses

theorem inner_handler_checked (environment : ResultSummaries.Environment) (world : List Nat) (ticket : TicketBound) :
    Derives declarations environment world ticket innerHandler [] :=
  .handle (.existing (.perform (operandBound := []) (.leaf (Or.inl trivial) rfl rfl) rfl rfl))
    (.cons rfl rfl rfl (.resume (.existing (.leaf (Or.inl trivial) rfl rfl))) .nil) rfl

theorem nested_handlers_checked : Derives declarations environment [] .none nestedHandlers [] :=
  .handle (.existing (.perform (operandBound := []) (.leaf (Or.inl trivial) rfl rfl) rfl rfl))
    (.cons rfl rfl rfl (.bind (.resume (.existing (.leaf (Or.inl trivial) rfl rfl)))
      (inner_handler_checked _ _ _)) .nil) rfl

theorem single_coverage (parameter binder : Nat) (body : Code) :
    ScopedPorts.Covers (signature declarations) family (.cons 0 parameter binder body .nil) := by
  intro operation input output known
  cases operation with
  | zero => exact List.mem_cons_self
  | succ operation =>
      simp [signature, DeclarationResults.userSignature, GenerativeFrames.Examples.declarations, family,
        ScopedPorts.withCellSignatures] at known

theorem inner_handler_typed (world : List Nat) (environment : ScopedPorts.TypeEnv)
    (ticket : ScopedPorts.Ticket) (allowed : List Instance) :
    ScopedPorts.Typed (signature declarations) world environment ticket allowed innerHandler .integer :=
  .handle (.perform rfl (by simp) .unit (List.nil_subset _))
    (.cons rfl (.resume .integer (List.nil_subset _) (List.nil_subset _)) .nil)
    (single_coverage _ _ _) (by decide) (List.nil_subset _)

theorem nested_handlers_typed : ScopedPorts.Typed (signature declarations) [] ScopedPorts.TypeEnv.empty .none []
    nestedHandlers .integer :=
  .handle (.perform rfl (by simp) .unit (List.nil_subset _))
    (.cons rfl (.bind (.resume .integer (List.nil_subset _) (List.nil_subset _)) (inner_handler_typed _ _ _ _)) .nil)
    (single_coverage _ _ _) (by decide) (List.nil_subset _)

def policy : Syntax.TicketPolicy := fun _ => ActionRequirements.resumeOnly

theorem nested_handlers_use_one_shot : Uses policy .none .available nestedHandlers .available :=
  .handle (.perform .unit) (.cons (.bind (.resume rfl .integer)
    (.handle (.perform .unit) (.cons (.resume rfl .integer) .nil))) .nil)

theorem nested_initial_ready : ScopedPortPrepared.Ready (signature declarations) policy (fun _ => none) []
    ⟨⟨⟨nestedHandlers, .none, .nil⟩, [], []⟩, []⟩ .integer [] :=
  ScopedPortPrepared.initial_ready nested_handlers_typed nested_handlers_use_one_shot rfl

def duplicateResume : Code := .bind 3 (.resume 9 (.integer 1)) (.resume 9 (.integer 2))

theorem result_bounds_do_not_grant_reuse :
    Derives declarations environment [] (.bound 9 [] []) duplicateResume [] ∧
    ¬ Uses policy (.ticket 9 (policy 9)) .available duplicateResume .consumed := by
  refine ⟨.bind (.resume (.existing (.leaf (Or.inl trivial) rfl rfl)))
    (.resume (.existing (.leaf (Or.inl trivial) rfl rfl))), ?_⟩
  intro used
  cases used with
  | bind first second => cases first with
      | resume permission operand => cases second with
          | resume permission argument => cases argument

def outerRuntime : HandlerData := ⟨12, family, outerClauses, .none, .integer, rfl⟩
def innerRuntime : HandlerData := ⟨13, family, innerClauses, .ticket 9 5, .integer, rfl⟩
def waiting : PlainData := ⟨.bind 3 innerHandler, .ticket 9 5, .integer, .integer, [], rfl⟩
def outerCapture : Stack := .push (.handler outerRuntime) .nil
def innerCapture : Stack := .push (.handler innerRuntime) .nil
def spentOuter : Stack := .spent 5 .integer .none .nil

def s0 : Configuration := ⟨nestedHandlers, .none, .nil⟩
def s1 : Configuration := ⟨.perform (freezeEffect family) 0 .unit, .none, outerCapture⟩
def s2 : Configuration := ⟨outerBody, .ticket 9 5, .live 5 .integer .integer outerCapture .none .nil⟩
def s3 : Configuration := ⟨.resume 9 (.integer 42), .ticket 9 5,
  .push (.plain waiting) (.live 5 .integer .integer outerCapture .none .nil)⟩
def s4 : Configuration := ⟨.integer 42, .ticket 9 5,
  .push (.handler outerRuntime) (.push (.plain waiting) spentOuter)⟩
def s5 : Configuration := ⟨.integer 42, .none, .push (.plain waiting) spentOuter⟩
def s6 : Configuration := ⟨.bind 3 (.integer 42) innerHandler, .ticket 9 5, spentOuter⟩
def s7 : Configuration := ⟨innerHandler, .ticket 9 5, spentOuter⟩
def s8 : Configuration := ⟨.perform (freezeEffect family) 0 .unit, .ticket 9 5,
  .push (.handler innerRuntime) spentOuter⟩
def s9 : Configuration := ⟨.resume 10 (.integer 17), .ticket 10 6,
  .live 6 .integer .integer innerCapture (.ticket 9 5) spentOuter⟩
def s10 : Configuration := ⟨.integer 17, .ticket 10 6,
  .push (.handler innerRuntime) (.spent 6 .integer (.ticket 9 5) spentOuter)⟩
def s11 : Configuration := ⟨.integer 17, .ticket 9 5, .spent 6 .integer (.ticket 9 5) spentOuter⟩
def s12 : Configuration := ⟨.integer 17, .ticket 9 5, spentOuter⟩
def s13 : Configuration := ⟨.integer 17, .none, .nil⟩

theorem integer_closed (value : Int) : ClosedValue (.integer value) :=
  ⟨trivial, rfl, by intro dependency member; cases member⟩

theorem nested_trace : RawTrace s0 s13 [.ticket 5, .ticket 6] [.ticket 6, .ticket 5] := by
  have unitClosed : ClosedValue Code.unit := ⟨trivial, rfl, by intro dependency member; cases member⟩
  have e0 : RawStep s0 s1 [] [] := .enterHandler outerRuntime _ .nil
  have e1 : RawStep s1 s2 [.ticket 5] [] :=
    .capture family 0 5 9 5 .unit outerBody .none outerCapture outerCapture .nil outerRuntime .integer
      (.hit outerRuntime .nil rfl) .hit unitClosed (by
        simp [ClosedExcept, outerBody, innerHandler, innerClauses, Code.dependencies, Clauses.dependencies, Syntax.without])
  have e2 : RawStep s2 s3 [] [] := .focus waiting (.bind (by simp [Code.IsValue])) _
  have e3 : RawStep s3 s4 [] [.ticket 5] :=
    .resume 9 5 (.ticket 9 5) .none .integer .integer (.push (.plain waiting) .nil) outerCapture .nil
      (.integer 42) (integer_closed 42) rfl
  have e4 : RawStep s4 s5 [] [] := .leaveHandler outerRuntime (.integer 42) (integer_closed 42) _ _
  have e5 : RawStep s5 s6 [] [] := .plug waiting (.integer 42) (integer_closed 42) .none _
  have e6 : RawStep s6 s7 [] [] :=
    .bind 3 (.integer 42) innerHandler (.ticket 9 5) spentOuter (integer_closed 42) (by intro name member; cases member)
  have e7 : RawStep s7 s8 [] [] := .enterHandler innerRuntime _ spentOuter
  have e8 : RawStep s8 s9 [.ticket 6] [] :=
    .capture family 0 5 10 6 .unit (.resume 10 (.integer 17)) (.ticket 9 5)
      (.push (.handler innerRuntime) spentOuter) innerCapture spentOuter innerRuntime .integer
      (.hit innerRuntime spentOuter rfl) .hit unitClosed (by simp [ClosedExcept, Code.dependencies])
  have e9 : RawStep s9 s10 [] [.ticket 6] :=
    .resume 10 6 (.ticket 10 6) (.ticket 9 5) .integer .integer .nil innerCapture spentOuter
      (.integer 17) (integer_closed 17) rfl
  have e10 : RawStep s10 s11 [] [] := .leaveHandler innerRuntime (.integer 17) (integer_closed 17) _ _
  have e11 : RawStep s11 s12 [] [] := .leaveClause 6 .integer (.integer 17) (integer_closed 17) _ _ _
  have e12 : RawStep s12 s13 [] [] := .leaveClause 5 .integer (.integer 17) (integer_closed 17) _ _ _
  exact .next e0 (.next e1 (.next e2 (.next e3 (.next e4 (.next e5 (.next e6
    (.next e7 (.next e8 (.next e9 (.next e10 (.next e11 (.next e12 (.refl _)))))))))))))

theorem nested_execution : RunSteps ⟨s0, [], []⟩ ⟨s13, [.ticket 5, .ticket 6], [.ticket 6, .ticket 5]⟩ :=
  raw_trace_enacts nested_trace (issued := []) (completed := []) (by decide)

theorem nested_ledger : Ledger (RunState.erase ⟨s13, [.ticket 5, .ticket 6], [.ticket 6, .ticket 5]⟩) :=
  run_steps_preserve_ledger nested_execution ⟨.refl _, by decide⟩

theorem wrong_clause_ticket_rejected :
    ¬ Derives declarations environment [7] (.bound 10 [] []) (.resume 9 (.integer 42)) [] := by
  intro checked
  obtain ⟨input, impossible, operand⟩ := resume_inversion checked
  cases impossible

theorem callable_parameter_bound_unknown (bound : List Nat) :
    ¬ PortBound (ScopedPorts.eraseType answer) bound := by intro known; cases known

end Examples

end Ash.OneShot.ClauseResults

#print axioms Ash.OneShot.ClauseResults.resource_closed
#print axioms Ash.OneShot.ClauseResults.actual_value_derivation
#print axioms Ash.OneShot.ClauseResults.value_support
#print axioms Ash.OneShot.ClauseResults.world_mono
#print axioms Ash.OneShot.ClauseResults.clauses_world_mono
#print axioms Ash.OneShot.ClauseResults.replacement_under_binding
#print axioms Ash.OneShot.ClauseResults.substitution_all
#print axioms Ash.OneShot.ClauseResults.clauses_substitution_all
#print axioms Ash.OneShot.ClauseResults.substitution
#print axioms Ash.OneShot.ClauseResults.clauses_substitution
#print axioms Ash.OneShot.ClauseResults.selected_clause
#print axioms Ash.OneShot.ClauseResults.selected_clause_substitution
#print axioms Ash.OneShot.ClauseResults.resume_inversion
#print axioms Ash.OneShot.ClauseResults.capture_result
#print axioms Ash.OneShot.ClauseResults.resume_result
#print axioms Ash.OneShot.ClauseResults.Examples.clauses_checked
#print axioms Ash.OneShot.ClauseResults.Examples.request_typed
#print axioms Ash.OneShot.ClauseResults.Examples.actual_capture_checks_clause
#print axioms Ash.OneShot.ClauseResults.Examples.actual_clause_resume
#print axioms Ash.OneShot.ClauseResults.Examples.inner_handler_checked
#print axioms Ash.OneShot.ClauseResults.Examples.nested_handlers_checked
#print axioms Ash.OneShot.ClauseResults.Examples.single_coverage
#print axioms Ash.OneShot.ClauseResults.Examples.inner_handler_typed
#print axioms Ash.OneShot.ClauseResults.Examples.nested_handlers_typed
#print axioms Ash.OneShot.ClauseResults.Examples.nested_handlers_use_one_shot
#print axioms Ash.OneShot.ClauseResults.Examples.nested_initial_ready
#print axioms Ash.OneShot.ClauseResults.Examples.result_bounds_do_not_grant_reuse
#print axioms Ash.OneShot.ClauseResults.Examples.integer_closed
#print axioms Ash.OneShot.ClauseResults.Examples.nested_trace
#print axioms Ash.OneShot.ClauseResults.Examples.nested_execution
#print axioms Ash.OneShot.ClauseResults.Examples.nested_ledger
#print axioms Ash.OneShot.ClauseResults.Examples.wrong_clause_ticket_rejected
#print axioms Ash.OneShot.ClauseResults.Examples.callable_parameter_bound_unknown
