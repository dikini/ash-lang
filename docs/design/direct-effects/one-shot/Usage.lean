import Expressions

/-!
Structural one-shot continuation usage for the administrative expression fragment.

The policy supplies permissions for each locally bound ticket. This layer checks
syntax and local paths, not effect dispatch, capture compatibility, resource-safe
disposal, or whole-machine execution. Clause coverage and ordinary typing are
separate. A permission to dispose is not a proof that the captured control closes.
-/

namespace Ash.OneShot.Syntax

structure OneShotRights where
  resume : Bool
  dispose : Bool
  deriving DecidableEq, Repr

inductive UseScope where
  | none
  | ticket : Nat → OneShotRights → UseScope
  deriving DecidableEq, Repr

inductive UseState where
  | available
  | consumed
  deriving DecidableEq, Repr

abbrev TicketPolicy := Nat → OneShotRights

mutual
/-- Sequential rules thread state; both branch arms must yield the same state.
    Functions and nested clauses have their own checking scopes. -/
inductive Uses (policy : TicketPolicy) : UseScope → UseState → Expr → UseState → Prop where
  | unit : Uses policy scope state .unit state
  | boolean : Uses policy scope state (.boolean value) state
  | integer : Uses policy scope state (.integer value) state
  | variable : Uses policy scope state (.variable name) state
  | resourceRef : Uses policy scope state (.resourceRef resource) state
  | pair : Uses policy scope before left middle → Uses policy scope middle right after →
      Uses policy scope before (.pair left right) after
  | lambda : Uses policy .none .available body .available →
      Uses policy scope state (.lambda parameter body) state
  | app : Uses policy scope before function middle → Uses policy scope middle argument after →
      Uses policy scope before (.app function argument) after
  | bind : Uses policy scope before initializer middle → Uses policy scope middle suffix after →
      Uses policy scope before (.bind parameter initializer suffix) after
  | branch : Uses policy scope before condition middle →
      Uses policy scope middle yes after → Uses policy scope middle no after →
      Uses policy scope before (.branch condition yes no) after
  | perform : Uses policy scope before operand after →
      Uses policy scope before (.perform effectInst operation operand) after
  | handle : Uses policy scope before body after → ClausesUse policy clauses →
      Uses policy scope before (.handle effectInst body clauses) after
  | resume : rights.resume = true →
      Uses policy (.ticket ticket rights) before operand .available →
      Uses policy (.ticket ticket rights) before (.resume ticket operand) .consumed
  | discard : rights.dispose = true →
      Uses policy (.ticket ticket rights) .available (.discard ticket) .consumed
  | resource : Uses policy scope before initializer middle → Uses policy scope middle body after →
      Uses policy scope before (.resource resource initializer body) after
  | cleanup : Uses policy scope before action middle → Uses policy scope middle body after →
      Uses policy scope before (.cleanup action body) after

/-- Each clause receives only its own ticket and must consume it on normal
    syntactic completion. The policy is a binder-indexed administrative input. -/
inductive ClausesUse (policy : TicketPolicy) : Clauses → Prop where
  | nil : ClausesUse policy .nil
  | cons : Uses policy (.ticket ticket (policy ticket)) .available body .consumed →
      ClausesUse policy rest → ClausesUse policy (.cons operation parameter ticket body rest)
end

theorem use_state_monotone (checked : Uses policy scope before expression after) :
    before = .consumed → after = .consumed := by
  induction checked using Uses.rec (motive_2 := fun _ _ => True) with
  | unit | boolean | integer | «variable» | resourceRef | lambda => exact id
  | pair _ _ left right | app _ _ left right | bind _ _ left right
  | resource _ _ left right | cleanup _ _ left right => exact fun spent => right (left spent)
  | branch _ _ _ condition yes no => exact fun spent => yes (condition spent)
  | perform _ operand | handle _ _ operand clauses => exact operand
  | resume | discard => exact fun _ => rfl
  | nil | cons => trivial

theorem value_use_preserves_state (value : expression.IsValue)
    (checked : Uses policy scope before expression after) : before = after := by
  cases checked with
  | unit | boolean | integer | «variable» | resourceRef | lambda body => rfl
  | pair left right =>
      exact (value_use_preserves_state value.1 left).trans (value_use_preserves_state value.2 right)
  | app _ _ | bind _ _ | branch _ _ _ | perform _ | handle _ _ | resume _ _
  | discard _ | resource _ _ | cleanup _ _ => cases value

termination_by sizeOf expression

/-- Values that pass a usage check can be checked under any enclosing ticket:
    their function bodies already passed the no-enclosing-ticket barrier. -/
theorem value_use_transport (value : expression.IsValue)
    (checked : Uses policy scope before expression after) (destination : UseScope) (state : UseState) :
    Uses policy destination state expression state := by
  cases checked with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | «variable» => cases value
  | resourceRef => exact .resourceRef
  | lambda body => exact .lambda body
  | pair left right =>
      exact .pair (value_use_transport value.1 left destination state)
        (value_use_transport value.2 right destination state)
  | app _ _ | bind _ _ | branch _ _ _ | perform _ | handle _ _ | resume _ _
  | discard _ | resource _ _ | cleanup _ _ => cases value

termination_by sizeOf expression

mutual
theorem usage_substitution (checked : Uses policy scope before expression after)
    (value : replacement.IsValue)
    (replacementChecked : Uses policy .none .available replacement .available) (name : Nat) :
    Uses policy scope before (expression.subst name replacement) after := by
  cases checked with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | resourceRef => exact .resourceRef
  | «variable» =>
      simp only [Expr.subst]
      split
      · exact value_use_transport value replacementChecked _ _
      · exact .variable
  | lambda body =>
      apply Uses.lambda
      split
      · exact body
      · exact usage_substitution body value replacementChecked name
  | pair left right =>
      exact .pair (usage_substitution left value replacementChecked name)
        (usage_substitution right value replacementChecked name)
  | app left right =>
      exact .app (usage_substitution left value replacementChecked name)
        (usage_substitution right value replacementChecked name)
  | bind initializer suffix =>
      apply Uses.bind (usage_substitution initializer value replacementChecked name)
      split
      · exact suffix
      · exact usage_substitution suffix value replacementChecked name
  | branch condition yes no =>
      exact .branch (usage_substitution condition value replacementChecked name)
        (usage_substitution yes value replacementChecked name)
        (usage_substitution no value replacementChecked name)
  | perform operand => exact .perform (usage_substitution operand value replacementChecked name)
  | handle body clauses =>
      exact .handle (usage_substitution body value replacementChecked name)
        (clauses_usage_substitution clauses value replacementChecked name)
  | resume permission operand =>
      exact .resume permission (usage_substitution operand value replacementChecked name)
  | discard permission => exact .discard permission
  | resource initializer body =>
      exact .resource (usage_substitution initializer value replacementChecked name)
        (usage_substitution body value replacementChecked name)
  | cleanup action body =>
      exact .cleanup (usage_substitution action value replacementChecked name)
        (usage_substitution body value replacementChecked name)

termination_by sizeOf expression

theorem clauses_usage_substitution (checked : ClausesUse policy clauses)
    (value : replacement.IsValue)
    (replacementChecked : Uses policy .none .available replacement .available) (name : Nat) :
    ClausesUse policy (clauses.subst name replacement) := by
  cases checked with
  | nil => exact .nil
  | cons body rest =>
      apply ClausesUse.cons
      · split
        · exact body
        · exact usage_substitution body value replacementChecked name
      · exact clauses_usage_substitution rest value replacementChecked name
termination_by sizeOf clauses
end

theorem no_scope_use_transport (checked : Uses policy .none before expression after)
    (destination : UseScope) (state : UseState) : Uses policy destination state expression state := by
  cases checked with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | «variable» => exact .variable
  | resourceRef => exact .resourceRef
  | lambda body => exact .lambda body
  | pair left right =>
      exact .pair (no_scope_use_transport left destination state)
        (no_scope_use_transport right destination state)
  | app left right =>
      exact .app (no_scope_use_transport left destination state)
        (no_scope_use_transport right destination state)
  | bind left right =>
      exact .bind (no_scope_use_transport left destination state)
        (no_scope_use_transport right destination state)
  | branch condition yes no =>
      exact .branch (no_scope_use_transport condition destination state)
        (no_scope_use_transport yes destination state) (no_scope_use_transport no destination state)
  | perform operand => exact .perform (no_scope_use_transport operand destination state)
  | handle body clauses => exact .handle (no_scope_use_transport body destination state) clauses
  | resource left right =>
      exact .resource (no_scope_use_transport left destination state)
        (no_scope_use_transport right destination state)
  | cleanup left right =>
      exact .cleanup (no_scope_use_transport left destination state)
        (no_scope_use_transport right destination state)

termination_by sizeOf expression

theorem local_step_preserves_usage (step : LocalStep before after)
    (checked : Uses policy scope incoming before outgoing) :
    Uses policy scope incoming after outgoing := by
  induction step generalizing incoming outgoing scope with
  | bind parameter value suffix closed environmentReady fresh =>
      cases checked with
      | bind initializer suffix =>
          have same := value_use_preserves_state closed.1 initializer
          subst same
          exact usage_substitution suffix closed.1
            (value_use_transport closed.1 initializer .none .available) parameter
  | beta parameter body value closed closureReady fresh =>
      cases checked with
      | app function argument =>
          cases function with
          | lambda bodyChecked =>
              have same := value_use_preserves_state closed.1 argument
              subst same
              have substituted := usage_substitution bodyChecked closed.1
                (value_use_transport closed.1 argument .none .available) parameter
              -- A function body has no enclosing ticket; its ordinary computation
              -- can run without changing the caller's structural usage state.
              exact no_scope_use_transport substituted _ _
  | ifTrue yes no => cases checked with
      | branch condition yes no => cases condition; exact yes
  | ifFalse yes no => cases checked with
      | branch condition yes no => cases condition; exact no
  | pairLeft step right ih => cases checked with
      | pair left right => exact .pair (ih left) right
  | pairRight left closed step ih => cases checked with
      | pair left right => exact .pair left (ih right)
  | appFunction step argument ih => cases checked with
      | app function argument => exact .app (ih function) argument
  | appArgument function closed step ih => cases checked with
      | app function argument => exact .app function (ih argument)
  | bindInitializer parameter step suffix ih => cases checked with
      | bind initializer suffix => exact .bind (ih initializer) suffix
  | branchCondition step yes no ih => cases checked with
      | branch condition yes no => exact .branch (ih condition) yes no
  | performOperand effectInst operation step ih => cases checked with
      | perform operand => exact .perform (ih operand)
  | resumeOperand ticket step ih => cases checked with
      | resume permission operand => exact .resume permission (ih operand)
  | handlerBody effectInst step clauses ih => cases checked with
      | handle body clauses => exact .handle (ih body) clauses
  | resourceInitializer resource step body ih => cases checked with
      | resource initializer body => exact .resource (ih initializer) body
  | cleanupInitializer step body ih => cases checked with
      | cleanup action body => exact .cleanup (ih action) body

inductive UseAction where
  | resume : Nat → UseAction
  | dispose : Nat → UseAction
  deriving DecidableEq, Repr

def UseAction.ticket : UseAction → Nat
  | .resume ticket | .dispose ticket => ticket

/-- A syntactic explicit-use path chooses one branch at each conditional.
    It does not expand function calls, effect dispatch, or nested clauses.
    Those clauses are checked separately, with their own structural tickets. -/
inductive SyntaxPath : Expr → List UseAction → Prop where
  | unit : SyntaxPath .unit []
  | boolean : SyntaxPath (.boolean value) []
  | integer : SyntaxPath (.integer value) []
  | variable : SyntaxPath (.variable name) []
  | resourceRef : SyntaxPath (.resourceRef resource) []
  | lambda : SyntaxPath (.lambda parameter body) []
  | pair : SyntaxPath left xs → SyntaxPath right ys → SyntaxPath (.pair left right) (xs ++ ys)
  | app : SyntaxPath function xs → SyntaxPath argument ys → SyntaxPath (.app function argument) (xs ++ ys)
  | bind : SyntaxPath initializer xs → SyntaxPath suffix ys →
      SyntaxPath (.bind parameter initializer suffix) (xs ++ ys)
  | branchYes : SyntaxPath condition xs → SyntaxPath yes ys →
      SyntaxPath (.branch condition yes no) (xs ++ ys)
  | branchNo : SyntaxPath condition xs → SyntaxPath no ys →
      SyntaxPath (.branch condition yes no) (xs ++ ys)
  | perform : SyntaxPath operand xs → SyntaxPath (.perform effectInst operation operand) xs
  | handle : SyntaxPath body xs → SyntaxPath (.handle effectInst body clauses) xs
  | resume : SyntaxPath operand xs → SyntaxPath (.resume ticket operand) (xs ++ [.resume ticket])
  | discard : SyntaxPath (.discard ticket) [.dispose ticket]
  | resource : SyntaxPath initializer xs → SyntaxPath body ys →
      SyntaxPath (.resource resource initializer body) (xs ++ ys)
  | cleanup : SyntaxPath action xs → SyntaxPath body ys → SyntaxPath (.cleanup action body) (xs ++ ys)

/-- An independent one-shot protocol admits an empty path or exactly one
    permitted consumption. In particular there is no revival or second use. -/
inductive UseProtocol : UseScope → UseState → List UseAction → UseState → Prop where
  | nil : UseProtocol scope state [] state
  | resume : rights.resume = true →
      UseProtocol (.ticket ticket rights) .available [.resume ticket] .consumed
  | dispose : rights.dispose = true →
      UseProtocol (.ticket ticket rights) .available [.dispose ticket] .consumed

theorem use_protocol_append (left : UseProtocol scope before xs middle)
    (right : UseProtocol scope middle ys after) : UseProtocol scope before (xs ++ ys) after := by
  cases left with
  | nil => exact right
  | resume allowed => cases right; exact .resume allowed
  | dispose allowed => cases right; exact .dispose allowed

theorem usage_path_sound (checked : Uses policy scope before expression after)
    : ∀ {actions}, SyntaxPath expression actions → UseProtocol scope before actions after := by
  induction checked using Uses.rec (motive_2 := fun _ _ => True) with
  | unit | boolean | integer | «variable» | resourceRef | lambda =>
      intro actions path
      cases path; exact .nil
  | pair _ _ left right | app _ _ left right | bind _ _ left right
  | resource _ _ left right | cleanup _ _ left right =>
      intro actions path
      cases path
      rename_i px py
      exact use_protocol_append (left px) (right py)
  | branch _ _ _ condition yes no =>
      intro actions path
      cases path with
      | branchYes pc py => exact use_protocol_append (condition pc) (yes py)
      | branchNo pc pn => exact use_protocol_append (condition pc) (no pn)
  | perform _ operand =>
      intro actions path
      cases path with
      | perform po => exact operand po
  | handle _ _ body clauses =>
      intro actions path
      cases path with
      | handle pb => exact body pb
  | resume allowed _ operand =>
      intro actions path
      cases path with
      | resume po => exact use_protocol_append (operand po) (.resume allowed)
  | discard allowed =>
      intro actions path
      cases path; exact .dispose allowed
  | nil | cons => trivial

theorem usage_paths_at_most_once (checked : Uses policy scope before expression after)
    (path : SyntaxPath expression actions) : actions.length ≤ 1 := by
  have protocol := usage_path_sound checked path
  cases protocol <;> simp

theorem consuming_paths_exactly_once
    (checked : Uses policy (.ticket ticket rights) .available expression .consumed)
    (path : SyntaxPath expression actions) :
    (actions = [.resume ticket] ∧ rights.resume = true) ∨
      (actions = [.dispose ticket] ∧ rights.dispose = true) := by
  have protocol := usage_path_sound checked path
  cases protocol with
  | resume allowed => exact Or.inl ⟨rfl, allowed⟩
  | dispose allowed => exact Or.inr ⟨rfl, allowed⟩

theorem syntax_path_exists (expression : Expr) : ∃ actions, SyntaxPath expression actions := by
  cases expression with
  | unit => exact ⟨[], .unit⟩
  | boolean => exact ⟨[], .boolean⟩
  | integer => exact ⟨[], .integer⟩
  | «variable» => exact ⟨[], .variable⟩
  | resourceRef => exact ⟨[], .resourceRef⟩
  | lambda => exact ⟨[], .lambda⟩
  | pair left right =>
      obtain ⟨xs, px⟩ := syntax_path_exists left
      obtain ⟨ys, py⟩ := syntax_path_exists right
      exact ⟨xs ++ ys, .pair px py⟩
  | app left right =>
      obtain ⟨xs, px⟩ := syntax_path_exists left
      obtain ⟨ys, py⟩ := syntax_path_exists right
      exact ⟨xs ++ ys, .app px py⟩
  | bind parameter left right =>
      obtain ⟨xs, px⟩ := syntax_path_exists left
      obtain ⟨ys, py⟩ := syntax_path_exists right
      exact ⟨xs ++ ys, .bind px py⟩
  | branch condition yes no =>
      obtain ⟨xs, px⟩ := syntax_path_exists condition
      obtain ⟨ys, py⟩ := syntax_path_exists yes
      exact ⟨xs ++ ys, .branchYes px py⟩
  | perform effectInst operation operand =>
      obtain ⟨xs, px⟩ := syntax_path_exists operand
      exact ⟨xs, .perform px⟩
  | handle effectInst body clauses =>
      obtain ⟨xs, px⟩ := syntax_path_exists body
      exact ⟨xs, .handle px⟩
  | resume ticket operand =>
      obtain ⟨xs, px⟩ := syntax_path_exists operand
      exact ⟨xs ++ [.resume ticket], .resume px⟩
  | discard ticket => exact ⟨[.dispose ticket], .discard⟩
  | resource resource initializer body =>
      obtain ⟨xs, px⟩ := syntax_path_exists initializer
      obtain ⟨ys, py⟩ := syntax_path_exists body
      exact ⟨xs ++ ys, .resource px py⟩
  | cleanup action body =>
      obtain ⟨xs, px⟩ := syntax_path_exists action
      obtain ⟨ys, py⟩ := syntax_path_exists body
      exact ⟨xs ++ ys, .cleanup px py⟩

theorem syntax_path_event_dependency (path : SyntaxPath expression actions)
    (retained : action ∈ actions) : Dependency.ticket action.ticket ∈ expression.dependencies := by
  induction path with
  | unit | boolean | integer | «variable» | resourceRef | lambda => cases retained
  | pair px py ix iy | app px py ix iy | cleanup px py ix iy =>
      rcases List.mem_append.mp retained with hx | hy
      · exact List.mem_append_left _ (ix hx)
      · exact List.mem_append_right _ (iy hy)
  | bind px py ix iy | resource px py ix iy =>
      rcases List.mem_append.mp retained with hx | hy
      · exact List.mem_append_left _ (ix hx)
      · exact List.mem_append_right _ (mem_without.mpr ⟨iy hy, by simp⟩)
  | branchYes pc py ic iy =>
      rcases List.mem_append.mp retained with hc | hy
      · exact List.mem_append_left _ (List.mem_append_left _ (ic hc))
      · exact List.mem_append_left _ (List.mem_append_right _ (iy hy))
  | branchNo pc pn ic ino =>
      rcases List.mem_append.mp retained with hc | hn
      · exact List.mem_append_left _ (List.mem_append_left _ (ic hc))
      · exact List.mem_append_right _ (ino hn)
  | perform po io => exact List.mem_append_right _ (io retained)
  | handle pb ib => exact List.mem_append_left _ (List.mem_append_right _ (ib retained))
  | resume po io =>
      rcases List.mem_append.mp retained with ho | direct
      · exact List.mem_cons_of_mem _ (io ho)
      · simp only [List.mem_singleton] at direct
        subst direct
        exact List.mem_cons_self
  | discard =>
      simp only [List.mem_singleton] at retained
      subst retained
      exact List.mem_cons_self

theorem consuming_use_retains_ticket
    (checked : Uses policy (.ticket ticket rights) .available expression .consumed) :
    Dependency.ticket ticket ∈ expression.dependencies := by
  obtain ⟨actions, path⟩ := syntax_path_exists expression
  rcases consuming_paths_exactly_once checked path with ⟨resume, _⟩ | ⟨dispose, _⟩
  · exact syntax_path_event_dependency path (action := .resume ticket) (by simp [resume])
  · exact syntax_path_event_dependency path (action := .dispose ticket) (by simp [dispose])

/-- The pathwise obligation is retained by the binding annotation and therefore
    participates in the existing structural disposal rejection theorem. -/
theorem consuming_suffix_blocks_discard
    (checked : Uses policy (.ticket ticket rights) .available suffix .consumed)
    (cut : SourceCut effectInst
      (.push (bindingFrame parameter suffix input answer) rest) cap outer)
    (outside : ticket ∉ cap.liveTickets) : ¬ Discardable cap surviving plan :=
  pending_suffix_blocks_discard cut (consuming_use_retains_ticket checked) outside

theorem use_protocol_output_unique (left : UseProtocol scope before actions after)
    (right : UseProtocol scope before actions other) : after = other := by
  cases left <;> cases right <;> rfl

theorem usage_output_unique (left : Uses policy scope before expression after)
    (right : Uses policy scope before expression other) : after = other := by
  obtain ⟨actions, path⟩ := syntax_path_exists expression
  exact use_protocol_output_unique (usage_path_sound left path) (usage_path_sound right path)

namespace UsageExamples

def resumeOnly : OneShotRights := ⟨true, false⟩
def resumeOrDispose : OneShotRights := ⟨true, true⟩
def disposeOnly : OneShotRights := ⟨false, true⟩
def policy : TicketPolicy := fun _ => resumeOrDispose

theorem mixed_completion_branches_are_accepted :
    Uses policy (.ticket 9 resumeOrDispose) .available
      (.branch (.variable 0) (.resume 9 .unit) (.discard 9)) .consumed :=
  .branch .variable (.resume rfl .unit) (.discard rfl)

theorem no_completion_is_rejected :
    ¬ Uses policy (.ticket 9 resumeOrDispose) .available .unit .consumed := by
  intro checked
  cases checked

theorem double_completion_is_rejected :
    ¬ Uses policy (.ticket 9 resumeOrDispose) .available
      (.bind 0 (.resume 9 .unit) (.discard 9)) after := by
  intro checked
  have bound := usage_paths_at_most_once checked (.bind (.resume .unit) .discard)
  simp at bound

theorem incomplete_branch_is_rejected :
    ¬ Uses policy (.ticket 9 resumeOrDispose) .available
      (.branch (.variable 0) (.resume 9 .unit) .unit) .consumed := by
  intro checked
  have impossible := consuming_paths_exactly_once checked (.branchNo .variable .unit)
  simp at impossible

theorem unavailable_disposal_permission_is_rejected :
    ¬ Uses policy (.ticket 9 resumeOnly) .available (.discard 9) .consumed := by
  intro checked
  cases checked with
  | discard allowed => cases allowed

theorem unavailable_resume_permission_is_rejected :
    ¬ Uses policy (.ticket 9 disposeOnly) .available (.resume 9 .unit) .consumed := by
  intro checked
  cases checked with
  | resume allowed operand => cases allowed

theorem operand_cannot_consume_the_resumed_ticket :
    ¬ Uses policy (.ticket 9 resumeOrDispose) .available
      (.resume 9 (.discard 9)) after := by
  intro checked
  have bound := usage_paths_at_most_once checked (.resume .discard)
  simp at bound

theorem enclosing_ticket_cannot_cross_function :
    ¬ Uses policy (.ticket 9 resumeOrDispose) .available
      (.lambda 0 (.resume 9 .unit)) after := by
  intro checked
  cases checked with
  | lambda body => cases body

theorem nested_clauses_have_independent_tickets :
    Uses policy (.ticket 9 resumeOrDispose) .available
      (.bind 0
        (.handle (.user 1 []) .unit (.cons 0 1 10 (.resume 10 .unit) .nil))
        (.resume 9 .unit)) .consumed :=
  .bind (.handle .unit (.cons (.resume rfl .unit) .nil)) (.resume rfl .unit)

theorem nested_clause_cannot_consume_outer_ticket :
    ¬ Uses policy (.ticket 9 resumeOrDispose) .available
      (.handle (.user 1 []) .unit (.cons 0 1 10 (.resume 9 .unit) .nil)) after := by
  intro checked
  cases checked with
  | handle body clauses =>
      cases clauses with
      | cons inner rest => cases inner

/-- Free dependencies alone miss an invalid lambda inside a local clause:
    the local ticket is bound in the outer value but crosses an inner barrier. -/
def internallyCapturedTicket : Expr :=
  .lambda 0 (.handle (.user 1 []) .unit
    (.cons 0 1 10
      (.bind 2 (.lambda 3 (.resume 10 .unit)) (.resume 10 .unit)) .nil))

theorem closed_dependencies_do_not_establish_usage :
    ClosedValue internallyCapturedTicket ∧
      ¬ Uses policy .none .available internallyCapturedTicket .available := by
  constructor
  · simp [internallyCapturedTicket, ClosedValue, Expr.IsValue, Expr.dependencies,
      Clauses.dependencies, instanceDependencies, Instance.resources, without]
  · intro checked
    cases checked with
    | lambda body =>
        cases body with
        | handle body clauses =>
            cases clauses with
            | cons inner rest =>
                cases inner with
                | bind function suffix =>
                    cases function with
                    | lambda hidden => cases hidden

end UsageExamples

end Ash.OneShot.Syntax

#print axioms Ash.OneShot.Syntax.use_state_monotone
#print axioms Ash.OneShot.Syntax.usage_substitution
#print axioms Ash.OneShot.Syntax.local_step_preserves_usage
#print axioms Ash.OneShot.Syntax.usage_path_sound
#print axioms Ash.OneShot.Syntax.consuming_paths_exactly_once
#print axioms Ash.OneShot.Syntax.consuming_suffix_blocks_discard
