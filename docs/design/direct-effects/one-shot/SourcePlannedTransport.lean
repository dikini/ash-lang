import SourcePlannedTyping

/-! Transport the stable annotation derivation. The proof follows the existing
hereditary transport and reuses its syntax dependency and instantiation bounds.
No effect, resource-support or ownership argument is repeated here. -/
namespace Ash.OneShot.SourcePlannedTyping
open ScopedExpressions ScopedExecution

def AgreeOn (source destination : Environment) (dependencies : List Syntax.Dependency) : Prop :=
  ∀ name, Syntax.Dependency.variable name ∈ dependencies → source name = destination name

theorem agree_left (agree : AgreeOn source destination (left ++ right)) : AgreeOn source destination left :=
  fun _ member => agree _ (List.mem_append_left _ member)

theorem agree_right (agree : AgreeOn source destination (left ++ right)) : AgreeOn source destination right :=
  fun _ member => agree _ (List.mem_append_right _ member)

theorem agree_extend (agree : AgreeOn source destination (Syntax.without (.variable binder) dependencies)) :
    AgreeOn (source.extend binder value) (destination.extend binder value) dependencies := by
  intro name member
  by_cases same : name = binder
  · simp [Environment.extend, same]
  · simp only [Environment.extend, if_neg same]
    exact agree name (Syntax.mem_without.mpr ⟨member, by simpa using same⟩)

theorem opened_environment_agree {code : Code}
    (agree : AgreeOn source destination code.dependencies) :
    AgreeOn source destination (code.instantiate (Instantiation.Environment.empty.bind binder identity)).dependencies := by
  intro name member
  rcases List.mem_append.mp (ScopedExpressions.acquisition_dependency_bound _ identity _ member) with original | introduced
  · exact agree name original
  · simp at introduced

@[simp] theorem Environment.extend_shadow (environment : Environment) (name : Nat) (first second : Value) :
    (environment.extend name first).extend name second = environment.extend name second := by
  funext other
  by_cases same : other = name <;> simp [Environment.extend, same]

@[simp] theorem Environment.extend_commute (environment : Environment) (first second : Nat) (a b : Value)
    (different : first ≠ second) :
    (environment.extend first a).extend second b = (environment.extend second b).extend first a := by
  funext other
  by_cases one : other = first <;> by_cases two : other = second <;> simp_all [Environment.extend]

theorem Annotation.environment_congr
    (source : Annotation operations contracts world scope environment code value signature)
    (agree : AgreeOn environment destination code.dependencies) :
    Annotation operations contracts world scope destination code value signature := by
  induction source using Annotation.rec
    (motive_2 := fun contracts world environment parameter binder argument input answer resumeEffects closeEffects code held _ plans _ =>
      ∀ destination, AgreeOn environment destination (Syntax.without (.variable parameter) code.dependencies) →
      Offer operations contracts world destination parameter binder argument input answer resumeEffects closeEffects code held plans)
    (motive_3 := fun contracts world environment effect answer clauses _ plans _ =>
      ∀ destination, AgreeOn environment destination clauses.dependencies →
      Declarations operations contracts world destination effect answer plans) generalizing destination with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference => exact .reference
  | «variable» known => exact .variable ((agree _ List.mem_cons_self).symm.trans known)
  | lambda body ih => exact .lambda (ih (agree_extend agree))
  | purePair left right ihLeft ihRight => exact .purePair (ihLeft (agree_left agree)) (ihRight (agree_right agree))
  | pair left right ihLeft ihRight => exact .pair (ihLeft (agree_left agree)) (ihRight (agree_right agree))
  | app function argument ihFunction ihArgument => exact .app (ihFunction (agree_left agree)) (ihArgument (agree_right agree))
  | bind initial body ihInitial ihBody => exact .bind (ihInitial (agree_left agree)) (ihBody (agree_extend (agree_right agree)))
  | branch condition yes no ihCondition ihYes ihNo =>
      exact .branch (ihCondition (agree_left (agree_left agree))) (ihYes (agree_right (agree_left agree))) (ihNo (agree_right agree))
  | perform known operand ih => exact .perform known (ih (agree_right agree))
  | handler body declarations ihBody ihDeclarations =>
      exact .handler (ihBody (agree_right (agree_left agree))) (ihDeclarations destination (agree_right agree))
  | resume known resolved operand ih => exact .resume known resolved (ih (fun name member => agree name (List.mem_cons_of_mem _ member)))
  | discard known resolved => exact .discard known resolved
  | cleanup callback body ihCallback ihBody => exact .cleanup (ihCallback (agree_left agree)) (ihBody (agree_right agree))
  | resource initial body ihInitial ihBody =>
      exact .resource (ihInitial (agree_left agree)) (fun identity fresh => ihBody identity fresh (opened_environment_agree (agree_right agree)))
  | unavailable => exact .unavailable
  | available family ih =>
      rename_i destination agree
      exact .available (fun owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance =>
        ih owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance (agree_extend agree))
  | nil => exact .nil
  | cons known ordinary protectedMode rest ihOrdinary ihProtected ihRest =>
      rename_i destination agree
      have bodyAgree := fun name member => agree_left agree name (Syntax.mem_without.mpr ⟨member, by simp⟩)
      exact .cons known (ihOrdinary destination bodyAgree) (ihProtected destination bodyAgree) (ihRest destination (agree_right agree))

theorem Annotation.world_weaken
    (source : Annotation operations contracts world scope environment code value signature)
    (larger : world ⊆ next) : Annotation operations contracts next scope environment code value signature := by
  induction source using Annotation.rec
    (motive_2 := fun contracts world environment parameter binder argument input answer resumeEffects closeEffects code held _ plans _ =>
      ∀ next, world ⊆ next → Offer operations contracts next environment parameter binder argument input answer resumeEffects closeEffects code held plans)
    (motive_3 := fun contracts world environment effect answer _ _ plans _ =>
      ∀ next, world ⊆ next → Declarations operations contracts next environment effect answer plans) generalizing next with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference => exact .reference
  | «variable» known => exact .variable known
  | lambda body ih => exact .lambda (ih larger)
  | purePair left right ihLeft ihRight => exact .purePair (ihLeft larger) (ihRight larger)
  | pair left right ihLeft ihRight => exact .pair (ihLeft larger) (ihRight larger)
  | app function argument ihFunction ihArgument => exact .app (ihFunction larger) (ihArgument larger)
  | bind initial body ihInitial ihBody => exact .bind (ihInitial larger) (ihBody larger)
  | branch condition yes no ihCondition ihYes ihNo => exact .branch (ihCondition larger) (ihYes larger) (ihNo larger)
  | perform known operand ih => exact .perform known (ih larger)
  | handler body declarations ihBody ihDeclarations => exact .handler (ihBody larger) (ihDeclarations next larger)
  | resume known resolved operand ih => exact .resume known resolved (ih larger)
  | discard known resolved => exact .discard known resolved
  | cleanup callback body ihCallback ihBody => exact .cleanup (ihCallback larger) (ihBody larger)
  | resource initial body ihInitial ihBody =>
      exact .resource (ihInitial larger) (fun identity fresh => ihBody identity (fun member => fresh (larger member))
        (ScopedExpressions.append_subset larger (List.Subset.refl _)))
  | unavailable => exact .unavailable
  | available family ih =>
      rename_i next larger
      exact .available (fun owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance =>
        ih owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance larger)
  | nil => exact .nil
  | cons known ordinary protectedMode rest ihOrdinary ihProtected ihRest =>
      rename_i next larger
      exact .cons known (ihOrdinary next larger) (ihProtected next larger) (ihRest next larger)

def Contracts.Extends (before after : Contracts) : Prop :=
  ∀ owner contract, before owner = some contract → after owner = some contract

theorem insert_extends (contracts : Contracts) (fresh : contracts owner = none) :
    contracts.Extends (contracts.insert owner contract) := by
  intro other previous known
  by_cases same : other = owner
  · subst other; rw [fresh] at known; cases known
  · simp [Contracts.insert, same, known]

theorem extension_fresh {contracts next : Contracts}
    (extension : contracts.Extends next) (fresh : next owner = none) : contracts owner = none := by
  cases known : contracts owner with
  | none => rfl
  | some previous => have impossible := extension owner previous known; rw [fresh] at impossible; cases impossible

theorem insert_extension {contracts next : Contracts} (extension : contracts.Extends next) :
    (contracts.insert owner contract).Extends (next.insert owner contract) := by
  intro other previous known
  by_cases same : other = owner
  · simpa only [Contracts.insert, if_pos same] using known
  · simp only [Contracts.insert, if_neg same] at known ⊢
    exact extension other previous known

theorem Annotation.extension
    (source : Annotation operations contracts world scope environment code value signature)
    (extension : contracts.Extends next) : Annotation operations next world scope environment code value signature := by
  induction source using Annotation.rec
    (motive_2 := fun contracts world environment parameter binder argument input answer resumeEffects closeEffects code held _ plans _ =>
      ∀ next, contracts.Extends next → Offer operations next world environment parameter binder argument input answer resumeEffects closeEffects code held plans)
    (motive_3 := fun contracts world environment effect answer _ _ plans _ =>
      ∀ next, contracts.Extends next → Declarations operations next world environment effect answer plans) generalizing next with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference => exact .reference
  | «variable» known => exact .variable known
  | lambda body ih => exact .lambda (ih extension)
  | purePair left right ihLeft ihRight => exact .purePair (ihLeft extension) (ihRight extension)
  | pair left right ihLeft ihRight => exact .pair (ihLeft extension) (ihRight extension)
  | app function argument ihFunction ihArgument => exact .app (ihFunction extension) (ihArgument extension)
  | bind initial body ihInitial ihBody => exact .bind (ihInitial extension) (ihBody extension)
  | branch condition yes no ihCondition ihYes ihNo => exact .branch (ihCondition extension) (ihYes extension) (ihNo extension)
  | perform known operand ih => exact .perform known (ih extension)
  | handler body declarations ihBody ihDeclarations => exact .handler (ihBody extension) (ihDeclarations next extension)
  | resume known resolved operand ih => exact .resume (extension _ _ known) resolved (ih extension)
  | discard known resolved => exact .discard (extension _ _ known) resolved
  | cleanup callback body ihCallback ihBody => exact .cleanup (ihCallback extension) (ihBody extension)
  | resource initial body ihInitial ihBody => exact .resource (ihInitial extension) (fun identity fresh => ihBody identity fresh extension)
  | unavailable => exact .unavailable
  | available family ih =>
      rename_i next extension
      exact .available (fun owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance =>
        ih owner contract (extension_fresh extension fresh) inputSame answerSame resumeSame closeSame heldSame balance (insert_extension extension))
  | nil => exact .nil
  | cons known ordinary protectedMode rest ihOrdinary ihProtected ihRest =>
      rename_i next extension
      exact .cons known (ihOrdinary next extension) (ihProtected next extension) (ihRest next extension)

end Ash.OneShot.SourcePlannedTyping

#print axioms Ash.OneShot.SourcePlannedTyping.agree_left
#print axioms Ash.OneShot.SourcePlannedTyping.agree_right
#print axioms Ash.OneShot.SourcePlannedTyping.agree_extend
#print axioms Ash.OneShot.SourcePlannedTyping.opened_environment_agree
#print axioms Ash.OneShot.SourcePlannedTyping.Environment.extend_shadow
#print axioms Ash.OneShot.SourcePlannedTyping.Environment.extend_commute
#print axioms Ash.OneShot.SourcePlannedTyping.Annotation.environment_congr
#print axioms Ash.OneShot.SourcePlannedTyping.Annotation.world_weaken
#print axioms Ash.OneShot.SourcePlannedTyping.insert_extends
#print axioms Ash.OneShot.SourcePlannedTyping.extension_fresh
#print axioms Ash.OneShot.SourcePlannedTyping.insert_extension
#print axioms Ash.OneShot.SourcePlannedTyping.Annotation.extension
