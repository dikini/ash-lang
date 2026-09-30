import SourceDependencyAnnotations
import DeclaredSourceValues

/-! Transport the hereditary dependency annotations without changing them.
The inductions follow DeclaredSourceTransport; ordinary port and source support
lemmas are reused. Rich value equality must be retained in the environment and
continuation registry, so erasure alone cannot discharge these obligations. -/
namespace Ash.OneShot.SourceDependencyAnnotations
open ScopedExpressions ScopedExecution ProtectionContracts
open RecursiveRequirements (Requirements)

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

theorem expression_environment_congr
    (source : Expression operations policy contracts world allowed scope environment code result demand requirements dependencies)
    (agree : AgreeOn environment destination code.dependencies) :
    Expression operations policy contracts world allowed scope destination code result demand requirements dependencies := by
  induction source using Expression.rec
      (motive_2 := fun contracts world allowed scope environment code value header dependencies _ => ∀ destination,
        AgreeOn environment destination code.dependencies →
          Body operations policy contracts world allowed scope destination code value header dependencies)
      (motive_3 := fun contracts world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row dependencies _ => ∀ destination,
        AgreeOn environment destination (Syntax.without (.variable parameter) code.dependencies) →
          Offer operations policy contracts world destination allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row dependencies)
      (motive_4 := fun contracts world environment allowed effect answer clauses table dependencies _ => ∀ destination,
        AgreeOn environment destination clauses.dependencies →
          Declarations operations policy contracts world destination allowed effect answer clauses table dependencies)
      generalizing destination with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | «variable» known formed => exact .variable ((agree _ List.mem_cons_self).symm.trans known) formed
  | lambda body outward formed latentBound ih => exact .lambda (ih (agree_extend agree)) outward formed latentBound
  | purePair left right ihLeft ihRight => exact .purePair (ihLeft (agree_left agree)) (ihRight (agree_right agree))
  | pair left right ihLeft ihRight => exact .pair (ihLeft (agree_left agree)) (ihRight (agree_right agree))
  | app function argument admitted ihFunction ihArgument =>
      exact .app (ihFunction (agree_left agree)) (ihArgument (agree_right agree)) admitted
  | bind initializer body ihInit ihBody => exact .bind (ihInit (agree_left agree)) (ihBody (agree_extend (agree_right agree)))
  | branch condition yes no same ihCondition ihYes ihNo =>
      exact .branch (ihCondition (agree_left (agree_left agree)))
        (ihYes (agree_right (agree_left agree))) (ihNo (agree_right agree)) same
  | perform known admitted operand formed ih => exact .perform known admitted (ih (agree_right agree)) formed
  | handler body clauses capabilities coverage unique admitted table modes declarations ihBody ihDecl =>
      apply Expression.handler (ihBody (agree_right (agree_left agree))) _ capabilities coverage unique admitted table modes
        (ihDecl destination (agree_right agree))
      apply ScopedPorts.clauses_environment_congr clauses
      intro name member
      simp only [CoherentSourceTypes.Environment.ports, Environment.erase, agree_right agree name member]
  | resume known resolved permission operand admitted formed ih =>
      exact .resume known resolved permission (ih (fun name member => agree name (List.mem_cons_of_mem _ member))) admitted formed
  | discard known resolved permission unprotected admitted => exact .discard known resolved permission unprotected admitted
  | cleanup callback body admitted ihCallback ihBody =>
      exact .cleanup (ihCallback (agree_left agree)) (ihBody (agree_right agree)) admitted
  | resource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      exact .resource (ihInit (agree_left agree))
        (fun identity fresh => ihBody identity fresh (opened_environment_agree (agree_right agree)))
        formed effectsBound admitted hidden
  | typed body rows ih =>
      rename_i destination agree
      exact .typed (ih agree) rows
  | annotated body annotation rows ih =>
      rename_i destination agree
      exact .annotated (ih agree) annotation rows
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface family ih =>
      rename_i destination agree
      apply Offer.available resumeInterface closeInterface
      intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
      exact ih owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance _ (agree_extend agree)
  | nil => exact .nil
  | cons known ordinary protectedMode rest ihOrdinary ihProtected ihRest =>
      rename_i destination agree
      have bodyAgree := fun name member => agree_left agree name
        (Syntax.mem_without.mpr ⟨member, by simp⟩)
      exact .cons known (ihOrdinary destination bodyAgree) (ihProtected destination bodyAgree) (ihRest destination (agree_right agree))

theorem expression_world_weaken
    (source : Expression operations policy contracts world allowed scope environment code result demand requirements dependencies)
    (larger : world ⊆ next) :
    Expression operations policy contracts next allowed scope environment code result demand requirements dependencies := by
  induction source using Expression.rec
      (motive_2 := fun contracts world allowed scope environment code value header dependencies _ => ∀ next, world ⊆ next →
        Body operations policy contracts next allowed scope environment code value header dependencies)
      (motive_3 := fun contracts world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row dependencies _ => ∀ next, world ⊆ next →
        Offer operations policy contracts next environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row dependencies)
      (motive_4 := fun contracts world environment allowed effect answer clauses table dependencies _ => ∀ next, world ⊆ next →
        Declarations operations policy contracts next environment allowed effect answer clauses table dependencies)
      generalizing next with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference (larger issued)
  | «variable» known formed => exact .variable known (ScopedPorts.in_world_mono formed larger)
  | lambda body outward formed latentBound ih => exact .lambda (ih larger) outward (ScopedPorts.in_world_mono formed larger) latentBound
  | purePair left right ihLeft ihRight => exact .purePair (ihLeft larger) (ihRight larger)
  | pair left right ihLeft ihRight => exact .pair (ihLeft larger) (ihRight larger)
  | app function argument admitted ihFunction ihArgument => exact .app (ihFunction larger) (ihArgument larger) admitted
  | bind initializer body ihInit ihBody => exact .bind (ihInit larger) (ihBody larger)
  | branch condition yes no same ihCondition ihYes ihNo => exact .branch (ihCondition larger) (ihYes larger) (ihNo larger) same
  | perform known admitted operand formed ih => exact .perform known admitted (ih larger) (ScopedPorts.in_world_mono formed larger)
  | handler body clauses capabilities coverage unique admitted table modes declarations ihBody ihDecl =>
      exact .handler (ihBody larger) (ScopedPorts.clauses_world_weaken clauses larger) capabilities coverage unique admitted table modes (ihDecl next larger)
  | resume known resolved permission operand admitted formed ih =>
      exact .resume known resolved permission (ih larger) admitted (ScopedPorts.in_world_mono formed larger)
  | discard known resolved permission unprotected admitted => exact .discard known resolved permission unprotected admitted
  | cleanup callback body admitted ihCallback ihBody => exact .cleanup (ihCallback larger) (ihBody larger) admitted
  | resource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      exact .resource (ihInit larger)
        (fun identity fresh => ihBody identity (fun member => fresh (larger member))
          (ScopedExpressions.append_subset larger (List.Subset.refl _)))
        (ScopedPorts.in_world_mono formed larger) (effectsBound.trans larger) admitted
        (fun identity fresh => hidden identity (fun member => fresh (larger member)))
  | typed body rows ih =>
      rename_i next larger
      exact .typed (ih larger) rows
  | annotated body annotation rows ih =>
      rename_i next larger
      exact .annotated (ih larger) annotation rows
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface family ih =>
      rename_i next larger
      apply Offer.available resumeInterface closeInterface
      intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
      exact ih owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance next larger
  | nil => exact .nil
  | cons known ordinary protectedMode rest ihOrdinary ihProtected ihRest =>
      rename_i next larger
      exact .cons known (ihOrdinary next larger) (ihProtected next larger) (ihRest next larger)

theorem expression_extension
    (source : Expression operations policy contracts world allowed scope environment code result demand requirements dependencies)
    (extension : contracts.Extends larger) :
    Expression operations policy larger world allowed scope environment code result demand requirements dependencies := by
  induction source using Expression.rec
      (motive_2 := fun contracts world allowed scope environment code value header dependencies _ => ∀ larger, contracts.Extends larger →
        Body operations policy larger world allowed scope environment code value header dependencies)
      (motive_3 := fun contracts world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row dependencies _ => ∀ larger, contracts.Extends larger →
        Offer operations policy larger world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row dependencies)
      (motive_4 := fun contracts world environment allowed effect answer clauses table dependencies _ => ∀ larger, contracts.Extends larger →
        Declarations operations policy larger world environment allowed effect answer clauses table dependencies)
      generalizing larger with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | «variable» known formed => exact .variable known formed
  | lambda body outward formed latentBound ih => exact .lambda (ih extension) outward formed latentBound
  | purePair left right ihLeft ihRight => exact .purePair (ihLeft extension) (ihRight extension)
  | pair left right ihLeft ihRight => exact .pair (ihLeft extension) (ihRight extension)
  | app function argument admitted ihFunction ihArgument => exact .app (ihFunction extension) (ihArgument extension) admitted
  | bind initializer body ihInit ihBody => exact .bind (ihInit extension) (ihBody extension)
  | branch condition yes no same ihCondition ihYes ihNo => exact .branch (ihCondition extension) (ihYes extension) (ihNo extension) same
  | perform known admitted operand formed ih => exact .perform known admitted (ih extension) formed
  | handler body clauses capabilities coverage unique admitted table modes declarations ihBody ihDecl =>
      exact .handler (ihBody extension) clauses capabilities coverage unique admitted table modes (ihDecl larger extension)
  | resume known resolved permission operand admitted formed ih => exact .resume (extension _ _ known) resolved permission (ih extension) admitted formed
  | discard known resolved permission unprotected admitted => exact .discard (extension _ _ known) resolved permission unprotected admitted
  | cleanup callback body admitted ihCallback ihBody => exact .cleanup (ihCallback extension) (ihBody extension) admitted
  | resource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      exact .resource (ihInit extension) (fun identity fresh => ihBody identity fresh extension) formed effectsBound admitted hidden
  | typed body rows ih =>
      rename_i larger extension
      exact .typed (ih extension) rows
  | annotated body annotation rows ih =>
      rename_i larger extension
      exact .annotated (ih extension) annotation rows
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface family ih =>
      rename_i larger extension
      apply Offer.available resumeInterface closeInterface
      intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
      exact ih owner contract (extension_fresh extension fresh)
        inputSame answerSame resumeSame closeSame heldSame balance _ (insert_extension extension)
  | nil => exact .nil
  | cons known ordinary protectedMode rest ihOrdinary ihProtected ihRest =>
      rename_i larger extension
      exact .cons known (ihOrdinary larger extension) (ihProtected larger extension) (ihRest larger extension)

theorem expression_allowed_mono
    (source : Expression operations policy contracts world allowed scope environment code result demand requirements dependencies)
    (more : allowed ⊆ destination) :
    Expression operations policy contracts world destination scope environment code result demand requirements dependencies := by
  induction source using Expression.rec
      (motive_2 := fun _ _ _ _ _ _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ _ _ _ _ => True) generalizing destination with
  | unit => exact .unit
  | boolean => exact .boolean
  | integer => exact .integer
  | reference issued => exact .reference issued
  | «variable» known formed => exact .variable known formed
  | lambda body outward formed latentBound ih => exact .lambda body outward formed latentBound
  | purePair left right ihLeft ihRight => exact .purePair (ihLeft more) (ihRight more)
  | pair left right ihLeft ihRight => exact .pair (ihLeft more) (ihRight more)
  | app function argument admitted ihFunction ihArgument => exact .app (ihFunction more) (ihArgument more) (admitted.trans more)
  | bind initializer body ihInit ihBody => exact .bind (ihInit more) (ihBody more)
  | branch condition yes no same ihCondition ihYes ihNo => exact .branch (ihCondition more) (ihYes more) (ihNo more) same
  | perform known admitted operand formed ih => exact .perform known (more admitted) (ih more) formed
  | handler body clauses capabilities coverage unique admitted table modes declarations ihBody ihDecl =>
      exact .handler body clauses capabilities coverage unique (admitted.trans more) table modes declarations
  | resume known resolved permission operand admitted formed ih => exact .resume known resolved permission (ih more) (admitted.trans more) formed
  | discard known resolved permission unprotected admitted => exact .discard known resolved permission unprotected (admitted.trans more)
  | cleanup callback body admitted ihCallback ihBody => exact .cleanup (ihCallback more) (ihBody more) (admitted.trans more)
  | resource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      exact .resource (ihInit more) body formed effectsBound (admitted.trans more) hidden
  | typed | annotated | unavailable | available | nil | cons => trivial

end Ash.OneShot.SourceDependencyAnnotations

#print axioms Ash.OneShot.SourceDependencyAnnotations.agree_left

#print axioms Ash.OneShot.SourceDependencyAnnotations.agree_right

#print axioms Ash.OneShot.SourceDependencyAnnotations.agree_extend

#print axioms Ash.OneShot.SourceDependencyAnnotations.opened_environment_agree

#print axioms Ash.OneShot.SourceDependencyAnnotations.Environment.extend_shadow

#print axioms Ash.OneShot.SourceDependencyAnnotations.Environment.extend_commute

#print axioms Ash.OneShot.SourceDependencyAnnotations.insert_extends

#print axioms Ash.OneShot.SourceDependencyAnnotations.extension_fresh

#print axioms Ash.OneShot.SourceDependencyAnnotations.insert_extension

#print axioms Ash.OneShot.SourceDependencyAnnotations.expression_environment_congr

#print axioms Ash.OneShot.SourceDependencyAnnotations.expression_world_weaken

#print axioms Ash.OneShot.SourceDependencyAnnotations.expression_extension

#print axioms Ash.OneShot.SourceDependencyAnnotations.expression_allowed_mono
