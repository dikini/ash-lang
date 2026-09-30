import SourceAnnotatedContexts

/-! Reuse the existing source transport induction with finite annotated
nodes. Environment agreement, resource-world growth and contract extension keep
the chosen hints and closure checks unchanged. -/
namespace Ash.OneShot.SourceAnnotatedSources
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceAnnotatedCode (Term)
open RecursiveRequirements (Requirements)
open SourcePlannedTyping (Value Environment Operations Contract Contracts AgreeOn agree_left agree_right agree_extend
  opened_environment_agree insert_extends extension_fresh insert_extension)

theorem expression_environment_congr
    (source : Expression operations policy contracts world allowed scope environment code result demand requirements dependencies)
    (agree : AgreeOn environment destination code.erase.dependencies) :
    Expression operations policy contracts world allowed scope destination code result demand requirements dependencies := by
  induction source using Expression.rec
      (motive_2 := fun contracts world allowed scope environment code result demand requirements _ checking _ => ∀ destination,
        AgreeOn environment destination code.erase.dependencies →
          Node operations policy contracts world allowed scope destination code result demand requirements checking)
      (motive_3 := fun contracts world allowed scope environment code value header _ dependencies _ => ∀ destination,
        AgreeOn environment destination code.erase.dependencies →
          Body operations policy contracts world allowed scope destination code value header dependencies)
      (motive_4 := fun contracts world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row _ dependencies _ => ∀ destination,
        AgreeOn environment destination (Syntax.without (.variable parameter) code.erase.dependencies) →
          Offer operations policy contracts world destination allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row dependencies)
      (motive_5 := fun contracts world environment allowed effect answer clauses table _ dependencies _ => ∀ destination,
        AgreeOn environment destination clauses.erase.dependencies →
          Declarations operations policy contracts world destination allowed effect answer clauses table dependencies)
      generalizing destination with
  | checked hint closed node ih => exact .checked hint closed (ih destination agree)
  | unit =>
      rename_i destination agree
      exact .unit
  | boolean =>
      rename_i destination agree
      exact .boolean
  | integer =>
      rename_i destination agree
      exact .integer
  | reference issued =>
      rename_i destination agree
      exact .reference issued
  | «variable» known formed =>
      rename_i destination agree
      exact .variable ((agree _ List.mem_cons_self).symm.trans known) formed
  | lambda body outward formed latentBound ih =>
      rename_i destination agree
      exact .lambda (ih (agree_extend agree)) outward formed latentBound
  | purePair left right ihLeft ihRight =>
      rename_i destination agree
      exact .purePair (ihLeft (agree_left agree)) (ihRight (agree_right agree))
  | pair left right ihLeft ihRight =>
      rename_i destination agree
      exact .pair (ihLeft (agree_left agree)) (ihRight (agree_right agree))
  | app function argument admitted ihFunction ihArgument =>
      rename_i destination agree
      exact .app (ihFunction (agree_left agree)) (ihArgument (agree_right agree)) admitted
  | bind initializer body ihInit ihBody =>
      rename_i destination agree
      exact .bind (ihInit (agree_left agree)) (ihBody (agree_extend (agree_right agree)))
  | branch condition yes no same ihCondition ihYes ihNo =>
      rename_i destination agree
      exact .branch (ihCondition (agree_left (agree_left agree)))
        (ihYes (agree_right (agree_left agree))) (ihNo (agree_right agree)) same
  | perform known admitted operand formed ih =>
      rename_i destination agree
      exact .perform known admitted (ih (agree_right agree)) formed
  | handler body clauses capabilities coverage unique admitted table modes declarations ihBody ihDecl =>
      rename_i destination agree
      apply Node.handler (ihBody (agree_right (agree_left agree))) _ capabilities coverage unique admitted table modes
        (ihDecl destination (agree_right agree))
      apply ScopedPorts.clauses_environment_congr clauses
      intro name member
      simp only [CoherentSourceTypes.Environment.ports, SourceDependencyAnnotations.Environment.erase, Environment.erase, agree_right agree name member]
  | resume known resolved permission operand admitted formed ih =>
      rename_i destination agree
      exact .resume known resolved permission (ih (fun name member => agree name (List.mem_cons_of_mem _ member))) admitted formed
  | discard known resolved permission unprotected admitted =>
      rename_i destination agree
      exact .discard known resolved permission unprotected admitted
  | cleanup callback body admitted ihCallback ihBody =>
      rename_i destination agree
      exact .cleanup (ihCallback (agree_left agree)) (ihBody (agree_right agree)) admitted
  | resource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      rename_i destination agree
      exact .resource (ihInit (agree_left agree))
        (fun identity fresh => ihBody identity fresh (by simpa only [Term.erase_instantiate] using opened_environment_agree (agree_right agree)))
        formed effectsBound admitted hidden
  | typed body rows closingRows ih =>
      rename_i destination agree
      exact .typed (ih agree) rows closingRows
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
      (motive_2 := fun contracts world allowed scope environment code result demand requirements _ checking _ => ∀ next, world ⊆ next →
        Node operations policy contracts next allowed scope environment code result demand requirements checking)
      (motive_3 := fun contracts world allowed scope environment code value header _ dependencies _ => ∀ next, world ⊆ next →
        Body operations policy contracts next allowed scope environment code value header dependencies)
      (motive_4 := fun contracts world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row _ dependencies _ => ∀ next, world ⊆ next →
        Offer operations policy contracts next environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row dependencies)
      (motive_5 := fun contracts world environment allowed effect answer clauses table _ dependencies _ => ∀ next, world ⊆ next →
        Declarations operations policy contracts next environment allowed effect answer clauses table dependencies)
      generalizing next with
  | checked hint closed node ih => exact .checked hint closed (ih next larger)
  | unit =>
      rename_i next larger
      exact .unit
  | boolean =>
      rename_i next larger
      exact .boolean
  | integer =>
      rename_i next larger
      exact .integer
  | reference issued =>
      rename_i next larger
      exact .reference (larger issued)
  | «variable» known formed =>
      rename_i next larger
      exact .variable known (ScopedPorts.in_world_mono formed larger)
  | lambda body outward formed latentBound ih =>
      rename_i next larger
      exact .lambda (ih larger) outward (ScopedPorts.in_world_mono formed larger) latentBound
  | purePair left right ihLeft ihRight =>
      rename_i next larger
      exact .purePair (ihLeft larger) (ihRight larger)
  | pair left right ihLeft ihRight =>
      rename_i next larger
      exact .pair (ihLeft larger) (ihRight larger)
  | app function argument admitted ihFunction ihArgument =>
      rename_i next larger
      exact .app (ihFunction larger) (ihArgument larger) admitted
  | bind initializer body ihInit ihBody =>
      rename_i next larger
      exact .bind (ihInit larger) (ihBody larger)
  | branch condition yes no same ihCondition ihYes ihNo =>
      rename_i next larger
      exact .branch (ihCondition larger) (ihYes larger) (ihNo larger) same
  | perform known admitted operand formed ih =>
      rename_i next larger
      exact .perform known admitted (ih larger) (ScopedPorts.in_world_mono formed larger)
  | handler body clauses capabilities coverage unique admitted table modes declarations ihBody ihDecl =>
      rename_i next larger
      exact .handler (ihBody larger) (ScopedPorts.clauses_world_weaken clauses larger) capabilities coverage unique admitted table modes (ihDecl next larger)
  | resume known resolved permission operand admitted formed ih =>
      rename_i next larger
      exact .resume known resolved permission (ih larger) admitted (ScopedPorts.in_world_mono formed larger)
  | discard known resolved permission unprotected admitted =>
      rename_i next larger
      exact .discard known resolved permission unprotected admitted
  | cleanup callback body admitted ihCallback ihBody =>
      rename_i next larger
      exact .cleanup (ihCallback larger) (ihBody larger) admitted
  | resource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      rename_i next larger
      exact .resource (ihInit larger)
        (fun identity fresh => ihBody identity (fun member => fresh (larger member))
          (ScopedExpressions.append_subset larger (List.Subset.refl _)))
        (ScopedPorts.in_world_mono formed larger) (effectsBound.trans larger) admitted
        (fun identity fresh => hidden identity (fun member => fresh (larger member)))
  | typed body rows closingRows ih =>
      rename_i next larger
      exact .typed (ih larger) rows closingRows
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
      (motive_2 := fun contracts world allowed scope environment code result demand requirements _ checking _ => ∀ larger, contracts.Extends larger →
        Node operations policy larger world allowed scope environment code result demand requirements checking)
      (motive_3 := fun contracts world allowed scope environment code value header _ dependencies _ => ∀ larger, contracts.Extends larger →
        Body operations policy larger world allowed scope environment code value header dependencies)
      (motive_4 := fun contracts world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row _ dependencies _ => ∀ larger, contracts.Extends larger →
        Offer operations policy larger world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row dependencies)
      (motive_5 := fun contracts world environment allowed effect answer clauses table _ dependencies _ => ∀ larger, contracts.Extends larger →
        Declarations operations policy larger world environment allowed effect answer clauses table dependencies)
      generalizing larger with
  | checked hint closed node ih => exact .checked hint closed (ih larger extension)
  | unit =>
      rename_i larger extension
      exact .unit
  | boolean =>
      rename_i larger extension
      exact .boolean
  | integer =>
      rename_i larger extension
      exact .integer
  | reference issued =>
      rename_i larger extension
      exact .reference issued
  | «variable» known formed =>
      rename_i larger extension
      exact .variable known formed
  | lambda body outward formed latentBound ih =>
      rename_i larger extension
      exact .lambda (ih extension) outward formed latentBound
  | purePair left right ihLeft ihRight =>
      rename_i larger extension
      exact .purePair (ihLeft extension) (ihRight extension)
  | pair left right ihLeft ihRight =>
      rename_i larger extension
      exact .pair (ihLeft extension) (ihRight extension)
  | app function argument admitted ihFunction ihArgument =>
      rename_i larger extension
      exact .app (ihFunction extension) (ihArgument extension) admitted
  | bind initializer body ihInit ihBody =>
      rename_i larger extension
      exact .bind (ihInit extension) (ihBody extension)
  | branch condition yes no same ihCondition ihYes ihNo =>
      rename_i larger extension
      exact .branch (ihCondition extension) (ihYes extension) (ihNo extension) same
  | perform known admitted operand formed ih =>
      rename_i larger extension
      exact .perform known admitted (ih extension) formed
  | handler body clauses capabilities coverage unique admitted table modes declarations ihBody ihDecl =>
      rename_i larger extension
      exact .handler (ihBody extension) clauses capabilities coverage unique admitted table modes (ihDecl larger extension)
  | resume known resolved permission operand admitted formed ih =>
      rename_i larger extension
      exact .resume (extension _ _ known) resolved permission (ih extension) admitted formed
  | discard known resolved permission unprotected admitted =>
      rename_i larger extension
      exact .discard (extension _ _ known) resolved permission unprotected admitted
  | cleanup callback body admitted ihCallback ihBody =>
      rename_i larger extension
      exact .cleanup (ihCallback extension) (ihBody extension) admitted
  | resource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      rename_i larger extension
      exact .resource (ihInit extension) (fun identity fresh => ihBody identity fresh extension) formed effectsBound admitted hidden
  | typed body rows closingRows ih =>
      rename_i larger extension
      exact .typed (ih extension) rows closingRows
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
      (motive_2 := fun contracts world allowed scope environment code result demand requirements _ checking _ => ∀ destination, allowed ⊆ destination →
        Node operations policy contracts world destination scope environment code result demand requirements checking)
      (motive_3 := fun _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_5 := fun _ _ _ _ _ _ _ _ _ _ _ => True) generalizing destination with
  | checked hint closed node ih => exact .checked hint closed (ih destination more)
  | unit =>
      rename_i destination more
      exact .unit
  | boolean =>
      rename_i destination more
      exact .boolean
  | integer =>
      rename_i destination more
      exact .integer
  | reference issued =>
      rename_i destination more
      exact .reference issued
  | «variable» known formed =>
      rename_i destination more
      exact .variable known formed
  | lambda body outward formed latentBound ih =>
      rename_i destination more
      exact .lambda body outward formed latentBound
  | purePair left right ihLeft ihRight =>
      rename_i destination more
      exact .purePair (ihLeft more) (ihRight more)
  | pair left right ihLeft ihRight =>
      rename_i destination more
      exact .pair (ihLeft more) (ihRight more)
  | app function argument admitted ihFunction ihArgument =>
      rename_i destination more
      exact .app (ihFunction more) (ihArgument more) (admitted.trans more)
  | bind initializer body ihInit ihBody =>
      rename_i destination more
      exact .bind (ihInit more) (ihBody more)
  | branch condition yes no same ihCondition ihYes ihNo =>
      rename_i destination more
      exact .branch (ihCondition more) (ihYes more) (ihNo more) same
  | perform known admitted operand formed ih =>
      rename_i destination more
      exact .perform known (more admitted) (ih more) formed
  | handler body clauses capabilities coverage unique admitted table modes declarations ihBody ihDecl =>
      rename_i destination more
      exact .handler body clauses capabilities coverage unique (admitted.trans more) table modes declarations
  | resume known resolved permission operand admitted formed ih =>
      rename_i destination more
      exact .resume known resolved permission (ih more) (admitted.trans more) formed
  | discard known resolved permission unprotected admitted =>
      rename_i destination more
      exact .discard known resolved permission unprotected (admitted.trans more)
  | cleanup callback body admitted ihCallback ihBody =>
      rename_i destination more
      exact .cleanup (ihCallback more) (ihBody more) (admitted.trans more)
  | resource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      rename_i destination more
      exact .resource (ihInit more) body formed effectsBound (admitted.trans more) hidden
  | typed | unavailable | available | nil | cons => trivial

end Ash.OneShot.SourceAnnotatedSources

#print axioms Ash.OneShot.SourceAnnotatedSources.expression_environment_congr

#print axioms Ash.OneShot.SourceAnnotatedSources.expression_world_weaken

#print axioms Ash.OneShot.SourceAnnotatedSources.expression_extension

#print axioms Ash.OneShot.SourceAnnotatedSources.expression_allowed_mono
