import DeclaredSources

/-! Hereditary source transport follows the existing shared source proofs.
    The additional induction cases retain full declarations in clause families
    under the same environment, world and contract transformations. -/
namespace Ash.OneShot.DeclaredSourceTransport
open ScopedExpressions ScopedExecution CoherentSourceTypes ProtectionContracts
open DeclaredSources (Expression Callable Body Offer Declarations)
open RecursiveRequirements (Requirements)

theorem expression_environment_congr
    (source : Expression operations policy contracts world allowed scope environment code result demand requirements)
    (agree : AgreeOn environment destination code.dependencies) :
    Expression operations policy contracts world allowed scope destination code result demand requirements := by
  induction source using Expression.rec
      (motive_2 := fun contracts world environment allowed code value row _ => ∀ destination,
        AgreeOn environment destination code.dependencies →
          Callable operations policy contracts world destination allowed code value row)
      (motive_3 := fun contracts world allowed scope environment code value header _ => ∀ destination,
        AgreeOn environment destination code.dependencies →
          Body operations policy contracts world allowed scope destination code value header)
      (motive_4 := fun contracts world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row _ => ∀ destination,
        AgreeOn environment destination (Syntax.without (.variable parameter) code.dependencies) →
          Offer operations policy contracts world destination allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row)
      (motive_5 := fun contracts world environment allowed effect answer clauses table _ => ∀ destination,
        AgreeOn environment destination clauses.dependencies →
          Declarations operations policy contracts world destination allowed effect answer clauses table)
      generalizing destination with
  | stable summary => exact .stable (CoherentSourceTypes.environment_congr summary agree)
  | callable summary ih => exact .callable (ih destination agree)
  | lambda body outward formed ih => exact .lambda (ih (agree_extend agree)) outward formed
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
      simp only [Environment.ports, agree_right agree name member]
  | resume known resolved permission operand admitted formed ih =>
      exact .resume known resolved permission (ih (fun name member => agree name (List.mem_cons_of_mem _ member))) admitted formed
  | discard known resolved permission unprotected admitted => exact .discard known resolved permission unprotected admitted
  | cleanup callback body admitted ihCallback ihBody =>
      exact .cleanup (ihCallback (agree_left agree)) (ihBody (agree_right agree)) admitted
  | resource initializer body formed effectsBound admitted outward ihInit ihBody =>
      exact .resource (ihInit (agree_left agree))
        (fun identity fresh => ihBody identity fresh destination
          (SourceCallableTransport.opened_environment_agree (agree_right agree))) formed effectsBound admitted outward
  | scopedResource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      exact .scopedResource (ihInit (agree_left agree))
        (fun identity fresh => ihBody identity fresh (SourceCallableTransport.opened_environment_agree (agree_right agree)))
        formed effectsBound admitted hidden
  | summaryUnit => exact .summaryUnit
  | summaryBoolean => exact .summaryBoolean
  | summaryInteger => exact .summaryInteger
  | summaryReference issued => exact .summaryReference issued
  | summaryVariable known formed =>
      rename_i destination agree
      exact .summaryVariable ((agree _ List.mem_cons_self).symm.trans known) formed
  | summaryPair left right ihLeft ihRight =>
      rename_i destination agree
      exact .summaryPair (ihLeft destination (agree_left agree)) (ihRight destination (agree_right agree))
  | summaryLambda body outward formed ih =>
      rename_i destination agree
      exact .summaryLambda (ih (agree_extend agree)) outward formed
  | summaryApp function argument admitted ihFunction ihArgument =>
      rename_i destination agree
      exact .summaryApp (ihFunction destination (agree_left agree)) (ihArgument destination (agree_right agree)) admitted
  | summaryBind initializer body ihInit ihBody =>
      rename_i destination agree
      exact .summaryBind (ihInit destination (agree_left agree)) (ihBody _ (agree_extend (agree_right agree)))
  | summaryBranch condition yes no ihCondition ihYes ihNo =>
      rename_i destination agree
      exact .summaryBranch (ihCondition destination (agree_left (agree_left agree)))
        (ihYes destination (agree_right (agree_left agree))) (ihNo destination (agree_right agree))
  | summaryPerform known admitted operand formed ih =>
      rename_i destination agree
      exact .summaryPerform known admitted (ih destination (agree_right agree)) formed
  | summaryCleanup callback body admitted ihCallback ihBody =>
      rename_i destination agree
      exact .summaryCleanup (ihCallback destination (agree_left agree)) (ihBody destination (agree_right agree)) admitted
  | summaryResource initializer body formed effectsBound admitted outward ihInit ihBody =>
      rename_i destination agree
      exact .summaryResource (ihInit destination (agree_left agree))
        (fun identity fresh => ihBody identity fresh destination (SourceCallableTransport.opened_environment_agree (agree_right agree)))
        formed effectsBound admitted outward
  | typed body rows ih =>
      rename_i destination agree
      exact .typed (ih agree) rows
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

theorem callable_environment_congr
    (source : Callable operations policy contracts world environment allowed code value row)
    (agree : AgreeOn environment destination code.dependencies) :
    Callable operations policy contracts world destination allowed code value row :=
  DeclaredSources.Callable.from_generic (CallableSources.environment_congr source.to_generic
    (fun _ _ _ _ _ _ _ _ body known => expression_environment_congr body known) agree)

theorem body_environment_congr
    (source : Body operations policy contracts world allowed scope environment code value header)
    (agree : AgreeOn environment destination code.dependencies) :
    Body operations policy contracts world allowed scope destination code value header := by
  cases source with
  | typed body rows => exact .typed (expression_environment_congr body agree) rows

theorem offer_environment_congr
    (source : Offer operations policy contracts world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row)
    (agree : AgreeOn environment destination (Syntax.without (.variable parameter) code.dependencies)) :
    Offer operations policy contracts world destination allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row := by
  cases source with
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface family =>
      apply Offer.available resumeInterface closeInterface
      intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
      exact body_environment_congr (family owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance) (agree_extend agree)

theorem declarations_environment_congr
    (source : Declarations operations policy contracts world environment allowed effect answer clauses table)
    (agree : AgreeOn environment destination clauses.dependencies) :
    Declarations operations policy contracts world destination allowed effect answer clauses table := by
  induction clauses using Clauses.rec (motive_1 := fun _ => True) generalizing table
  case nil => cases source; exact .nil
  case cons operation parameter binder body rest ihBody ihRest =>
    cases source with
    | cons known ordinary protectedMode rest =>
        have bodyAgree := fun name member => agree_left agree name (Syntax.mem_without.mpr ⟨member, by simp⟩)
        exact .cons known (offer_environment_congr ordinary bodyAgree) (offer_environment_congr protectedMode bodyAgree)
          (ihRest rest (agree_right agree))
  all_goals trivial

theorem expression_world_weaken
    (source : Expression operations policy contracts world allowed scope environment code result demand requirements)
    (larger : world ⊆ next) :
    Expression operations policy contracts next allowed scope environment code result demand requirements := by
  induction source using Expression.rec
      (motive_2 := fun contracts world environment allowed code value row _ => ∀ next, world ⊆ next →
        Callable operations policy contracts next environment allowed code value row)
      (motive_3 := fun contracts world allowed scope environment code value header _ => ∀ next, world ⊆ next →
        Body operations policy contracts next allowed scope environment code value header)
      (motive_4 := fun contracts world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row _ => ∀ next, world ⊆ next →
        Offer operations policy contracts next environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row)
      (motive_5 := fun contracts world environment allowed effect answer clauses table _ => ∀ next, world ⊆ next →
        Declarations operations policy contracts next environment allowed effect answer clauses table)
      generalizing next with
  | stable summary => exact .stable (summary_world_weaken summary larger)
  | callable summary ih => exact .callable (ih next larger)
  | lambda body outward formed ih => exact .lambda (ih larger) outward (ScopedPorts.in_world_mono formed larger)
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
  | resource initializer body formed effectsBound admitted outward ihInit ihBody =>
      exact .resource (ihInit larger)
        (fun identity fresh => ihBody identity (fun member => fresh (larger member)) (next ++ [identity])
          (ScopedExpressions.append_subset larger (List.Subset.refl _)))
        (ScopedPorts.in_world_mono formed larger) (effectsBound.trans larger) admitted
        (fun identity fresh => outward identity (fun member => fresh (larger member)))
  | scopedResource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      exact .scopedResource (ihInit larger)
        (fun identity fresh => ihBody identity (fun member => fresh (larger member))
          (ScopedExpressions.append_subset larger (List.Subset.refl _)))
        (ScopedPorts.in_world_mono formed larger) (effectsBound.trans larger) admitted
        (fun identity fresh => hidden identity (fun member => fresh (larger member)))
  | summaryUnit =>
      rename_i next larger
      exact .summaryUnit
  | summaryBoolean =>
      rename_i next larger
      exact .summaryBoolean
  | summaryInteger =>
      rename_i next larger
      exact .summaryInteger
  | summaryReference issued =>
      rename_i next larger
      exact .summaryReference (larger issued)
  | summaryVariable known formed =>
      rename_i next larger
      exact .summaryVariable known (ScopedPorts.in_world_mono formed larger)
  | summaryPair left right ihLeft ihRight =>
      rename_i next larger
      exact .summaryPair (ihLeft next larger) (ihRight next larger)
  | summaryLambda body outward formed ih =>
      rename_i next larger
      exact .summaryLambda (ih larger) outward (ScopedPorts.in_world_mono formed larger)
  | summaryApp function argument admitted ihFunction ihArgument =>
      rename_i next larger
      exact .summaryApp (ihFunction next larger) (ihArgument next larger) admitted
  | summaryBind initializer body ihInit ihBody =>
      rename_i next larger
      exact .summaryBind (ihInit next larger) (ihBody next larger)
  | summaryBranch condition yes no ihCondition ihYes ihNo =>
      rename_i next larger
      exact .summaryBranch (ihCondition next larger) (ihYes next larger) (ihNo next larger)
  | summaryPerform known admitted operand formed ih =>
      rename_i next larger
      exact .summaryPerform known admitted (ih next larger) (ScopedPorts.in_world_mono formed larger)
  | summaryCleanup callback body admitted ihCallback ihBody =>
      rename_i next larger
      exact .summaryCleanup (ihCallback next larger) (ihBody next larger) admitted
  | summaryResource initializer body formed effectsBound admitted outward ihInit ihBody =>
      rename_i next larger

      exact .summaryResource (ihInit next larger)
        (fun identity fresh => ihBody identity (fun member => fresh (larger member))
          (next ++ [identity]) (ScopedExpressions.append_subset larger (List.Subset.refl _)))
        (ScopedPorts.in_world_mono formed larger) (effectsBound.trans larger) admitted
        (fun identity fresh => outward identity (fun member => fresh (larger member)))
  | typed body rows ih =>
      rename_i next larger
      exact .typed (ih larger) rows
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

theorem callable_world_weaken
    (source : Callable operations policy contracts world environment allowed code value row)
    (larger : world ⊆ next) :
    Callable operations policy contracts next environment allowed code value row :=
  DeclaredSources.Callable.from_generic (CallableSources.summary_world_weaken source.to_generic
    (fun _ _ _ _ _ _ _ _ body grows => expression_world_weaken body grows) larger)

theorem body_world_weaken
    (source : Body operations policy contracts world allowed scope environment code value header)
    (larger : world ⊆ next) : Body operations policy contracts next allowed scope environment code value header := by
  cases source with
  | typed body rows => exact .typed (expression_world_weaken body larger) rows

theorem offer_world_weaken
    (source : Offer operations policy contracts world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row)
    (larger : world ⊆ next) :
    Offer operations policy contracts next environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row := by
  cases source with
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface family =>
      apply Offer.available resumeInterface closeInterface
      intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
      exact body_world_weaken (family owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance) larger

theorem declarations_world_weaken
    (source : Declarations operations policy contracts world environment allowed effect answer clauses table)
    (larger : world ⊆ next) :
    Declarations operations policy contracts next environment allowed effect answer clauses table := by
  induction clauses using Clauses.rec (motive_1 := fun _ => True) generalizing table
  case nil => cases source; exact .nil
  case cons operation parameter binder body rest ihBody ihRest =>
    cases source with
    | cons known ordinary protectedMode rest =>
        exact .cons known (offer_world_weaken ordinary larger) (offer_world_weaken protectedMode larger) (ihRest rest)
  all_goals trivial

theorem expression_extension
    (source : Expression operations policy contracts world allowed scope environment code result demand requirements)
    (extension : contracts.Extends larger) :
    Expression operations policy larger world allowed scope environment code result demand requirements := by
  induction source using Expression.rec
      (motive_2 := fun contracts world environment allowed code value row _ => ∀ larger, contracts.Extends larger →
        Callable operations policy larger world environment allowed code value row)
      (motive_3 := fun contracts world allowed scope environment code value header _ => ∀ larger, contracts.Extends larger →
        Body operations policy larger world allowed scope environment code value header)
      (motive_4 := fun contracts world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row _ => ∀ larger, contracts.Extends larger →
        Offer operations policy larger world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row)
      (motive_5 := fun contracts world environment allowed effect answer clauses table _ => ∀ larger, contracts.Extends larger →
        Declarations operations policy larger world environment allowed effect answer clauses table)
      generalizing larger with
  | stable summary => exact .stable summary
  | callable summary ih => exact .callable (ih larger extension)
  | lambda body outward formed ih => exact .lambda (ih extension) outward formed
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
  | resource initializer body formed effectsBound admitted outward ihInit ihBody => exact .resource (ihInit extension) (fun identity fresh => ihBody identity fresh larger extension) formed effectsBound admitted outward
  | scopedResource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      exact .scopedResource (ihInit extension) (fun identity fresh => ihBody identity fresh extension) formed effectsBound admitted hidden
  | summaryUnit =>
      rename_i larger extension
      exact .summaryUnit
  | summaryBoolean =>
      rename_i larger extension
      exact .summaryBoolean
  | summaryInteger =>
      rename_i larger extension
      exact .summaryInteger
  | summaryReference issued =>
      rename_i larger extension
      exact .summaryReference issued
  | summaryVariable known formed =>
      rename_i larger extension
      exact .summaryVariable known formed
  | summaryPair left right ihLeft ihRight =>
      rename_i larger extension
      exact .summaryPair (ihLeft larger extension) (ihRight larger extension)
  | summaryLambda body outward formed ih =>
      rename_i larger extension
      exact .summaryLambda (ih extension) outward formed
  | summaryApp function argument admitted ihFunction ihArgument =>
      rename_i larger extension
      exact .summaryApp (ihFunction larger extension) (ihArgument larger extension) admitted
  | summaryBind initializer body ihInit ihBody =>
      rename_i larger extension
      exact .summaryBind (ihInit larger extension) (ihBody larger extension)
  | summaryBranch condition yes no ihCondition ihYes ihNo =>
      rename_i larger extension
      exact .summaryBranch (ihCondition larger extension) (ihYes larger extension) (ihNo larger extension)
  | summaryPerform known admitted operand formed ih =>
      rename_i larger extension
      exact .summaryPerform known admitted (ih larger extension) formed
  | summaryCleanup callback body admitted ihCallback ihBody =>
      rename_i larger extension
      exact .summaryCleanup (ihCallback larger extension) (ihBody larger extension) admitted
  | summaryResource initializer body formed effectsBound admitted outward ihInit ihBody =>
      rename_i larger extension
      exact .summaryResource (ihInit larger extension) (fun identity fresh => ihBody identity fresh larger extension) formed effectsBound admitted outward
  | typed body rows ih =>
      rename_i larger extension
      exact .typed (ih extension) rows
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface family ih =>
      rename_i larger extension
      apply Offer.available resumeInterface closeInterface
      intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
      exact ih owner contract (SourceClauseDeclarations.extension_fresh extension fresh)
        inputSame answerSame resumeSame closeSame heldSame balance _ (SourceClauseDeclarations.insert_extension extension)
  | nil => exact .nil
  | cons known ordinary protectedMode rest ihOrdinary ihProtected ihRest =>
      rename_i larger extension
      exact .cons known (ihOrdinary larger extension) (ihProtected larger extension) (ihRest larger extension)

theorem callable_extension
    (source : Callable operations policy contracts world environment allowed code value row)
    (extension : contracts.Extends larger) :
    Callable operations policy larger world environment allowed code value row :=
  DeclaredSources.Callable.from_generic (CallableSources.map_body source.to_generic
    (fun _ _ _ _ _ _ _ body => expression_extension body extension))

theorem body_extension
    (source : Body operations policy contracts world allowed scope environment code value header)
    (extension : contracts.Extends larger) : Body operations policy larger world allowed scope environment code value header := by
  cases source with
  | typed body rows => exact .typed (expression_extension body extension) rows

theorem offer_extension
    (source : Offer operations policy contracts world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row)
    (extension : contracts.Extends larger) :
    Offer operations policy larger world environment allowed parameter binder argument input answer resumeEffects closeEffects code held disposes row := by
  cases source with
  | unavailable => exact .unavailable
  | available resumeInterface closeInterface family =>
      apply Offer.available resumeInterface closeInterface
      intro owner contract fresh inputSame answerSame resumeSame closeSame heldSame balance
      exact body_extension
        (family owner contract (SourceClauseDeclarations.extension_fresh extension fresh)
          inputSame answerSame resumeSame closeSame heldSame balance)
        (SourceClauseDeclarations.insert_extension extension)

theorem declarations_extension
    (source : Declarations operations policy contracts world environment allowed effect answer clauses table)
    (extension : contracts.Extends larger) :
    Declarations operations policy larger world environment allowed effect answer clauses table := by
  induction clauses using Clauses.rec (motive_1 := fun _ => True) generalizing table
  case nil => cases source; exact .nil
  case cons operation parameter binder body rest ihBody ihRest =>
    cases source with
    | cons known ordinary protectedMode rest =>
        exact .cons known (offer_extension ordinary extension) (offer_extension protectedMode extension) (ihRest rest)
  all_goals trivial

theorem expression_allowed_mono
    (source : Expression operations policy contracts world allowed scope environment code result demand requirements)
    (more : allowed ⊆ destination) :
    Expression operations policy contracts world destination scope environment code result demand requirements := by
  induction source using Expression.rec (motive_2 := fun _ _ _ _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ _ _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => True)
      (motive_5 := fun _ _ _ _ _ _ _ _ _ => True) generalizing destination with
  | stable summary => exact .stable (CoherentSourceTypes.allowed_mono summary more)
  | callable summary ih => exact .callable (DeclaredSources.Callable.from_generic (CallableSources.allowed_mono summary.to_generic more))
  | lambda body outward formed ih => exact .lambda body outward formed
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
  | resource initializer body formed effectsBound admitted outward ihInit ihBody =>
      exact .resource (ihInit more) body formed effectsBound (admitted.trans more) outward
  | scopedResource initializer body formed effectsBound admitted hidden ihInit ihBody =>
      exact .scopedResource (ihInit more) body formed effectsBound (admitted.trans more) hidden
  | _ => intros; trivial

end Ash.OneShot.DeclaredSourceTransport
#print axioms Ash.OneShot.DeclaredSourceTransport.expression_environment_congr
#print axioms Ash.OneShot.DeclaredSourceTransport.callable_environment_congr
#print axioms Ash.OneShot.DeclaredSourceTransport.body_environment_congr
#print axioms Ash.OneShot.DeclaredSourceTransport.offer_environment_congr
#print axioms Ash.OneShot.DeclaredSourceTransport.declarations_environment_congr

#print axioms Ash.OneShot.DeclaredSourceTransport.expression_world_weaken
#print axioms Ash.OneShot.DeclaredSourceTransport.callable_world_weaken
#print axioms Ash.OneShot.DeclaredSourceTransport.body_world_weaken
#print axioms Ash.OneShot.DeclaredSourceTransport.offer_world_weaken
#print axioms Ash.OneShot.DeclaredSourceTransport.declarations_world_weaken

#print axioms Ash.OneShot.DeclaredSourceTransport.expression_extension
#print axioms Ash.OneShot.DeclaredSourceTransport.callable_extension
#print axioms Ash.OneShot.DeclaredSourceTransport.body_extension
#print axioms Ash.OneShot.DeclaredSourceTransport.offer_extension
#print axioms Ash.OneShot.DeclaredSourceTransport.declarations_extension

#print axioms Ash.OneShot.DeclaredSourceTransport.expression_allowed_mono
