import CoreCallableRestoredSupport

/-! Raw admission and scalar accounting transport across the concrete restored
row/context delta. Source authentication and actual receiver checking remain
separate obligations of the restoration consumer. -/
namespace Ash.OneShot.CoreCallableRestoredSupport
open ScopedExpressions ProtectionContracts
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual

 theorem RestoredContext.builtin
    (delta : RestoredContext before after)
    (found : select effect operation before = some (.builtin identity)) :
    select effect operation after = some (.builtin identity) := by
  have same := congrArg (select effect operation) delta.complete
  rw [select_eraseContextSupport, select_eraseContextSupport, found] at same
  cases next : select effect operation after with
  | none => rw [next] at same; cases same
  | some selected => cases selected with
    | builtin nextIdentity => rw [next] at same; cases same; rfl
    | handler captured tail contract modes => rw [next] at same; cases same

 theorem RestoredContext.callback (delta : RestoredContext before after) (mode : LexicalUnwind.UseMode) :
    RestoredContext (before.callback mode) (after.callback mode) := by
  cases mode
  · exact .normal delta
  · exact .unwinding delta

end Ash.OneShot.CoreCallableRestoredSupport

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.SourceAdmission
open Ash.OneShot.CoreCallableRestoredSupport
open SourceDependencyChecks.Lexical (ReturnHints)
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

 theorem Code.restore_support
    {checking : SourcePlanSignatures.Signature dependencies} {rows nextRows : Rows checking}
    {hints : ReturnHints scope} {context nextContext : Context hints}
    (checked : Code outward actions budget phases world installations rows context)
    (rowsSame : SupportOnly rows nextRows)
    (delta : RestoredContext context nextContext) :
    Code outward actions budget phases world installations nextRows nextContext := by
  revert nextRows nextContext
  apply Code.rec
    (motive_1 := fun actions budget phases world installations {dependencies checking} rows {scope hints} context _ =>
      ∀ (nextRows : Rows checking) (nextContext : Context hints), SupportOnly rows nextRows → RestoredContext context nextContext →
      Code outward actions budget phases world installations nextRows nextContext)
    (motive_2 := fun actions budget phases world installations {scope outsideScope hints external} context outside input output _ =>
      ∀ (nextContext : Context hints) (nextOutside : Context external), RestoredContext context nextContext → RestoredContext outside nextOutside →
      Pending outward actions budget phases world installations nextContext nextOutside input output)
    (t := checked)
  · intros
    rename_i nextRows nextContext rowsSame delta
    cases nextRows; exact .pure
  · intros
    rename_i found nextRows nextContext rowsSame delta
    cases nextRows; exact .builtin (delta.builtin found)
  · intros
    rename_i cut guarded callbacks ownerBound cleanupBudget family bodies bodyRows declarations declarationRows selected terminal requiredRights retained body ihCallbacks ihRetained ihBody nextRows nextContext rowsSame delta
    cases nextRows
    obtain ⟨nextCaptured, nextTail, nextCut, capturedDelta, tailDelta⟩ := delta.cut cut
    obtain ⟨nextBodyRows, nextSelected, bodySame⟩ := CapturedClauseRows.restore_support selected capturedDelta
    obtain ⟨nextDeclarations, declarationsSame, nextTerminal⟩ := capturedDelta.terminal terminal
    refine .request nextCut guarded (fun disposing => ihCallbacks disposing _ _ capturedDelta (.closing tailDelta))
      ownerBound (CoreCallableRestoredSupport.RequestBudget.restore_support cleanupBudget delta) nextSelected nextTerminal requiredRights
      (ihRetained _ _ delta .nil) ?_
    intro owner demand fresh absent
    apply ihBody owner demand fresh
    · simpa only [delta.ticketNames] using absent
    · exact bodySame owner
    · exact .live capturedDelta tailDelta
  · intros
    rename_i located known permission available shape restored ih nextRows nextContext rowsSame delta
    cases nextRows
    rename_i front captured tail
    obtain ⟨nextFront, nextLive, rfl, frontDelta, liveDelta⟩ := delta.split front (.live captured tail)
    cases liveDelta with
    | live capturedDelta tailDelta =>
      refine .resume located known permission available ?_ (ih _ _ (capturedDelta.append (frontDelta.append (.spent tailDelta))) .nil)
      simpa only [ResumeShape, frontDelta.closing_same] using shape
  · intros
    rename_i located known permission available unprotected abandoned waiting ihAbandoned ihWaiting nextRows nextContext rowsSame delta
    cases nextRows
    rename_i front captured tail
    obtain ⟨nextFront, nextLive, rfl, frontDelta, liveDelta⟩ := delta.split front (.live captured tail)
    cases liveDelta with
    | live capturedDelta tailDelta =>
      exact .dispose located known permission available unprotected
        (ihAbandoned _ _ capturedDelta (.closing (frontDelta.append (.spent tailDelta))))
        (ihWaiting _ _ (frontDelta.append (.spent tailDelta)) .nil)
  · intros
    rename_i first second ihFirst ihSecond nextRows nextContext rowsSame delta
    cases nextRows with
    | sequence nextFirst nextSecond =>
      unfold SupportOnly at rowsSame
      simp only [eraseSupportBounds] at rowsSame
      injection rowsSame
      exact .sequence (ihFirst _ _ (by assumption) (.plain (by assumption) delta)) (ihSecond _ _ (by assumption) delta)
  · intros
    rename_i first second ihFirst ihSecond nextRows nextContext rowsSame delta
    cases nextRows with
    | choice nextFirst nextSecond =>
      unfold SupportOnly at rowsSame
      simp only [eraseSupportBounds] at rowsSame
      injection rowsSame
      exact .choice (ihFirst _ _ (by assumption) delta) (ihSecond _ _ (by assumption) delta)
  · intros
    rename_i body ih nextRows nextContext rowsSame delta
    cases nextRows with
    | handler nextDeclarations nextBody =>
      unfold SupportOnly at rowsSame
      simp only [eraseSupportBounds] at rowsSame
      injection rowsSame
      exact .handler (fun activation fresh => ih activation fresh _ _ (by assumption) (.handler (by assumption) delta))
  · intros
    rename_i body callback ihBody ihCallback nextRows nextContext rowsSame delta
    cases nextRows with
    | cleanup nextLatent nextCallback nextBody =>
      unfold SupportOnly at rowsSame
      simp only [eraseSupportBounds] at rowsSame
      injection rowsSame
      subst_vars
      exact .cleanup (ihBody _ _ (by assumption) (.cleanup (by assumption) delta)) (ihCallback _ _ (by assumption) (.normal delta))
  · intros
    rename_i body ih nextRows nextContext rowsSame delta
    cases nextRows with
    | resource nextBody =>
      unfold SupportOnly at rowsSame
      simp only [eraseSupportBounds] at rowsSame
      injection rowsSame
      rename_i bodySame
      exact .resource (fun identity fresh => ih identity fresh _ _ (congrFun bodySame identity) (.cell delta))
  · intros
    rename_i nextContext nextOutside delta outsideDelta
    cases delta; exact .nil
  · intros
    rename_i code tail ihCode ihTail nextContext nextOutside delta outsideDelta
    cases delta with
    | plain rowsSame restDelta =>
      exact .plain (ihCode _ _ rowsSame (restDelta.append outsideDelta)) (ihTail _ _ restDelta outsideDelta)
  · intros
    rename_i tail ih nextContext nextOutside delta outsideDelta
    cases delta with
      | plain rowsSame restDelta => exact .skipped (ih _ _ restDelta outsideDelta)
  · intros
    rename_i tail ih nextContext nextOutside delta outsideDelta
    cases delta with
      | handler rowsSame restDelta => exact .handler (ih _ _ restDelta outsideDelta)
  · intros
    rename_i tail ih nextContext nextOutside delta outsideDelta
    cases delta with
      | cell restDelta => exact .cell (ih _ _ restDelta outsideDelta)
  · intros
    rename_i callback tail ihCallback ihTail nextContext nextOutside delta outsideDelta
    cases delta with
      | cleanup rowsSame restDelta => exact .cleanup (ihCallback _ _ rowsSame ((restDelta.append outsideDelta).callback _)) (ihTail _ _ restDelta outsideDelta)
  · intros
    rename_i tail ih nextContext nextOutside delta outsideDelta
    cases delta with
      | normal restDelta => exact .normal (ih _ _ restDelta outsideDelta)
  · intros
    rename_i tail ih nextContext nextOutside delta outsideDelta
    cases delta with
      | unwinding restDelta => exact .unwinding (ih _ _ restDelta outsideDelta)
  · intros
    rename_i tail ih nextContext nextOutside delta outsideDelta
    cases delta with
      | closing restDelta => exact .closing (ih _ _ restDelta outsideDelta)
  · intros
    rename_i tail ih nextContext nextOutside delta outsideDelta
    cases delta with
      | retiring restDelta => exact .retiring (ih _ _ restDelta outsideDelta)
  · intros
    rename_i saved tail ihSaved ihTail nextContext nextOutside delta outsideDelta
    cases delta with
      | live savedDelta restDelta => exact .live (ihSaved _ _ savedDelta (restDelta.append outsideDelta)) (ihTail _ _ restDelta outsideDelta)
  · intros
    rename_i saved tail ihSaved ihTail nextContext nextOutside delta outsideDelta
    cases delta with
      | live savedDelta restDelta => exact .opening (ihSaved _ _ savedDelta (.retiring (restDelta.append outsideDelta))) (ihTail _ _ restDelta outsideDelta)
  · intros
    rename_i tail ih nextContext nextOutside delta outsideDelta
    cases delta with
      | spent restDelta => exact .spent (ih _ _ restDelta outsideDelta)
 theorem Pending.restore_support
    {hints : ReturnHints scope} {external : ReturnHints outsideScope}
    {context nextContext : Context hints} {outside nextOutside : Context external}
    (checked : Pending outward actions budget phases world installations context outside input output)
    (delta : RestoredContext context nextContext) (outsideDelta : RestoredContext outside nextOutside) :
    Pending outward actions budget phases world installations nextContext nextOutside input output := by
  revert nextContext nextOutside
  apply Pending.rec
    (motive_1 := fun actions budget phases world installations {dependencies checking} rows {scope hints} context _ => True)
    (motive_2 := fun actions budget phases world installations {scope outsideScope hints external} context outside input output _ =>
      ∀ (nextContext : Context hints) (nextOutside : Context external), RestoredContext context nextContext → RestoredContext outside nextOutside →
      Pending outward actions budget phases world installations nextContext nextOutside input output)
    (t := checked)
  all_goals try (intros; trivial)
  · intros
    rename_i nextContext nextOutside delta outsideDelta
    cases delta; exact .nil
  · intros
    rename_i code tail ihCode ihTail nextContext nextOutside delta outsideDelta
    cases delta with
    | plain rowsSame restDelta =>
      exact .plain (code.restore_support rowsSame (restDelta.append outsideDelta)) (ihTail _ _ restDelta outsideDelta)
  · intros
    rename_i tail ih nextContext nextOutside delta outsideDelta
    cases delta with
      | plain rowsSame restDelta => exact .skipped (ih _ _ restDelta outsideDelta)
  · intros
    rename_i tail ih nextContext nextOutside delta outsideDelta
    cases delta with
      | handler rowsSame restDelta => exact .handler (ih _ _ restDelta outsideDelta)
  · intros
    rename_i tail ih nextContext nextOutside delta outsideDelta
    cases delta with
      | cell restDelta => exact .cell (ih _ _ restDelta outsideDelta)
  · intros
    rename_i callback tail ihCallback ihTail nextContext nextOutside delta outsideDelta
    cases delta with
      | cleanup rowsSame restDelta => exact .cleanup (callback.restore_support rowsSame ((restDelta.append outsideDelta).callback _)) (ihTail _ _ restDelta outsideDelta)
  · intros
    rename_i tail ih nextContext nextOutside delta outsideDelta
    cases delta with
      | normal restDelta => exact .normal (ih _ _ restDelta outsideDelta)
  · intros
    rename_i tail ih nextContext nextOutside delta outsideDelta
    cases delta with
      | unwinding restDelta => exact .unwinding (ih _ _ restDelta outsideDelta)
  · intros
    rename_i tail ih nextContext nextOutside delta outsideDelta
    cases delta with
      | closing restDelta => exact .closing (ih _ _ restDelta outsideDelta)
  · intros
    rename_i tail ih nextContext nextOutside delta outsideDelta
    cases delta with
      | retiring restDelta => exact .retiring (ih _ _ restDelta outsideDelta)
  · intros
    rename_i saved tail ihSaved ihTail nextContext nextOutside delta outsideDelta
    cases delta with
      | live savedDelta restDelta => exact .live (ihSaved _ _ savedDelta (restDelta.append outsideDelta)) (ihTail _ _ restDelta outsideDelta)
  · intros
    rename_i saved tail ihSaved ihTail nextContext nextOutside delta outsideDelta
    cases delta with
      | live savedDelta restDelta => exact .opening (ihSaved _ _ savedDelta (.retiring (restDelta.append outsideDelta))) (ihTail _ _ restDelta outsideDelta)
  · intros
    rename_i tail ih nextContext nextOutside delta outsideDelta
    cases delta with
      | spent restDelta => exact .spent (ih _ _ restDelta outsideDelta)
end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.SourceAdmission

namespace Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting
open Ash.OneShot.CoreCallableRestoredSupport
open SourceDependencyChecks.Lexical (ReturnHints)
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

 theorem Run.restore_support
    {checking : SourcePlanSignatures.Signature dependencies} {rows nextRows : Rows checking}
    {hints : ReturnHints scope} {context nextContext : Context hints}
    {root : RecursiveRequirements.Requirements demand}
    (run : Run world installations rows context root)
    (rowsSame : SupportOnly rows nextRows) (delta : RestoredContext context nextContext) :
    Run world installations nextRows nextContext root := by
  revert nextRows nextContext
  apply Run.rec
    (motive_1 := fun world installations {dependencies checking} rows {scope hints} context {demand} root _ =>
      ∀ (nextRows : Rows checking) (nextContext : Context hints), SupportOnly rows nextRows → RestoredContext context nextContext →
      Run world installations nextRows nextContext root)
    (motive_2 := fun world installations {scope hints} context mode {demand} root _ =>
      ∀ (nextContext : Context hints), RestoredContext context nextContext → Wait world installations nextContext mode root)
    (t := run)
  · intros
    rename_i continuation ih nextRows nextContext rowsSame delta
    cases nextRows
    exact .pure (ih _ delta)
  · intros
    rename_i found continuation ih nextRows nextContext rowsSame delta
    cases nextRows
    exact .builtin (delta.builtin found) (ih _ delta)
  · intros
    rename_i localDemand localRoot cut selected body binding ihBody nextRows nextContext rowsSame delta
    cases nextRows
    obtain ⟨nextCaptured, nextTail, nextCut, capturedDelta, tailDelta⟩ := delta.cut cut
    obtain ⟨nextBodyRows, nextSelected, bodySame⟩ := CapturedClauseRows.restore_support selected capturedDelta
    refine .request (localDemand := localDemand) (localRoot := localRoot) nextCut nextSelected ?_ ?_
    · intro owner demand absent
      apply ihBody owner demand
      · simpa only [delta.ticketNames] using absent
      · exact bodySame owner
      · exact .live capturedDelta tailDelta
    · intro owner demand absent
      apply binding owner demand
      simpa only [delta.ticketNames] using absent
  · intros
    rename_i first ih nextRows nextContext rowsSame delta
    cases nextRows with
    | sequence nextFirst nextSecond =>
      unfold SupportOnly at rowsSame
      simp only [eraseSupportBounds] at rowsSame
      injection rowsSame
      exact .sequence (ih _ _ (by assumption) (.plain (by assumption) delta))
  · intros
    rename_i body ih nextRows nextContext rowsSame delta
    cases nextRows with
    | handler nextDeclarations nextBody =>
      unfold SupportOnly at rowsSame
      simp only [eraseSupportBounds] at rowsSame
      injection rowsSame
      exact .installHandler (fun activation fresh => ih activation fresh _ _ (by assumption) (.handler (by assumption) delta))
  · intros
    rename_i body ih nextRows nextContext rowsSame delta
    cases nextRows with
    | resource nextBody =>
      unfold SupportOnly at rowsSame
      simp only [eraseSupportBounds] at rowsSame
      injection rowsSame
      rename_i bodySame
      exact .installResource (fun identity fresh => ih identity fresh _ _ (congrFun bodySame identity) (.cell delta))
  · intros
    rename_i body ih nextRows nextContext rowsSame delta
    cases nextRows with
    | cleanup nextLatent nextCallback nextBody =>
      unfold SupportOnly at rowsSame
      simp only [eraseSupportBounds] at rowsSame
      injection rowsSame
      subst_vars
      exact .installCleanup (ih _ _ (by assumption) (.cleanup (by assumption) delta))
  · intros
    rename_i left right same ihLeft ihRight nextRows nextContext rowsSame delta
    cases nextRows with
    | choice nextLeft nextRight =>
      unfold SupportOnly at rowsSame
      simp only [eraseSupportBounds] at rowsSame
      injection rowsSame
      exact .choice (ihLeft _ _ (by assumption) delta) (ihRight _ _ (by assumption) delta) same
  · intros
    rename_i located restored ih nextRows nextContext rowsSame delta
    cases nextRows
    rename_i front captured tail
    obtain ⟨nextFront, nextLive, rfl, frontDelta, liveDelta⟩ := delta.split front (.live captured tail)
    cases liveDelta with
    | live capturedDelta tailDelta =>
      exact .resume located (ih _ (capturedDelta.append (frontDelta.append (.spent tailDelta))))
  · intros
    rename_i located abandoned ih nextRows nextContext rowsSame delta
    cases nextRows
    rename_i front captured tail
    obtain ⟨nextFront, nextLive, rfl, frontDelta, liveDelta⟩ := delta.split front (.live captured tail)
    cases liveDelta with
    | live capturedDelta tailDelta =>
      exact .dispose located (ih _ (capturedDelta.append (.closing (frontDelta.append (.spent tailDelta)))))
  · intros
    rename_i nextContext delta
    cases delta
    exact .nil
  · intros
    rename_i code ih nextContext delta
    cases delta with
    | plain rowsSame tailDelta => exact .plain (ih _ _ rowsSame tailDelta)
  · intros
    rename_i tail ih nextContext delta
    cases delta with
    | plain rowsSame tailDelta => exact .skipped (ih _ tailDelta)
  · intros
    rename_i tail ih nextContext delta
    cases delta with
    | handler rowsSame tailDelta => exact .handler (ih _ tailDelta)
  · intros
    rename_i tail ih nextContext delta
    cases delta with
    | cell tailDelta => exact .cell (ih _ tailDelta)
  · intros
    rename_i callback ih nextContext delta
    cases delta with
    | cleanup rowsSame tailDelta => exact .cleanup (ih _ _ rowsSame (tailDelta.callback _))
  · intros
    rename_i tail ih nextContext delta
    cases delta with
    | normal tailDelta => exact .normal (ih _ tailDelta)
  · intros
    rename_i tail ih nextContext delta
    cases delta with
    | unwinding tailDelta => exact .unwinding (ih _ tailDelta)
  · intros
    rename_i tail ih nextContext delta
    cases delta with
    | closing tailDelta => exact .closing (ih _ tailDelta)
  · intros
    rename_i tail ih nextContext delta
    cases delta with
    | retiring tailDelta => exact .retiring (ih _ tailDelta)
  · intros
    rename_i tail ih nextContext delta
    cases delta with
    | live savedDelta tailDelta => exact .live (ih _ tailDelta)
  · intros
    rename_i captured ih nextContext delta
    cases delta with
    | live savedDelta tailDelta => exact .opening (ih _ (savedDelta.append (.retiring tailDelta)))
  · intros
    rename_i tail ih nextContext delta
    cases delta with
    | spent tailDelta => exact .spent (ih _ tailDelta)

 theorem Wait.restore_support
    {hints : ReturnHints scope} {context nextContext : Context hints}
    {root : RecursiveRequirements.Requirements demand}
    (waiting : Wait world installations context mode root)
    (delta : RestoredContext context nextContext) :
    Wait world installations nextContext mode root := by
  revert nextContext
  apply Wait.rec
    (motive_1 := fun world installations {dependencies checking} rows {scope hints} context {demand} root _ => True)
    (motive_2 := fun world installations {scope hints} context mode {demand} root _ =>
      ∀ (nextContext : Context hints), RestoredContext context nextContext → Wait world installations nextContext mode root)
    (t := waiting)
  all_goals try (intros; trivial)
  · intros
    rename_i nextContext delta
    cases delta
    exact .nil
  · intros
    rename_i code ih nextContext delta
    cases delta with
    | plain rowsSame tailDelta => exact .plain (code.restore_support rowsSame tailDelta)
  · intros
    rename_i tail ih nextContext delta
    cases delta with
    | plain rowsSame tailDelta => exact .skipped (ih _ tailDelta)
  · intros
    rename_i tail ih nextContext delta
    cases delta with
    | handler rowsSame tailDelta => exact .handler (ih _ tailDelta)
  · intros
    rename_i tail ih nextContext delta
    cases delta with
    | cell tailDelta => exact .cell (ih _ tailDelta)
  · intros
    rename_i callback ih nextContext delta
    cases delta with
    | cleanup rowsSame tailDelta => exact .cleanup (callback.restore_support rowsSame (tailDelta.callback _))
  · intros
    rename_i tail ih nextContext delta
    cases delta with
    | normal tailDelta => exact .normal (ih _ tailDelta)
  · intros
    rename_i tail ih nextContext delta
    cases delta with
    | unwinding tailDelta => exact .unwinding (ih _ tailDelta)
  · intros
    rename_i tail ih nextContext delta
    cases delta with
    | closing tailDelta => exact .closing (ih _ tailDelta)
  · intros
    rename_i tail ih nextContext delta
    cases delta with
    | retiring tailDelta => exact .retiring (ih _ tailDelta)
  · intros
    rename_i tail ih nextContext delta
    cases delta with
    | live savedDelta tailDelta => exact .live (ih _ tailDelta)
  · intros
    rename_i captured ih nextContext delta
    cases delta with
    | live savedDelta tailDelta => exact .opening (ih _ (savedDelta.append (.retiring tailDelta)))
  · intros
    rename_i tail ih nextContext delta
    cases delta with
    | spent tailDelta => exact .spent (ih _ tailDelta)

end Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.SourceAdmission.Code.restore_support
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.Run.restore_support

#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.SourceAdmission.Pending.restore_support
#print axioms Ash.OneShot.SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Accounting.Wait.restore_support
#print axioms Ash.OneShot.CoreCallableRestoredSupport.RestoredContext.builtin
#print axioms Ash.OneShot.CoreCallableRestoredSupport.RestoredContext.callback
