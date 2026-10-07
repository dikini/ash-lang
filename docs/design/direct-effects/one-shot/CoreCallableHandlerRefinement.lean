import CoreCallableReceiverRefinement

/-! Nonvacuity of the receiver-dependent refinement interface. The private
callable installs one non-disposing handler and immediately resumes its own
request. All caller evidence is current; no future admission is a premise. -/
namespace Ash.OneShot.CoreCallableHandlerRefinement
open ScopedExpressions ScopedExecution ProtectionContracts
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open RecursiveRequirements (Requirements LocalOwner)
open CoreCallableRootRefinement (RootTransport)
open CoreCallableReceiverRefinement (ReceiverRefines)

private def Quiet (alpha : Nat) : {demand : List Nat} → Requirements demand → Prop
  | _, .request nearer raw => nearer = [] ∧ raw = []
  | _, .retire other | _, .spent other => other ≠ alpha
  | _, .sequence first second | _, .choice first second _ => Quiet alpha first ∧ Quiet alpha second
  | _, .invoke _ _ _ | _, .emitAfter _ _ _ => False

private theorem quiet_identity (quiet : Quiet alpha root) : LocalOwner alpha phase root root phase := by
  induction root with
  | request nearer raw => rcases quiet with ⟨rfl, rfl⟩; exact .empty
  | retire other => exact .retireOther quiet
  | spent other => exact .spentOther quiet
  | sequence first second ihFirst ihSecond => exact .sequence (ihFirst quiet.1) (ihSecond quiet.2)
  | choice first second same ihFirst ihSecond => exact .choice (ihFirst quiet.1) (ihSecond quiet.2)
  | invoke | emitAfter => exact False.elim quiet

private theorem discharge_quiet
    (discharge : LocalOwner beta before localRoot outerRoot after)
    (quiet : Quiet alpha localRoot) : Quiet alpha outerRoot := by
  induction discharge with
  | empty | retireSelf | spentSelf => exact ⟨rfl, rfl⟩
  | retireOther | spentOther => exact quiet
  | sequence first second ihFirst ihSecond | choice first second ihFirst ihSecond =>
    exact ⟨ihFirst quiet.1, ihSecond quiet.2⟩

private theorem run_identity
    (run : Accounting.Run world installations rows context root) :
    ∀ alpha, alpha ∉ context.ticketNames → Quiet alpha root := by
  induction run using Accounting.Run.rec
    (motive_2 := fun world installations {_} {_} context mode {demand} root _ =>
      ∀ alpha, alpha ∉ context.ticketNames → Quiet alpha root) with
  | pure waiting ih | builtin found waiting ih => exact ih
  | @request wholeScope captureScope tailScope effect operation contract modes world installations demand root wholeHints captureHints tailHints whole captured tail family bodies bodyRows localDemand localRoot cut selected body binding ih =>
    intro alpha absent
    obtain ⟨beta, fresh⟩ := ScopedTyping.fresh_world_name (alpha :: whole.ticketNames)
    have separate : beta ≠ alpha := fun same => fresh (by simp [same])
    have betaFresh : beta ∉ whole.ticketNames := fun member => fresh (List.mem_cons_of_mem _ member)
    have parts := congrArg (fun packed : Packed => packed.context.ticketNames) cut.decomposition
    change whole.ticketNames = (captured.append tail).ticketNames at parts
    have alphaParts : alpha ∉ (captured.append tail).ticketNames := by
      rw [← parts]
      exact absent
    have nextAbsent : alpha ∉ (Context.live (owner := beta) (resumeDemand := []) captured tail).ticketNames := by
      simpa only [Context.ticketNames, Context.append_ticketNames, List.mem_cons, List.mem_append, not_or]
        using And.intro (Ne.symm separate) alphaParts
    exact discharge_quiet (binding beta [] betaFresh) (ih beta [] betaFresh alpha nextAbsent)
  | sequence first ih | installCleanup body ih => exact ih
  | installHandler body ih =>
    intro alpha absent
    obtain ⟨activation, fresh⟩ := ScopedTyping.fresh_world_name _
    exact ih activation fresh alpha absent
  | installResource body ih =>
    intro alpha absent
    obtain ⟨identity, fresh⟩ := ScopedTyping.fresh_world_name _
    exact ih identity fresh alpha absent
  | choice left right same ihLeft ihRight =>
    intro alpha absent
    exact ⟨ihLeft alpha absent, ihRight alpha absent⟩
  | resume located restored ih | dispose located abandoned ih =>
    intro alpha absent
    simp only [Context.append_ticketNames, Context.ticketNames, List.mem_append, List.mem_cons, not_or] at absent
    exact And.intro (Ne.symm absent.2.1)
      (ih alpha (by
        simp only [Context.append_ticketNames, Context.ticketNames, List.mem_append, List.mem_cons, not_or]
        exact ⟨absent.2.2.1, absent.1, absent.2.1, absent.2.2.2⟩))
  | nil => rename_i alpha absent; exact ⟨rfl, rfl⟩
  | plain code ih | skipped tail ih | handler tail ih | cell tail ih
  | normal tail ih | unwinding tail ih | closing tail ih =>
    rename_i alpha absent
    exact ih alpha absent
  | cleanup callback ih =>
    rename_i alpha absent
    exact ih alpha (by simpa only [Context.callback_ticketNames, Context.ticketNames] using absent)
  | retiring tail ih =>
    rename_i alpha absent
    simp only [Context.ticketNames, List.mem_cons, not_or] at absent
    exact ⟨Ne.symm absent.1, ih alpha absent.2⟩
  | live tail ih =>
    rename_i alpha absent
    simp only [Context.ticketNames, List.mem_cons, List.mem_append, not_or] at absent
    exact ⟨Ne.symm absent.1, ih alpha absent.2.2⟩
  | opening captured ih =>
    rename_i alpha absent
    apply ih alpha
    simpa only [Context.append_ticketNames, Context.ticketNames, List.mem_cons, List.mem_append, not_or,
      and_assoc, and_left_comm, and_comm] using absent
  | spent tail ih =>
    rename_i alpha absent
    simp only [Context.ticketNames, List.mem_cons, not_or] at absent
    exact ⟨Ne.symm absent.1, ih alpha absent.2⟩

theorem wait_identity (waiting : Accounting.Wait world installations context mode root)
    (absent : alpha ∉ context.ticketNames) : LocalOwner alpha phase root root phase := by
  cases mode with
  | ordinary => exact quiet_identity (run_identity (.pure waiting) alpha absent)
  | unwind => exact quiet_identity (run_identity (.pure (.unwinding waiting)) alpha absent)

/-- The same minimal local effect used by the old-interface counterexample. -/
def effect : Instance := .user 7 []
def contract : ClauseContract := ⟨false, some [], none⟩
def declarations : ClauseRows
    (.cons (operation := 0) ⟨true, false⟩
      (.available (fun owner => .sequence .pure (.invoke (key := ⟨owner, .resume⟩)))) .unavailable .nil) :=
  .cons (.available (fun _ => .sequence .pure .invoke)) .unavailable .nil []
def captured (activation : Nat) :=
  Context.handler (effect := effect) (table := [(0, contract)]) activation declarations Context.nil
def privateRows :=
  Rows.handler (effect := effect) (table := [(0, contract)]) (required := []) declarations
    (Rows.sequence Rows.pure (Rows.request (effect := effect) (operation := 0)))

private theorem extension (fresh : actions owner = none) :
    Syntax.UsageExtension actions (actions.insert owner rights) := by
  intro name old known
  by_cases same : name = owner
  · subst name; rw [fresh] at known; cases known
  · simpa only [Syntax.UsageTickets.insert, if_neg same] using known

private theorem resumedTail
    {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope} {context : Context hints}
    (retained : SourceAdmission.Pending outward actions budget phases world installations context Context.nil
      .ordinary (hints.returnMode .ordinary)) (activation owner : Nat)
    (fresh : actions owner = none) (absent : owner ∉ context.ticketNames) :
    SourceAdmission.Pending outward (actions.insert owner ⟨true, false⟩) budget
      (OwnerPhaseTransitions.spend (OwnerPhaseTransitions.introduce phases owner) owner) world
      (activation :: installations) context Context.nil .ordinary (hints.returnMode .ordinary) := by
  let installed := retained.installations_mono (nextInstallations := activation :: installations)
    (fun _ member => List.mem_cons_of_mem _ member)
  let permitted := installed.permissions (extension (rights := ⟨true, false⟩) fresh)
  let introduced := permitted.introduce_absent (by
    simpa only [Context.append_ticketNames, Context.ticketNames, List.append_nil] using absent)
  exact introduced.spend_absent (by
    intro member
    exact absent (by simpa only [Context.append_ticketNames, Context.ticketNames, List.append_nil] using
      (Context.owned_subset_ticketNames _ member)))

private theorem resumedTail_checked
    {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope} {context : Context hints}
    {retained : SourceAdmission.Pending outward actions budget phases world installations context Context.nil
      .ordinary (hints.returnMode .ordinary)} (checked : InstallationSupport.PendingChecked ambient outward retained)
    (activation owner : Nat) (fresh : actions owner = none) (absent : owner ∉ context.ticketNames) :
    InstallationSupport.PendingChecked ambient outward (resumedTail retained activation owner fresh absent) := by
  exact (((checked.installations_mono (nextInstallations := activation :: installations)
    (fun _ member => List.mem_cons_of_mem _ member)).permissions (extension (rights := ⟨true, false⟩) fresh)).introduce_absent (by simpa only [Context.append_ticketNames, Context.ticketNames, List.append_nil] using absent)).spend_absent (by
      intro member
      exact absent (by simpa only [Context.append_ticketNames, Context.ticketNames, List.append_nil] using
        (Context.owned_subset_ticketNames _ member)))

/-- Retained caller source is restored by the private immediate-resume clause.
Every fresh installation and owner is constructed by the existing rules. -/
theorem certificate
    {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope} {context : Context hints}
    (retained : SourceAdmission.Pending outward actions budget phases world installations context Context.nil
      .ordinary (hints.returnMode .ordinary)) :
    SourceAdmission.Code outward actions budget phases world installations privateRows context := by
  apply SourceAdmission.Code.handler
  intro activation activationFresh
  apply SourceAdmission.Code.sequence SourceAdmission.Code.pure
  apply SourceAdmission.Code.request (effect := effect) (operation := 0)
    (whole := Context.handler (effect := effect) (table := [(0, contract)]) activation declarations context)
    (captured := captured activation) (tail := context) (contract := contract)
    (modes := (some (fun owner => .sequence .pure (.invoke ⟨owner, .resume⟩)), none))
    (bodyRows := fun owner => Rows.sequence Rows.pure (Rows.invoke (key := ⟨owner, .resume⟩)))
    (declarationRows := declarations) (rights := ⟨true, false⟩) (cut := rfl)
  · exact .handler rfl rfl rfl rfl
  · intro impossible; cases impossible
  · intro impossible; cases impossible
  · exact RequestBudget.nonconsuming rfl rfl
  · exact .selected .here .ordinary
  · exact .here
  · rfl
  · exact .handler (retained.installations_mono (fun _ member => List.mem_cons_of_mem _ member))
  · intro owner demand fresh absent
    apply SourceAdmission.Code.sequence .pure
    apply SourceAdmission.Code.resume (front := Context.nil) (captured := captured activation)
      (tail := context) (rights := ⟨true, false⟩)
    · exact .hit
    · simp [Syntax.UsageTickets.insert]
    · rfl
    · simp [OwnerPhaseTransitions.introduce]
    · exact ResumeShape.ordinary
    · exact .handler (.spent (resumedTail retained activation owner fresh absent))

theorem certificate_checked
    {scope : SourceDependencyCapture.Scope} {hints : ReturnHints scope} {context : Context hints}
    {retained : SourceAdmission.Pending outward actions budget phases world installations context Context.nil
      .ordinary (hints.returnMode .ordinary)}
    (checked : InstallationSupport.PendingChecked ambient outward retained) :
    InstallationSupport.CodeChecked ambient outward (certificate retained) := by
  apply InstallationSupport.CodeChecked.handler
  · simp [declarations, ClauseRows.resourceSupport]
  · intro activation activationFresh
    apply InstallationSupport.CodeChecked.sequence .pure
    apply InstallationSupport.CodeChecked.request
      (effect := effect) (operation := 0)
      (modes := (some (fun owner => .sequence .pure (.invoke ⟨owner, .resume⟩)), none))
      (contract := contract) (rights := ⟨true, false⟩)
      (whole := Context.handler (effect := effect) (table := [(0, contract)]) activation declarations context)
      (captured := captured activation) (tail := context)
      (bodyRows := fun owner => Rows.sequence Rows.pure (Rows.invoke (key := ⟨owner, .resume⟩)))
      (declarationRows := declarations) (activation := activation)
      (cut := rfl) (guarded := .handler rfl rfl rfl rfl)
      (callbacks := fun impossible => False.elim (Bool.noConfusion impossible))
      (ownerBound := fun impossible => False.elim (Bool.noConfusion impossible))
      (cleanupBudget := RequestBudget.nonconsuming rfl rfl)
      (selected := .selected .here .ordinary) (terminal := .here) (requiredRights := rfl)
      (retained := .handler (retained.installations_mono (fun _ member => List.mem_cons_of_mem _ member)))
    · intro impossible; cases impossible
    · exact .handler (checked.installations_mono (fun _ member => List.mem_cons_of_mem _ member))
    · intro owner demand fresh absent
      apply InstallationSupport.CodeChecked.sequence .pure
      apply InstallationSupport.CodeChecked.resume
        (front := Context.nil) (captured := captured activation) (tail := context)
        (rights := ⟨true, false⟩) (located := .hit)
        (known := by simp [Syntax.UsageTickets.insert]) (permission := rfl)
        (available := by simp [OwnerPhaseTransitions.introduce]) (resumeShape := ResumeShape.ordinary)
        (restored := .handler (.spent (resumedTail retained activation owner fresh absent)))
      exact .handler (.spent (resumedTail_checked checked activation owner fresh absent))

private def actualRoot (root : Requirements demand) : Requirements demand :=
  .sequence (.request [] []) (.sequence (.request [] []) root)

/-- The fresh local owner disappears from external requirements; the caller's
current requirement tree is retained underneath two empty leaves. -/
theorem accounting (run : Accounting.Run world installations Rows.pure context root) :
    Accounting.Run world installations privateRows context (actualRoot root) := by
  cases run with
  | pure waiting =>
    apply Accounting.Run.installHandler
    intro activation activationFresh
    apply Accounting.Run.sequence
    apply Accounting.Run.pure
    apply Accounting.Wait.plain
    apply Accounting.Run.request
      (whole := Context.handler (effect := effect) (table := [(0, contract)]) activation declarations context)
      (captured := captured activation) (tail := context) (contract := contract)
      (modes := (some (fun owner => .sequence .pure (.invoke ⟨owner, .resume⟩)), none))
      (bodyRows := fun owner => Rows.sequence Rows.pure (Rows.invoke (key := ⟨owner, .resume⟩)))
      (localRoot := fun owner _ => .sequence (.retire owner) (.sequence (.spent owner) root))
      (effect := effect) (operation := 0) (cut := rfl)
    · exact .selected .here .ordinary
    · intro owner demand absent
      apply Accounting.Run.sequence
      apply Accounting.Run.pure
      apply Accounting.Wait.plain
      apply Accounting.Run.resume (front := Context.nil) (captured := captured activation) (tail := context)
      · exact .hit
      · exact .handler (.spent (waiting.mono (List.Subset.refl _)
          (fun _ member => List.mem_cons_of_mem _ member)))
    · intro owner demand absent
      exact .sequence .retireSelf (.sequence .spentSelf (wait_identity waiting absent))

private theorem empty_prefix_transport (root : Requirements demand) :
    RootTransport root (.sequence (.request [] []) root) where
  checked := by
    intro entries receiving phases budget annotated row annotation checked bounded
    refine ⟨.sequence (.request [] []) annotated, row,
      .sequence .original annotation, ?_, bounded⟩
    have empty : RecursiveRequirements.Checked entries receiving phases (.request [] []) [] :=
      .request (by simp [OwnerSource.exportAt, ProtectionResiduals.residual_empty])
    simpa only [SourceScheduledCleanupInterfaces.Lexical.Recursive.annotateDisposals,
      OwnerPhaseTransitions.spendAll, List.nil_append] using RecursiveRequirements.Checked.sequence empty checked

theorem actual_root_transport (root : Requirements demand) : RootTransport root (actualRoot root) :=
  (empty_prefix_transport root).compose (empty_prefix_transport (.sequence (.request [] []) root))

/-- All three corrected refinement fields are inhabited for this one private
handler. Its immediate resume restores the supplied current caller evidence. -/
theorem refinement : ReceiverRefines Rows.pure privateRows [] [] where
  code := by
    intro outward actions budget phases world installations scope hints context retained publicCertificate
    exact certificate retained
  checked := by
    intro ambient outward actions budget phases world installations scope hints context retained publicCertificate required issued received retainedChecked publicChecked
    exact certificate_checked retainedChecked
  accounting := by
    intro world installations scope hints context demand root run
    exact ⟨actualRoot root, accounting run, actual_root_transport root⟩

end Ash.OneShot.CoreCallableHandlerRefinement
#print axioms Ash.OneShot.CoreCallableHandlerRefinement.wait_identity
#print axioms Ash.OneShot.CoreCallableHandlerRefinement.certificate
#print axioms Ash.OneShot.CoreCallableHandlerRefinement.certificate_checked

#print axioms Ash.OneShot.CoreCallableHandlerRefinement.accounting
#print axioms Ash.OneShot.CoreCallableHandlerRefinement.actual_root_transport
#print axioms Ash.OneShot.CoreCallableHandlerRefinement.refinement
