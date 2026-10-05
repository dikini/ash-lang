import CoreCallableContractExecution

/-! Derive full retained context ticket domains from the existing rich pending
relation. Installed captures, dormant saved contexts and spent owners are kept.
This source draft does not construct a rich capture successor or registry origin. -/
namespace Ash.OneShot.CoreCallableRichContextTicketDomain
open ScopedExpressions ScopedExecution ProtectionContracts
open CoreCallableContractSource (Contract)
open CoreCallableContractAdmission (Globals)
open CoreCallableContractExecution (Pending SelectedPending Site)
open SourcePlannedChecks (DeclarationPolicy)
open SourceDependencyChecks.Lexical (ReturnHints)
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual

/-- Exact target property; no additional invariant or runtime history is assumed. -/
def TicketDomain (globals : Globals) {hints : ReturnHints scope}
    (context : Context hints) : Prop :=
  ∀ owner, owner ∈ context.ticketNames → ∃ contract, globals.owners owner = some contract

/-- A decorated cut preserves every ticket name, including saved and spent names. -/
theorem cut_ticketNames
    {effect : Instance} {operation : Nat} {contract : ClauseContract}
    {modes : Option (Nat → SourceDependencyAnnotations.Dependencies) ×
      Option (Nat → SourceDependencyAnnotations.Dependencies)}
    {wholeHints : ReturnHints wholeScope} {captureHints : ReturnHints captureScope}
    {tailHints : ReturnHints tailScope}
    {whole : Context wholeHints} {captured : Context captureHints} {tail : Context tailHints}
    (cut : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Cut
      effect operation whole captured tail contract modes) :
    whole.ticketNames = captured.ticketNames ++ tail.ticketNames := by
  have same := congrArg (fun packed : Packed ↦ packed.context.ticketNames)
    (SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Cut.decomposition cut)
  change whole.ticketNames = (captured.append tail).ticketNames at same
  exact same.trans (Context.append_ticketNames captured tail)

private theorem cut_domain
    {effect : Instance} {operation : Nat} {contract : ClauseContract}
    {modes : Option (Nat → SourceDependencyAnnotations.Dependencies) ×
      Option (Nat → SourceDependencyAnnotations.Dependencies)}
    {wholeHints : ReturnHints wholeScope} {captureHints : ReturnHints captureScope}
    {tailHints : ReturnHints tailScope}
    {whole : Context wholeHints} {captured : Context captureHints} {tail : Context tailHints}
    (cut : SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual.Cut
      effect operation whole captured tail contract modes)
    (known : TicketDomain globals whole) :
    TicketDomain globals captured ∧ TicketDomain globals tail := by
  constructor
  · intro owner member
    apply known owner
    rw [cut_ticketNames cut]
    exact List.mem_append_left _ member
  · intro owner member
    apply known owner
    rw [cut_ticketNames cut]
    exact List.mem_append_right _ member

private theorem live_domain
    {globals : Globals} {owner : Nat} {contract : CoreCallableContractRegistries.OwnerContract}
    {captureHints : ReturnHints captureScope} {tailHints : ReturnHints tailScope}
    {captured : Context captureHints} {tail : Context tailHints}
    (known : globals.owners owner = some contract)
    (saved : TicketDomain globals captured) (outside : TicketDomain globals tail) :
    TicketDomain globals (.live (owner := owner) (resumeDemand := resumeDemand) captured tail) := by
  intro name member
  simp only [Context.ticketNames, List.mem_cons, List.mem_append] at member
  rcases member with same | savedMember | outsideMember
  · subst name
    exact ⟨contract, known⟩
  · exact saved name savedMember
  · exact outside name outsideMember

private theorem spent_domain
    {globals : Globals} {owner : Nat} {contract : CoreCallableContractRegistries.OwnerContract}
    {hints : ReturnHints scope} {context : Context hints}
    (known : globals.owners owner = some contract)
    (tail : TicketDomain globals context) :
    TicketDomain globals (.spent (owner := owner) context) := by
  intro name member
  simp only [Context.ticketNames, List.mem_cons] at member
  rcases member with same | tailMember
  · subst name
    exact ⟨contract, known⟩
  · exact tail name tailMember

section
variable [evidence : DeclarationPolicy]

/-- Every name retained by the SAME rich pending context has a full owner entry.
The mutual motive keeps both installed whole and outside context domains. -/
theorem pending_ticket_domain
    (pending : Pending globals outward world allowed ambient stack input output context) :
    TicketDomain globals context := by
  induction pending using Pending.rec
    (motive_2 := fun {_} {_} {_} {_} {_} {_} {_}
      {wholeContext} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_}
      {outside} _ _ => TicketDomain globals wholeContext ∧ TicketDomain globals outside) with
  | nil =>
      intro owner member
      cases member
  | plain frame received accepts tail ih => exact ih
  | handler frame admitted tail ih => exact ih
  | handlerView frame admitted entered bounded tail ih => exact ih
  | live known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation
      saved tail ihSaved ihTail =>
      exact live_domain known ihSaved ihTail
  | capture known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation
      frame installed physical contextual terminal ihInstalled =>
      obtain ⟨savedDomain, outsideDomain⟩ := cut_domain contextual ihInstalled.1
      exact live_domain known savedDomain outsideDomain
  | spent known answerSame annotation tail ih => exact spent_domain known ih
  | cell issued annotation tail ih => exact ih
  | here frame admitted tail ih => exact ⟨ih, ih⟩
  | hereView frame admitted entered bounded tail ih => exact ⟨ih, ih⟩
  | plainPath saved received accepts selected ih => exact ih
  | handlerMiss saved admitted miss selected ih => exact ih
  | handlerMissView saved admitted entered bounded miss selected ih => exact ih
  | cellPath issued annotation selected ih => exact ih
  | spentPath known answerSame annotation selected ih =>
      exact ⟨spent_domain known ih.1, ih.2⟩
  | liveTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation
      saved selected ihSaved ih =>
      exact ⟨live_domain known ihSaved ih.1, ih.2⟩
  | captureTail known inputSame answerSame heldSame resumeSame balanced inputAnnotation answerAnnotation
      installedFrame installation physical contextual terminal selected ihInstallation ih =>
      obtain ⟨savedDomain, _⟩ := cut_domain contextual ihInstallation.1
      exact ⟨live_domain known savedDomain ih.1, ih.2⟩

/-- Selected installation prefixes and their actual outside are both covered.
Connection reuses the same pending contexts; no replacement context is supplied. -/
theorem selected_ticket_domain
    (selected : SelectedPending globals outward world (beforeAllowed := beforeAllowed)
      (ambient := ambient) (whole := whole) (input := input) (output := output)
      (wholeContext := wholeContext) (tailAllowed := tailAllowed) (tail := tail)
      (outside := outside) frame) :
    TicketDomain globals wholeContext ∧ TicketDomain globals outside :=
  ⟨pending_ticket_domain selected.before, pending_ticket_domain selected.outside⟩

/-- The full current Site supplies the pending premise without an extra domain field. -/
theorem site_ticket_domain
    (site : Site globals outward world allowed actions phases budget ambient installations
      expression runtimeScope stack result final context root) :
    ∀ owner, owner ∈ context.ticketNames → ∃ contract, globals.owners owner = some contract :=
  pending_ticket_domain site.pending

#check TicketDomain
#check cut_ticketNames
#check pending_ticket_domain
#check selected_ticket_domain
#check site_ticket_domain

#print axioms cut_ticketNames
#print axioms pending_ticket_domain
#print axioms selected_ticket_domain
#print axioms site_ticket_domain
end
end Ash.OneShot.CoreCallableRichContextTicketDomain
