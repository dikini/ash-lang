import CoreCallableStrictOutsideHeadOrigins
namespace Ash.OneShot.CoreCallableStrictCallerHeadCompatibility
open CoreSyntax CoreMachine CoreTranslation CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreCallableGeneralHistory CoreCallableGeneratedChronology
open CoreCallableReachableResume CoreCallableSiteLineage CoreCallableGeneralStrictFocus CoreCallableStrictFocusConsumers
open CoreCallableStrictCaptureOrigins CoreCallableOutsideOrigin CoreCallableCallerBarriers

open CoreCallableStrictOutsideHeadOrigins

/-- Compare original saved active handler heads only; tails, owners and tickets
remain independently indexed. No future path or restored metadata is examined. -/
def savedCallerHeadCheck (owners : OwnerMap) (scope : Execution.Scope)
    (selectedOwners : OwnerMap) (selectedScope : Execution.Scope) : Bool :=
  match scope, owners, selectedScope, selectedOwners with
  | .none, _, _, _ => true
  | .ticket _ _, caller :: _, .ticket _ _, selected :: _ => caller.handler == selected.handler
  | _, _, _, _ => false

theorem independent_saved_metadata (originalTail selectedTail : OwnerMap)
    (handler originalOwner selectedOwner originalTicket selectedTicket : Nat) :
    savedCallerHeadCheck (⟨handler,originalOwner,ticket graph originalOwner⟩::originalTail)
      (.ticket (ticket graph originalOwner) originalTicket)
      (⟨handler,selectedOwner,ticket graph selectedOwner⟩::selectedTail)
      (.ticket (ticket graph selectedOwner) selectedTicket) = true := by
  simp [savedCallerHeadCheck]

/-- Active original metadata is inverted independently of HandlerData projections. -/
theorem active_lineage_handler_miss
    (lineage : SiteLineage graph selectedOwners selectedScope site)
    (selectedKnown : graph.node site = some selectedNode)
    (selectedKind : selectedNode.kind = .handler selectedHandler effect body clauses)
    (unique : UniqueHandlerSites graph)
    (checked : savedCallerHeadCheck
      (⟨callerHandler,callerOwner,ticket graph callerOwner⟩::callerTail)
      (.ticket (ticket graph callerOwner) callerTicket) selectedOwners selectedScope = true) :
    callerHandler ≠ selectedHandler := by
  cases lineage with
  | inactive canonical => simp [savedCallerHeadCheck] at checked
  | @clause selectedTail enclosingSite enclosingNode enclosingHandler enclosingEffect enclosingBody enclosingClauses evaluatedSite enclosingOwner enclosingTicket canonical known kind below =>
    have sameHead : callerHandler = enclosingHandler := by simpa [savedCallerHeadCheck] using checked
    intro same
    rw [← same, sameHead] at selectedKind
    have sameSite := unique.lookup selectedKnown selectedKind known kind
    exact Nat.lt_irrefl _ (sameSite ▸ below)

/-- The selected installation keeps its OWN map/scope. No retargeting. -/
theorem selected_handler_miss
    (past : GeneralClausePast graph selectedOwners selectedHandler selectedOwner occurrence dynamicTicket captured data)
    (unique : UniqueHandlerSites graph)
    (checked : savedCallerHeadCheck
      (⟨callerHandler,callerOwner,ticket graph callerOwner⟩::callerTail)
      (.ticket (ticket graph callerOwner) callerTicket) selectedOwners data.scope = true) :
    callerHandler ≠ selectedHandler := by
  have different := active_lineage_handler_miss past.installation.lineage
    past.installation.known past.installation.kind unique checked
  simpa only [past.sameHandler] using different

private theorem path_outside_bound
    (path : OwnerPath handler owner occurrence dynamicTicket saved physical front tail)
    (same : physical = kept ++ outside) (checked : prefixMiss handler owner kept = true) :
    kept.length ≤ front.length := by
  induction path generalizing kept outside with
  | hit tail =>
    cases kept with
    | nil => simp
    | cons frame rest =>
      obtain ⟨rfl,_⟩ := List.cons.inj same
      simp [prefixMiss,frameMiss] at checked
  | skip frame miss next ih =>
    cases kept with
    | nil => simp
    | cons head rest =>
      obtain ⟨rfl,tailSame⟩ := List.cons.inj same
      have checks : frameMiss handler owner frame = true ∧ prefixMiss handler owner rest = true := by
        simpa [prefixMiss] using checked
      simpa using Nat.succ_le_succ (ih tailSame checks.2)

/-- The original first occurrence, dynamic ticket and saved capture survive
insertion. Selected installation metadata remains independently indexed. -/
theorem original_owner_path_restored
    (path : OwnerPath handler owner occurrence callerTicket saved physical front outsideTail)
    (same : physical = kept ++ outside)
    (keptChecked : prefixMiss handler owner kept = true)
    (past : GeneralClausePast graph selectedOwners selectedHandler selectedOwner selectedOccurrence selectedTicket captured data)
    (unique : UniqueHandlerSites graph)
    (metadata : savedCallerHeadCheck (⟨handler,owner,ticket graph owner⟩::callerTail)
      (.ticket (ticket graph owner) callerTicket) selectedOwners data.scope = true)
    {addedPhysical : List CoreMachine.Frame} {addedTarget : Stack}
    {addedHistory : GeneralHistory graph heap addedPhysical addedTarget}
    (added : PassFront handler owner addedHistory) :
    ∃ remaining, front = kept ++ remaining ∧
      OwnerPath handler owner occurrence callerTicket saved
        (kept ++ ((addedPhysical ++ [.clauseBoundary selectedHandler selectedOwner selectedOccurrence selectedTicket none]) ++ outside))
        (kept ++ ((addedPhysical ++ [.clauseBoundary selectedHandler selectedOwner selectedOccurrence selectedTicket none]) ++ remaining))
        outsideTail := by
  obtain ⟨remaining,retained,frontSame,keptMiss⟩ := OwnerPath.drop_prefix path same
    (path_outside_bound path same keptChecked)
  have different := selected_handler_miss past unique metadata
  have frontMiss := PassFront.prefix_miss added
  have inserted : prefixMiss handler owner
      (addedPhysical ++ [.clauseBoundary selectedHandler selectedOwner selectedOccurrence selectedTicket none]) = true := by
    simpa [prefixMiss,List.all_append,frameMiss,different] using frontMiss
  exact ⟨remaining,frontSame,OwnerPath.prepend_checked
    (OwnerPath.prepend_checked retained inserted) keptMiss⟩

theorem original_scope_restored
    (origin : CurrentScopeOrigin graph owners scope physical)
    (same : physical = kept ++ outside)
    (position : callerOutsideCheck owners scope kept = true)
    (past : GeneralClausePast graph selectedOwners handler owner occurrence dynamicTicket captured data)
    (unique : UniqueHandlerSites graph)
    (metadata : savedCallerHeadCheck owners scope selectedOwners data.scope = true)
    {addedPhysical : List CoreMachine.Frame} {addedTarget : Stack}
    {addedHistory : GeneralHistory graph heap addedPhysical addedTarget}
    (added : PassFront (match owners with | [] => 0 | e::_ => e.handler)
      (match owners with | [] => 0 | e::_ => e.owner) addedHistory) :
    CurrentScopeOrigin graph owners scope
      (kept ++ ((addedPhysical ++ [.clauseBoundary handler owner occurrence dynamicTicket none]) ++ outside)) := by
  cases origin with
  | inactive canonical => exact .inactive canonical
  | clause canonical path =>
    have keptChecked := position
    simp only [callerOutsideCheck] at keptChecked
    obtain ⟨remaining,_,restored⟩ := original_owner_path_restored path same keptChecked past unique metadata added
    exact .clause canonical restored

theorem outside_restored_scope {graph : Graph} {kind : PairApplication} {original capturedFrom current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    (before : BeforeCapture pastRun ready capturedFrom beforeCount) (input : CaptureInput capturedFrom)
    (run : AfterCapture input current afterCount) (unique : UniqueHandlerSites graph)
    (metadata : savedCallerHeadCheck original.owners ready.plain.scope
      (location capturedFrom input.index).owners (location capturedFrom input.index).data.scope = true)
    (position : callerOutsideCheck original.owners ready.plain.scope (dormant before input).kept = true) :
    CurrentScopeOrigin graph original.owners ready.plain.scope
      ((dormant before input).kept ++ (run.carrier.front ++
        .clauseBoundary (location capturedFrom input.index).installation.handler input.selectedClause.owner
          (location capturedFrom input.index).data.activation capturedFrom.state.nextOwner none ::
          (location capturedFrom input.index).outside)) := by
  simpa only [List.append_assoc,List.singleton_append] using
    original_scope_restored (pastRun.receipt ready).saved.origin (dormant_original_tail before input)
      position (capture_data input).installation unique metadata (AfterCapture.caller_front_pass run _ _)

#print axioms independent_saved_metadata
#print axioms active_lineage_handler_miss
#print axioms selected_handler_miss
#print axioms original_owner_path_restored
#print axioms original_scope_restored
#print axioms outside_restored_scope
end Ash.OneShot.CoreCallableStrictCallerHeadCompatibility
