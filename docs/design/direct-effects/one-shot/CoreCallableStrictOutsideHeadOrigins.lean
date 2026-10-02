import CoreCallableStrictCaptureOrigins
import CoreCallableCallerBarriers
namespace Ash.OneShot.CoreCallableStrictOutsideHeadOrigins
open CoreSyntax CoreMachine CoreTranslation CoreValueRelation CoreStrictFrames CoreStrictStack
open ScopedExpressions ScopedExecution CoreCallableGeneralHistory CoreCallableGeneratedChronology
open CoreCallableReachableResume CoreCallableSiteLineage CoreCallableGeneralStrictFocus CoreCallableStrictFocusConsumers
open CoreCallableStrictCaptureOrigins CoreCallableOutsideOrigin CoreCallableCallerBarriers

theorem AfterCapture.caller_front_pass {capturedFrom current : Endpoint graph} {input : CaptureInput capturedFrom}
    (run : AfterCapture input current count) (handler owner : Nat) :
    PassFront handler owner run.carrier.frontHistory := by
  induction run with
  | captured => exact .nil
  | stable earlier step ih => cases step <;> exact ih
  | handler earlier installed ih => exact .handler _ _ _ ih

theorem PassFront.prefix_miss {graph : Graph} {heap : CoreMachine.Heap} {handler owner : Nat}
    {physical : List CoreMachine.Frame} {target : Stack} {history : GeneralHistory graph heap physical target}
    (pass : PassFront handler owner history) : prefixMiss handler owner physical = true := by
  apply (prefixMiss_test physical).mp
  simpa only [List.append_nil] using pass.physical_pass
    [.clauseBoundary handler owner 0 0 (some [])] ⟨[],handler,owner,0,0,[],[]⟩ (by simp [findOwner])

def selectedCallerCheck (owners : OwnerMap) (scope : Execution.Scope)
    (selectedOwners : OwnerMap) (selectedScope : Execution.Scope) : Bool :=
  decide (selectedOwners = owners ∧ selectedScope = scope)

theorem selectedCallerCheck_exact
    (checked : selectedCallerCheck owners scope selectedOwners selectedScope = true) :
    selectedOwners = owners ∧ selectedScope = scope := of_decide_eq_true checked

/-- Only the original cut is classified. No restored prefix or future path is examined. -/
def callerOutsideCheck (owners : OwnerMap) (scope : Execution.Scope) (kept : List CoreMachine.Frame) : Bool :=
  match scope, owners with
  | .none, _ => true
  | .ticket _ _, entry :: _ => prefixMiss entry.handler entry.owner kept
  | .ticket _ _, [] => false

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

theorem scope_outside_computed
    (origin : CurrentScopeOrigin graph owners scope physical)
    (same : physical = kept ++ outside) (checked : callerOutsideCheck owners scope kept = true) :
    ScopeOutside origin kept := by
  cases origin with
  | inactive canonical => exact .inactive canonical
  | clause canonical path => exact .clause canonical path (path_outside_bound path same checked)

private theorem inserted_miss {graph : Graph} {heap : CoreMachine.Heap}
    {frontPhysical : List CoreMachine.Frame} {frontTarget : Stack}
    {frontHistory : GeneralHistory graph heap frontPhysical frontTarget}
    (origin : CurrentScopeOrigin graph owners scope physical)
    (past : GeneralClausePast graph owners handler owner occurrence dynamicTicket captured data)
    (sameScope : data.scope = scope) (unique : UniqueHandlerSites graph)
    (front : PassFront (match owners with | [] => 0 | e::_ => e.handler)
      (match owners with | [] => 0 | e::_ => e.owner) frontHistory) :
    callerOutsideCheck owners scope (historyPhysical frontHistory ++
      [.clauseBoundary handler owner occurrence dynamicTicket none]) = true := by
  cases origin with
  | inactive canonical => rfl
  | @clause rest callerHandler callerOwner callerOccurrence callerTicket saved originalPhysical oldFront outside canonical path =>
    have different : callerHandler ≠ handler ∨ callerOwner ≠ owner := installed_clause_miss past unique sameScope
    have miss := PassFront.prefix_miss front
    rcases different with h | h <;>
      simpa [callerOutsideCheck,prefixMiss,List.all_append,frameMiss,h,historyPhysical] using miss

private theorem restore_outside_miss
    (origin : CurrentScopeOrigin graph owners scope physical)
    (same : physical = kept ++ outside) (position : ScopeOutside origin kept)
    (checked : callerOutsideCheck owners scope added = true) :
    CurrentScopeOrigin graph owners scope (kept ++ (added ++ outside)) := by
  cases position with
  | inactive canonical => exact .inactive canonical
  | clause canonical path bound =>
    obtain ⟨remaining,retained,_,keptMiss⟩ := OwnerPath.drop_prefix path same bound
    exact .clause canonical (OwnerPath.prepend_checked
      (OwnerPath.prepend_checked retained checked) keptMiss)

theorem outside_restored_scope {graph : Graph} {kind : PairApplication} {original capturedFrom current : Endpoint graph}
    {pastRun : Prefix graph original} {ready : EntryReady kind original}
    (before : BeforeCapture pastRun ready capturedFrom beforeCount) (input : CaptureInput capturedFrom)
    (run : AfterCapture input current afterCount) (unique : UniqueHandlerSites graph)
    (metadata : selectedCallerCheck original.owners ready.plain.scope
      (location capturedFrom input.index).owners (location capturedFrom input.index).data.scope = true)
    (position : callerOutsideCheck original.owners ready.plain.scope (dormant before input).kept = true) :
    CurrentScopeOrigin graph original.owners ready.plain.scope
      ((dormant before input).kept ++ (run.carrier.front ++
        .clauseBoundary (location capturedFrom input.index).installation.handler input.selectedClause.owner
          (location capturedFrom input.index).data.activation capturedFrom.state.nextOwner none ::
          (location capturedFrom input.index).outside)) := by
  have equalities := selectedCallerCheck_exact metadata
  have past : GeneralClausePast graph original.owners
      (location capturedFrom input.index).installation.handler input.selectedClause.owner
      (location capturedFrom input.index).data.activation capturedFrom.state.nextOwner
      ((location capturedFrom input.index).inside ++ [.handlerBoundary (location capturedFrom input.index).site
        (location capturedFrom input.index).environment (location capturedFrom input.index).data.activation])
      (location capturedFrom input.index).data := equalities.1 ▸ (capture_data input).installation
  have originalOrigin := (pastRun.receipt ready).saved.origin
  simpa only [List.append_assoc,List.singleton_append,historyPhysical] using restore_outside_miss originalOrigin (dormant_original_tail before input)
    (scope_outside_computed originalOrigin (dormant_original_tail before input) position)
    (inserted_miss originalOrigin past equalities.2 unique
      (AfterCapture.caller_front_pass run _ _))

#print axioms AfterCapture.caller_front_pass
#print axioms PassFront.prefix_miss
#print axioms selectedCallerCheck_exact
#print axioms scope_outside_computed
#print axioms outside_restored_scope
end Ash.OneShot.CoreCallableStrictOutsideHeadOrigins
