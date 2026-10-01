import CoreCallableCleanupOrigins
import CoreGeneralProjection

/-! Bounded running-cleanup receipt movement. Original installation receipts
remain attached to the same ActionData and saved value. A current owner path
anchored inside the restored suffix permits arbitrary work inserted BELOW its
first match. Outside-anchored paths and armed projection history remain open. -/
namespace Ash.OneShot.CoreCallableCleanupReachableTransport
open ScopedExpressions ScopedExecution CoreTranslation CoreMachine CoreValueRelation
open CoreStrictStack CoreStrictFrames CoreCleanupFrames CoreCleanupRunFrames
open CoreGeneralStack CoreGeneralCaptureResume CoreGeneralRestoration
open CoreCallableReachableResume CoreCallableCleanupOrigins

 theorem OwnerPath.append_suffix
    (path : OwnerPath handler owner occurrence dynamicTicket saved physical front outside)
    (suffix : List CoreMachine.Frame) :
    OwnerPath handler owner occurrence dynamicTicket saved (physical ++ suffix) front (outside ++ suffix) := by
  induction path with
  | hit outside => exact .hit _
  | skip frame miss next ih => exact .skip frame miss ih

 theorem OwnerPath.take_prefix
    (path : OwnerPath handler owner occurrence dynamicTicket saved physical front tail)
    (same : physical = kept ++ outside)
    (inside : front.length < kept.length) :
    ∃ prefixTail, OwnerPath handler owner occurrence dynamicTicket saved kept front prefixTail := by
  induction path generalizing kept with
  | hit tail =>
      cases kept with
      | nil => simp at inside
      | cons frame rest =>
          obtain ⟨rfl, _⟩ := List.cons.inj same
          exact ⟨rest, .hit rest⟩
  | skip frame miss next ih =>
      cases kept with
      | nil => simp at inside
      | cons head rest =>
          obtain ⟨rfl, tailSame⟩ := List.cons.inj same
          obtain ⟨prefixTail, path⟩ := ih tailSame (by simpa using inside)
          exact ⟨prefixTail, .skip frame miss path⟩

/-- A current-position bound on the SAME original first owner path. It makes
no claim about desired future scope or a separately selected installation. -/
inductive ScopeInside {graph : CoreSyntax.Graph} :
    {owners : OwnerMap} → {scope : Execution.Scope} → {physical : List CoreMachine.Frame} →
    CurrentScopeOrigin graph owners scope physical → List CoreMachine.Frame → Prop where
  | inactive (canonical : CanonicalOwnerMap graph owners) :
      ScopeInside (.inactive (physical := physical) canonical) kept
  | clause (canonical : CanonicalOwnerMap graph owners)
      (path : OwnerPath handler owner occurrence dynamicTicket saved physical front outside)
      (inside : front.length < kept.length) : ScopeInside (.clause canonical path) kept

 theorem CurrentScopeOrigin.restore_inside
    (origin : CurrentScopeOrigin graph owners scope physical)
    (same : physical = kept ++ oldOutside) (inside : ScopeInside origin kept)
    (nextOutside : List CoreMachine.Frame) :
    CurrentScopeOrigin graph owners scope (kept ++ nextOutside) := by
  cases inside with
  | inactive canonical => exact .inactive canonical
  | clause canonical path bound =>
      obtain ⟨prefixTail, preserved⟩ := OwnerPath.take_prefix path same bound
      exact .clause canonical (OwnerPath.append_suffix preserved nextOutside)

/-- Same delayed callback and original installation scope proof, kept dormant.
Normal completion's actual saved value is authenticated at its ORIGINAL map. -/
structure RunningReceipt (graph : CoreSyntax.Graph) (owners : OwnerMap) (heap : CoreMachine.Heap)
    (action : CoreSyntax.NodeRef) (environment : CoreMachine.Environment)
    (data : ActionData) (savedValue : CoreMachine.Value) (savedCode : Code)
    (originalPhysical : List CoreMachine.Frame) : Prop where
  installed : SavedCleanupOrigin graph owners heap action environment data originalPhysical
  value : ValueRel graph owners heap savedValue savedCode

 theorem RunningReceipt.heap_weaken
    (receipt : RunningReceipt graph owners heap action environment data savedValue savedCode originalPhysical)
    (extension : HeapExtends heap larger) :
    RunningReceipt graph owners larger action environment data savedValue savedCode originalPhysical :=
  ⟨receipt.installed.heap_weaken extension,receipt.value.heap_weaken extension⟩

 theorem RunningReceipt.restore_inside
    (receipt : RunningReceipt graph owners heap action environment data savedValue savedCode originalPhysical)
    (same : originalPhysical = kept ++ oldOutside)
    (inside : ScopeInside receipt.installed.origin kept) (nextOutside : List CoreMachine.Frame) :
    RunningReceipt graph owners heap action environment data savedValue savedCode (kept ++ nextOutside) :=
  ⟨⟨receipt.installed.delayed,CurrentScopeOrigin.restore_inside receipt.installed.origin same inside nextOutside⟩,receipt.value⟩

/-- Any actual capture containing this running completion is protected at the
physical level, including deeper nesting inside other kept owner captures. -/
 theorem running_capture_protected (front tail : List CoreMachine.Frame)
    (data : ActionData) (savedValue : CoreMachine.Value) :
    ProtectedCapture (front ++ .cleanupCompletion data.identity savedValue :: tail) :=
  ProtectedCapture.prepend .cleanup front

 theorem running_capture_no_projection (front tail : List CoreMachine.Frame)
    (data : ActionData) (savedValue : CoreMachine.Value) (fuel : Nat) :
    ∀ closing observations,
      CoreMachine.closeFuel fuel (front ++ .cleanupCompletion data.identity savedValue :: tail) ≠ .ok (closing,observations) :=
  (running_capture_protected front tail data savedValue).close_no_success fuel


/-- Actual entry produces the running receipt from the SAME installed caller
origin and SAME saved value; callback entry still uses current scope.none. -/
theorem running_start_owned {base : CoreMachine.State}
    (receipt : SavedCleanupOrigin graph cleanupOwners base.heap action environment data physical)
    (saved : ValueRel graph callerOwners base.heap savedValue savedCode)
    (outside : GeneralSegment graph base.heap physical lexical)
    (bounded : TicketBound base (.push (.armed data) lexical)) (scope : Execution.Scope) :
    GeneralStepWitness graph
      ⟨returnedState base savedValue (.cleanupBoundary action environment data.identity :: physical),
        .eval ⟨savedCode,scope,.push (.armed data) lexical⟩,callerOwners,[]⟩
      ⟨startedState base action environment data.identity savedValue physical,
        .eval ⟨.app data.action .unit,.none,.push (.running data savedCode saved.closed) lexical⟩,cleanupOwners,[]⟩ [] [] ∧
    CurrentOwnership graph cleanupOwners
      (startedState base action environment data.identity savedValue physical) .none
      (.push (.running data savedCode saved.closed) lexical) ∧
    RunningReceipt graph cleanupOwners
      (startedState base action environment data.identity savedValue physical).heap
      action environment data savedValue savedCode physical := by
  obtain ⟨step, current, installed⟩ := normal_start_owned receipt saved outside bounded scope
  exact ⟨step,current,installed,saved.owner_transport cleanupOwners⟩

/-- The actual full-prefix resume and Unit completion use the same dormant
receipt. Its original first owner path lies in the restored captured suffix;
all intervening front frames and the spent marker occur strictly below it. -/
theorem resume_then_finish_inside {base : CoreMachine.State} {ticket : Nat}
    (receipt : RunningReceipt graph cleanupOwners base.heap action environment actionData savedValue savedCode originalPhysical)
    (cut : GeneralOwnerCut graph base.heap handler owner whole target front frontTarget savedOwners occurrence ticket data result
      (.cleanupCompletion actionData.identity savedValue :: capturedPhysical)
      (.push (.running actionData savedCode receipt.value.closed) capturedTarget) outside outsideTarget)
    (original : originalPhysical = capturedPhysical ++ oldOutside)
    (inside : ScopeInside receipt.installed.origin capturedPhysical)
    (capturedTail : GeneralSegment graph base.heap capturedPhysical capturedTarget)
    (frame : CoreResumeFrames.ResumeRel graph frameOwners base.heap (.resume handler owner) plain)
    (context : plain.context = .resume binder) (resolve : plain.scope.resolve binder = some ticket)
    (bounded : TicketBound base target)
    (activeOwners : CoreTranslation.OwnerMap) (runtimeScope : Scope) :
    let resumed := resumeAfter base handler owner occurrence ticket .unit
      (.cleanupCompletion actionData.identity savedValue :: capturedPhysical) front outside
    let restPhysical := capturedPhysical ++ front ++ .clauseBoundary handler owner occurrence ticket none :: outside
    let restTarget := capturedTarget.append (frontTarget.append (.spent ticket data.answer data.scope outsideTarget))
    GeneralChain graph
      ⟨resumeBefore base handler owner .unit whole,.eval ⟨.resume binder .unit,plain.scope,target⟩,activeOwners,[(frameOwners,.resume handler owner)]⟩
      [⟨resumed,.eval ⟨.unit,plain.scope,.push (.running actionData savedCode receipt.value.closed) restTarget⟩,activeOwners,[]⟩,
       ⟨observedState resumed savedValue restPhysical (.cleanupFinished actionData.identity),.eval ⟨savedCode,actionData.scope,restTarget⟩,cleanupOwners,[]⟩]
      ⟨observedState resumed savedValue restPhysical (.cleanupFinished actionData.identity),.eval ⟨savedCode,actionData.scope,restTarget⟩,cleanupOwners,[]⟩
      [] [.cleanup actionData.identity,.ticket ticket] ∧
    CurrentOwnership graph cleanupOwners
      (observedState resumed savedValue restPhysical (.cleanupFinished actionData.identity))
      actionData.scope restTarget := by
  dsimp only
  have chain := resume_then_normal_finish receipt.value cut receipt.installed.delayed capturedTail frame context resolve activeOwners runtimeScope
  obtain ⟨found,shape,header,current,frontSegment,capturedSegment,outsideSegment⟩ := cut.realizes
  let restPhysical := capturedPhysical ++ front ++ .clauseBoundary handler owner occurrence ticket none :: outside
  let restTarget := capturedTarget.append (frontTarget.append (.spent ticket data.answer data.scope outsideTarget))
  let resumed := resumeAfter base handler owner occurrence ticket .unit
    (.cleanupCompletion actionData.identity savedValue :: capturedPhysical) front outside
  have kept := receipt.restore_inside original inside (front ++ .clauseBoundary handler owner occurrence ticket none :: outside)
  have restoredReceipt : SavedCleanupOrigin graph cleanupOwners resumed.heap action environment actionData restPhysical := by
    simpa [resumed,resumeAfter,restPhysical,List.append_assoc] using kept.installed
  have remaining : GeneralSegment graph resumed.heap restPhysical restTarget := by
    simpa [resumed,resumeAfter,restPhysical,restTarget,List.append_assoc] using
      capturedTail.append (frontSegment.append (.spent (ticket := ticket) header outsideSegment))
  have raw : RawStep ⟨.resume binder .unit,plain.scope,target⟩
      ⟨.unit,plain.scope,.push (.running actionData savedCode receipt.value.closed) restTarget⟩ [] [.ticket ticket] := by
    rw [shape]
    simpa [Stack.append,restTarget] using
      (RawStep.resume binder ticket plain.scope data.scope result data.answer frontTarget
        (.push (.running actionData savedCode receipt.value.closed) capturedTarget) outsideTarget .unit
        (by simp [ClosedValue, Code.IsValue, Code.ResourceClosed, Code.freeNames, Code.dependencies]) resolve)
  have events : CoreTicketHistory.capturedTickets resumed.observations =
      CoreTicketHistory.capturedTickets base.observations ++ issuedTickets [] := by
    simp [resumed,resumeAfter,CoreTicketHistory.capturedTickets,issuedTickets]
  have restoredBound := bounded.step raw events
  have saved : ValueRel graph cleanupOwners resumed.heap savedValue savedCode := receipt.value
  obtain ⟨finish, ownership⟩ := normal_finish_owned restoredReceipt saved remaining restoredBound activeOwners plain.scope
  exact ⟨chain,ownership⟩


/-- Actual capture stores the SAME completion frame, entire callback data and
saved value receipt in its dormant physical prefix. The current clause family
and complete target capture remain those selected by the SAME actual cut. -/
theorem capture_running_owned {base : CoreMachine.State}
    (receipt : RunningReceipt graph cleanupOwners base.heap action cleanupEnvironment actionData savedValue savedCode
      (capturedRest ++ .handlerBoundary site handlerEnvironment data.activation :: outside))
    (cut : GeneralHandlerCut graph base.heap requested whole target
      (captureFront ++ .cleanupCompletion actionData.identity savedValue :: capturedRest)
      savedOwners site handlerEnvironment data outside
      (Stack.append capFront (.push (.running actionData savedCode receipt.value.closed) capRest)) tail)
    (known : graph.node site = some node) (kind : node.kind = .handler handler handled handlerBody clauses)
    (selected : clauses.find? (fun clause => clause.operation == operation) = some clause)
    (operand : ValueRel graph operandOwners base.heap value operandCode)
    (requestCarrier : EnvCloses graph operandOwners base.heap requestEnvironment
      (.perform effect operation .unit) (.perform (Instantiation.freezeEffect requested) operation .unit))
    (plain : PlainData) (context : plain.context = .perform (Instantiation.freezeEffect requested) operation)
    (ready : ∀ parameter binder body, ClauseAt operation data.clauses parameter binder body → ClosedExcept parameter body)
    (operationResult : Ty) (runtimeScope : Scope) :
    ∃ fuel argument rawBody body,
      clause.argument = .binder argument ∧
      ClauseAt operation data.clauses argument.id (CoreTranslation.ticket graph clause.owner) body ∧
      CoreTranslation.translateFuel graph fuel
        (⟨handler,clause.owner,CoreTranslation.ticket graph clause.owner⟩ :: savedOwners) clause.body = .ok rawBody ∧
      EnvCloses graph (⟨handler,clause.owner,CoreTranslation.ticket graph clause.owner⟩ :: savedOwners)
        base.heap (.binding argument.id value handlerEnvironment) rawBody (body.subst argument.id operandCode) ∧
      CoreRequestFrames.OwnerHeader graph savedOwners base.heap handler clause.owner data.activation data ∧
      GeneralStepWitness graph
        ⟨captureBefore base value effect operation requestEnvironment whole,
          .eval ⟨.perform (Instantiation.freezeEffect requested) operation operandCode,plain.scope,target⟩,
          operandOwners,[(operandOwners,.request effect operation requestEnvironment)]⟩
        ⟨captureAfter base clause argument.id value handler data.activation site handlerEnvironment
          (captureFront ++ .cleanupCompletion actionData.identity savedValue :: capturedRest) outside,
          .eval ⟨body.subst argument.id operandCode,.ticket (CoreTranslation.ticket graph clause.owner) base.nextOwner,
            .live base.nextOwner operationResult data.answer
              (Stack.append capFront (.push (.running actionData savedCode receipt.value.closed) capRest)) data.scope tail⟩,
          ⟨handler,clause.owner,CoreTranslation.ticket graph clause.owner⟩ :: savedOwners,[]⟩ [.ticket base.nextOwner] [] ∧
      RunningReceipt graph cleanupOwners base.heap action cleanupEnvironment actionData savedValue savedCode
        (capturedRest ++ .handlerBoundary site handlerEnvironment data.activation :: outside) ∧
      ProtectedCapture ((captureFront ++ .cleanupCompletion actionData.identity savedValue :: capturedRest) ++
        [.handlerBoundary site handlerEnvironment data.activation]) := by
  obtain ⟨fuel,argument,rawBody,body,pattern,selectedAt,translation,closed,header,step⟩ :=
    capture_general cut known kind selected operand requestCarrier plain context ready operationResult runtimeScope
  exact ⟨fuel,argument,rawBody,body,pattern,selectedAt,translation,closed,header,step,receipt,
    (running_capture_protected captureFront capturedRest actionData savedValue).append _⟩

/-- Generic obstruction: an inserted first frame with the same static pair
must determine its own dynamic ticket, regardless of distinct old tickets.
This is not a new finite program example or a static-pair uniqueness rule. -/
theorem OwnerPath.first_pair_ticket
    (path : OwnerPath handler owner occurrence dynamicTicket saved
      (.clauseBoundary handler owner newOccurrence newTicket newSaved :: physical) front outside) :
    dynamicTicket = newTicket := by
  cases path with
  | hit => rfl
  | skip frame miss next =>
      rcases miss handler owner newOccurrence newTicket newSaved rfl with impossible | impossible
      all_goals exact False.elim (impossible rfl)

theorem outside_static_shadow_obstruction (different : oldTicket ≠ newTicket) :
    ¬ OwnerPath handler owner oldOccurrence oldTicket oldSaved
      (.clauseBoundary handler owner newOccurrence newTicket none :: physical) front outside := by
  intro path
  exact different (OwnerPath.first_pair_ticket path)

#print axioms OwnerPath.append_suffix
#print axioms OwnerPath.take_prefix
#print axioms CurrentScopeOrigin.restore_inside
#print axioms RunningReceipt.heap_weaken
#print axioms RunningReceipt.restore_inside
#print axioms running_capture_protected
#print axioms running_capture_no_projection
#print axioms running_start_owned
#print axioms resume_then_finish_inside
#print axioms capture_running_owned
#print axioms OwnerPath.first_pair_ticket
#print axioms outside_static_shadow_obstruction
end Ash.OneShot.CoreCallableCleanupReachableTransport
