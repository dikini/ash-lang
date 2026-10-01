import CoreCallableResumeCorrespondence
import CoreTicketHistory
import CoreStrictFocus

/-! Current ownership receipts for the admitted resume correspondence.
Actual capture produces the generated scope and a ticket bound; non-value bind
and resume focus save the same frame's own map/scope at its physical suffix.
Beta resets current callable capabilities while those saved receipts retain
identity, and actual frame return recovers their scope. The connected consumers
use the actual Core initial history to derive name uniqueness and the same
current Source primitive to derive runtime resolution.

This is explicit producer coverage for capture, beta, bind and resume operands.
It does not derive coherence from arbitrary GeneralSegment/GeneralChain data or
cover every projected cleanup, disposal, handler exit or restored saved-prefix
scope transition. These receipts do not establish Rust capacity or allocation
success. Their input source, private families and full admitted contracts stay
those of the existing capture/resume correspondence. -/
namespace Ash.OneShot.CoreCallableReachableResume
open ScopedExpressions ScopedExecution CoreTranslation CoreMachine
open CoreGeneralCaptureResume CoreGeneralStack CoreResumeFrames CoreValueRelation CoreRequestFrames CoreStrictStack CoreStrictFrames

/-- The translator's static owner entries retain their generated lexical binder.
Dynamic tickets belong to current scope receipts, not this static map. -/
def CanonicalOwnerMap (graph : CoreSyntax.Graph) (owners : OwnerMap) : Prop :=
  ∀ binding ∈ owners, binding.ticket = CoreTranslation.ticket graph binding.owner

theorem CanonicalOwnerMap.empty (graph : CoreSyntax.Graph) : CanonicalOwnerMap graph [] := by
  intro binding member
  cases member

theorem CanonicalOwnerMap.clause (canonical : CanonicalOwnerMap graph owners) :
    CanonicalOwnerMap graph (⟨handler, owner, CoreTranslation.ticket graph owner⟩ :: owners) := by
  intro binding member
  cases member with
  | head => rfl
  | tail _ member => exact canonical _ member

/-- A successful static lookup at the generated binder identifies the same
clause owner. The current head then identifies the same handler. -/
theorem CanonicalOwnerMap.resolve_head
    (canonical : CanonicalOwnerMap graph (⟨handler, owner, CoreTranslation.ticket graph owner⟩ :: owners))
    (resolved : resolveOwner (⟨handler, owner, CoreTranslation.ticket graph owner⟩ :: owners)
      site requestedHandler requestedOwner = .ok (CoreTranslation.ticket graph owner)) :
    requestedHandler = handler ∧ requestedOwner = owner := by
  cases selected : List.find? (fun binding : OwnerBinding => binding.owner == requestedOwner)
      (⟨handler, owner, CoreTranslation.ticket graph owner⟩ :: owners) with
  | none => simp [resolveOwner, selected] at resolved
  | some binding =>
    have member := List.mem_of_find?_eq_some selected
    have ownerSame : binding.owner = requestedOwner := by simpa using List.find?_some selected
    have generated := canonical binding member
    by_cases handlerSame : binding.handler = requestedHandler
    · have ticketSame : binding.ticket = CoreTranslation.ticket graph owner := by
        simpa [resolveOwner, selected, handlerSame, Pure.pure, Except.pure] using resolved
      have sameOwner : requestedOwner = owner := CoreTranslation.ticket_injective graph _ _
        (ownerSame ▸ generated.symm.trans ticketSame)
      have selectedHead : binding = ⟨handler, owner, CoreTranslation.ticket graph owner⟩ := by
        rw [sameOwner] at selected
        simpa using selected.symm
      exact ⟨by simpa [selectedHead] using handlerSame.symm, sameOwner⟩
    · simp [resolveOwner, selected, handlerSame, Pure.pure, Except.pure, Bind.bind, Except.bind] at resolved

/-- A structural first matching physical owner occurrence. Dormant captures are
not searched; unrelated active clause frames may occur in the front. -/
inductive OwnerPath (handler owner occurrence dynamicTicket : Nat)
    (saved : Option (List CoreMachine.Frame)) : List CoreMachine.Frame → List CoreMachine.Frame →
    List CoreMachine.Frame → Prop where
  | hit (outside : List CoreMachine.Frame) :
      OwnerPath handler owner occurrence dynamicTicket saved
        (.clauseBoundary handler owner occurrence dynamicTicket saved :: outside) [] outside
  | skip (frame : CoreMachine.Frame)
      (miss : ∀ candidate selected activation ticket capture,
        frame = .clauseBoundary candidate selected activation ticket capture →
        handler ≠ candidate ∨ owner ≠ selected)
      (next : OwnerPath handler owner occurrence dynamicTicket saved whole front outside) :
      OwnerPath handler owner occurrence dynamicTicket saved
        (frame :: whole) (frame :: front) outside

theorem OwnerPath.lookup (path : OwnerPath handler owner occurrence dynamicTicket saved whole front outside) :
    findOwner handler owner whole = match saved with
      | none => .error (.consumedOwner handler owner)
      | some captured => .ok ⟨front, handler, owner, occurrence, dynamicTicket, captured, outside⟩ := by
  induction path with
  | hit outside => cases saved <;> simp [findOwner]
  | skip frame miss next ih =>
    cases frame
    case clauseBoundary candidate selected activation ticket capture =>
      have different := miss candidate selected activation ticket capture rfl
      rcases different with different | different
      all_goals cases saved <;> simp [findOwner, different, ih, Bind.bind, Except.bind, Pure.pure, Except.pure]
    all_goals cases saved <;> simp [findOwner, ih, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Capture-generated current lexical scope, linked to the first physical
occurrence of that same static clause owner. Saved frame scopes keep their own
maps and below-frame path when a callee enters the empty capability map. -/
inductive CurrentScopeOrigin (graph : CoreSyntax.Graph) : OwnerMap → Execution.Scope →
    List CoreMachine.Frame → Prop where
  | inactive (canonical : CanonicalOwnerMap graph owners) :
      CurrentScopeOrigin graph owners .none physical
  | clause (canonical : CanonicalOwnerMap graph owners)
      (path : OwnerPath handler owner occurrence dynamicTicket saved physical front outside) :
      CurrentScopeOrigin graph
        (⟨handler, owner, CoreTranslation.ticket graph owner⟩ :: owners)
        (.ticket (CoreTranslation.ticket graph owner) dynamicTicket) physical

/-- A saved ordinary frame retains the map and runtime scope that were current
when that same frame was installed. Its owner path concerns the suffix below
this frame, so a callee's empty current map cannot replace this receipt. -/
structure SavedFrameOrigin (graph : CoreSyntax.Graph) (owners : OwnerMap) (heap : CoreMachine.Heap)
    (frame : CoreMachine.Frame) (plain : PlainData) (below : List CoreMachine.Frame) : Prop where
  related : PlainFrameRel graph owners heap frame plain
  origin : CurrentScopeOrigin graph owners plain.scope below

theorem CurrentScopeOrigin.prepend_plain
    (origin : CurrentScopeOrigin graph owners scope below)
    (related : PlainFrameRel graph owners heap frame plain) :
    CurrentScopeOrigin graph owners scope (frame :: below) := by
  have miss : ∀ handler owner candidate selected activation ticket capture,
      frame = .clauseBoundary candidate selected activation ticket capture →
      handler ≠ candidate ∨ owner ≠ selected := by
    intro handler owner candidate selected activation ticket capture same
    change FrameRel graph owners heap frame plain.context at related
    generalize contextSame : plain.context = context at related
    cases related <;> cases same
  cases origin with
  | inactive canonical => exact .inactive canonical
  | clause canonical path => exact .clause canonical (.skip frame (miss _ _) path)

theorem SavedFrameOrigin.install
    (origin : CurrentScopeOrigin graph owners plain.scope below)
    (related : PlainFrameRel graph owners heap frame plain) :
    SavedFrameOrigin graph owners heap frame plain below :=
  ⟨related, origin⟩

/-- The static bind body and environment are inverted from this same retained
frame proof before the actual return rule is instantiated. -/
theorem SavedFrameOrigin.bind_static
    (receipt : SavedFrameOrigin graph owners heap (.bind parameter body environment) plain below)
    (context : plain.context = .bind parameter suffix) :
    ∃ fuel rawBody,
      CoreTranslation.translateFuel graph fuel owners body = .ok rawBody ∧
      EnvCloses graph owners heap environment (.lambda parameter rawBody) (.lambda parameter suffix) ∧
      ClosedExcept parameter suffix := by
  have related : FrameRel graph owners heap (.bind parameter body environment) (.bind parameter suffix) := by
    simpa [PlainFrameRel, context] using receipt.related
  cases related with
  | bind translated saved ready => exact ⟨_, _, translated, saved, ready⟩

/-- Resume operand evaluation saves its own static map and lexical runtime
scope at the actual below-frame suffix. It does not borrow the callee's map. -/
structure SavedResumeOrigin (graph : CoreSyntax.Graph) (owners : OwnerMap) (heap : CoreMachine.Heap)
    (handler owner : Nat) (plain : PlainData) (below : List CoreMachine.Frame) : Prop where
  related : ResumeRel graph owners heap (.resume handler owner) plain
  origin : CurrentScopeOrigin graph owners plain.scope below

theorem CurrentScopeOrigin.prepend_resume
    (origin : CurrentScopeOrigin graph owners scope below) :
    CurrentScopeOrigin graph owners scope (.resume handler owner :: below) := by
  cases origin with
  | inactive canonical => exact .inactive canonical
  | clause canonical path =>
    exact .clause canonical (.skip _ (by intro _ _ _ _ _ impossible; cases impossible) path)

/-- Only the ticket component of name history is needed for this consumer.
It includes dormant and spent target names and uses the actual Core history. -/
def TicketBound (state : CoreMachine.State) (target : Stack) : Prop :=
  ∀ ticket, target.erase.ticketNames.count ticket ≤
    (CoreTicketHistory.capturedTickets state.observations).count ticket

theorem TicketBound.empty (state : CoreMachine.State) : TicketBound state .nil := by
  intro ticket
  simp [Stack.erase, Control.ticketNames]

theorem TicketBound.names (bounded : TicketBound state target)
    (history : CoreTicketHistory.History state) : target.erase.ticketNames.Nodup := by
  exact List.nodup_iff_count.mpr fun ticket =>
    Nat.le_trans (bounded ticket) (List.nodup_iff_count.mp (CoreTicketHistory.history_nodup state history) ticket)

def issuedTickets (created : List Owner) : List Nat :=
  created.filterMap fun owner => match owner with | .ticket ticket => some ticket | _ => none

private theorem issuedTickets_count (created : List Owner) (ticket : Nat) :
    (issuedTickets created).count ticket = created.count (.ticket ticket) := by
  induction created with
  | nil => rfl
  | cons owner rest ih =>
    simp only [issuedTickets] at ih
    cases owner <;> simp [issuedTickets, List.count_cons, ih]

/-- Actual event coupling transports the current ticket bound. The concrete
capture/noncapture factories derive this observation equation from their Core
rule; it is not a future source or name-uniqueness assumption. -/
theorem TicketBound.step
    (bounded : TicketBound before beforeTarget.stack)
    (raw : RawStep beforeTarget afterTarget created discharged)
    (events : CoreTicketHistory.capturedTickets after.observations =
      CoreTicketHistory.capturedTickets before.observations ++ issuedTickets created) :
    TicketBound after afterTarget.stack := by
  intro ticket
  have names := (raw_step_name_bounds raw ticket 0).1
  have previous := bounded ticket
  rw [events, List.count_append, issuedTickets_count]
  omega

structure CurrentOwnership (graph : CoreSyntax.Graph) (owners : OwnerMap)
    (state : CoreMachine.State) (scope : Execution.Scope) (target : Stack) : Prop where
  tickets : TicketBound state target
  scopeOrigin : CurrentScopeOrigin graph owners scope state.frames

theorem CurrentOwnership.initial (graph : CoreSyntax.Graph) :
    CurrentOwnership graph [] (CoreMachine.initial graph) .none .nil :=
  ⟨TicketBound.empty _, .inactive (CanonicalOwnerMap.empty _)⟩

theorem capture_owned {base : CoreMachine.State}
    (bounded : TicketBound base target)
    (canonical : CanonicalOwnerMap graph savedOwners)
    (cut : GeneralHandlerCut graph base.heap requested whole target inside savedOwners site environment data outside cap tail)
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
        base.heap (.binding argument.id value environment) rawBody (body.subst argument.id operandCode) ∧
      OwnerHeader graph savedOwners base.heap handler clause.owner data.activation data ∧
      GeneralStepWitness graph
        ⟨captureBefore base value effect operation requestEnvironment whole,
          .eval ⟨.perform (Instantiation.freezeEffect requested) operation operandCode,plain.scope,target⟩,
          operandOwners,[(operandOwners,.request effect operation requestEnvironment)]⟩
        ⟨captureAfter base clause argument.id value handler data.activation site environment inside outside,
          .eval ⟨body.subst argument.id operandCode,.ticket (CoreTranslation.ticket graph clause.owner) base.nextOwner,
            .live base.nextOwner operationResult data.answer cap data.scope tail⟩,
          ⟨handler,clause.owner,CoreTranslation.ticket graph clause.owner⟩ :: savedOwners,[]⟩ [.ticket base.nextOwner] [] ∧
      CurrentOwnership graph
        (⟨handler, clause.owner, CoreTranslation.ticket graph clause.owner⟩ :: savedOwners)
        (captureAfter base clause argument.id value handler data.activation site environment inside outside)
        (.ticket (CoreTranslation.ticket graph clause.owner) base.nextOwner)
        (.live base.nextOwner operationResult data.answer cap data.scope tail) := by
  obtain ⟨fuel, argument, rawBody, body, pattern, selectedBody, translated, closed, header, step⟩ :=
    capture_general cut known kind selected operand requestCarrier plain context ready operationResult runtimeScope
  have raw : RawStep
      ⟨.perform (Instantiation.freezeEffect requested) operation operandCode, plain.scope, target⟩
      ⟨body.subst argument.id operandCode, .ticket (CoreTranslation.ticket graph clause.owner) base.nextOwner,
        .live base.nextOwner operationResult data.answer cap data.scope tail⟩ [.ticket base.nextOwner] [] :=
    .capture _ _ _ _ _ _ _ _ _ _ _ _ _ cut.realizes.2.1 selectedBody operand.closed (ready _ _ _ selectedBody)
  have events : CoreTicketHistory.capturedTickets
      (captureAfter base clause argument.id value handler data.activation site environment inside outside).observations =
      CoreTicketHistory.capturedTickets base.observations ++ issuedTickets [.ticket base.nextOwner] := by
    simp [captureAfter, CoreTicketHistory.capturedTickets, issuedTickets]
  have owned : CurrentOwnership graph
      (⟨handler, clause.owner, CoreTranslation.ticket graph clause.owner⟩ :: savedOwners)
      (captureAfter base clause argument.id value handler data.activation site environment inside outside)
      (.ticket (CoreTranslation.ticket graph clause.owner) base.nextOwner)
      (.live base.nextOwner operationResult data.answer cap data.scope tail) :=
    ⟨bounded.step raw events, .clause canonical (.hit outside)⟩
  exact ⟨fuel, argument, rawBody, body, pattern, selectedBody, translated, closed, header, step, owned⟩

/-- Actual beta enters the callable's empty capability map. The older physical
suffix and heap, and hence every saved frame receipt on that suffix, are the
same; this reset concerns only the current expression. -/
theorem beta_owned {base : CoreMachine.State}
    (bounded : TicketBound base target)
    (function : ValueRel graph owners base.heap (.closure parameter body saved) (.lambda parameter result))
    (argument : ValueRel graph owners base.heap value argumentCode)
    (coreTail : List CoreMachine.Frame) (scope : Execution.Scope) :
    CoreStrictSteps.ApplicationWitness graph owners base parameter body saved value argumentCode result coreTail scope target ∧
    CurrentOwnership graph []
      {base with control := .evaluate body (.binding parameter value saved), frames := coreTail} .none target := by
  exact ⟨CoreStrictSteps.application_complete function argument coreTail scope target,
    bounded, .inactive (CanonicalOwnerMap.empty _)⟩

theorem SavedFrameOrigin.beta_survives {base : CoreMachine.State}
    (receipt : SavedFrameOrigin graph owners base.heap frame plain below) :
    SavedFrameOrigin graph owners
      ({base with control := .evaluate body (.binding parameter value saved), frames := coreTail} : CoreMachine.State).heap
      frame plain below := receipt

theorem bind_focus_owned {base : CoreMachine.State}
    (known : graph.node site = some node) (kind : node.kind = .bind binder initializer body)
    (it : CoreTranslation.translateFuel graph fuel owners initializer = .ok rawInitializer)
    (bt : CoreTranslation.translateFuel graph fuel owners body = .ok rawBody)
    (current : EnvCloses graph owners base.heap environment
      (.bind binder.id rawInitializer rawBody) (.bind binder.id initializerCode suffix))
    (notValue : ¬ initializerCode.IsValue) (ready : ClosedExcept binder.id suffix)
    (plain : PlainData) (context : plain.context = .bind binder.id suffix)
    (ownership : CurrentOwnership graph owners {base with frames := framesOf annotations} plain.scope target)
    (older : PushedWithMaps graph base.heap annotations target) :
    ComponentMapped graph owners annotations
      {base with control := .evaluate site environment, frames := framesOf annotations}
      ⟨.bind binder.id initializerCode suffix,plain.scope,target⟩ ∧
    CoreMachine.next graph {base with control := .evaluate site environment, frames := framesOf annotations} =
      .stepped {base with control := .evaluate initializer environment, frames := .bind binder.id body environment :: framesOf annotations, observations := base.observations ++ [.entered site]} ∧
    RawStep ⟨.bind binder.id initializerCode suffix,plain.scope,target⟩ ⟨initializerCode,plain.scope,.push (.plain plain) target⟩ [] [] ∧
    ComponentMapped graph owners ((owners,.bind binder.id body environment) :: annotations)
      {base with control := .evaluate initializer environment, frames := .bind binder.id body environment :: framesOf annotations, observations := base.observations ++ [.entered site]}
      ⟨initializerCode,plain.scope,.push (.plain plain) target⟩ ∧
    CoreInitialPrefix.Link graph
      ⟨{base with control := .evaluate site environment, frames := framesOf annotations},⟨.bind binder.id initializerCode suffix,plain.scope,target⟩,owners,annotations⟩
      ⟨{base with control := .evaluate initializer environment, frames := .bind binder.id body environment :: framesOf annotations, observations := base.observations ++ [.entered site]},⟨initializerCode,plain.scope,.push (.plain plain) target⟩,owners,((owners,.bind binder.id body environment) :: annotations)⟩ ∧
    SavedFrameOrigin graph owners base.heap (.bind binder.id body environment) plain (framesOf annotations) ∧
    CurrentOwnership graph owners
      {base with control := .evaluate initializer environment, frames := .bind binder.id body environment :: framesOf annotations, observations := base.observations ++ [.entered site]} plain.scope (.push (.plain plain) target) := by
  obtain ⟨before, next, raw, after, link⟩ :=
    CoreStrictFocus.bind_focus known kind it bt current notValue ready plain context older
  obtain ⟨initializerSaved, bodySaved⟩ := CoreOrdinaryCompletion.bind_components current
  have related : PlainFrameRel graph owners base.heap (.bind binder.id body environment) plain := by
    change FrameRel graph owners base.heap _ plain.context
    rw [context]
    exact .bind bt bodySaved ready
  have events : CoreTicketHistory.capturedTickets (base.observations ++ [.entered site]) =
      CoreTicketHistory.capturedTickets base.observations ++ issuedTickets [] := by
    simp [CoreTicketHistory.capturedTickets, issuedTickets]
  exact ⟨before, next, raw, after, link, ⟨related, ownership.scopeOrigin⟩,
    ownership.tickets.step raw events, ownership.scopeOrigin.prepend_plain related⟩

theorem bind_return_owned {base : CoreMachine.State}
    (argument : ValueRel graph codeOwners base.heap value argumentCode)
    (plain : PlainData) (context : plain.context = .bind parameter suffix)
    (receipt : SavedFrameOrigin graph savedOwners base.heap (.bind parameter body environment) plain (framesOf annotations))
    (bounded : TicketBound base (.push (.plain plain) target))
    (tail : PushedWithMaps graph base.heap annotations target) (runtimeScope : Scope) :
    ComponentMapped graph codeOwners ((savedOwners, .bind parameter body environment) :: annotations)
      { base with control := .returned value, frames := .bind parameter body environment :: framesOf annotations }
      ⟨argumentCode, runtimeScope, .push (.plain plain) target⟩ ∧
    CoreMachine.next graph { base with control := .returned value, frames := .bind parameter body environment :: framesOf annotations } =
      .stepped { base with control := .evaluate body (.binding parameter value environment), frames := framesOf annotations } ∧
    RawStep ⟨argumentCode, runtimeScope, .push (.plain plain) target⟩
      ⟨.bind parameter argumentCode suffix, plain.scope, target⟩ [] [] ∧
    RawStep ⟨.bind parameter argumentCode suffix, plain.scope, target⟩
      ⟨suffix.subst parameter argumentCode, plain.scope, target⟩ [] [] ∧
    ComponentMapped graph savedOwners annotations
      { base with control := .evaluate body (.binding parameter value environment), frames := framesOf annotations }
      ⟨suffix.subst parameter argumentCode, plain.scope, target⟩ ∧
    CurrentOwnership graph savedOwners
      {base with control := .evaluate body (.binding parameter value environment), frames := framesOf annotations}
      plain.scope target := by
  obtain ⟨fuel, rawBody, translated, saved, ready⟩ := receipt.bind_static context
  obtain ⟨before, next, plug, bind, after⟩ :=
    bind_return_mapped translated saved ready argument plain context tail runtimeScope
  have popped : TicketBound base target := bounded.step plug (by simp [issuedTickets])
  have completed : TicketBound
      ({base with control := .evaluate body (.binding parameter value environment), frames := framesOf annotations} : CoreMachine.State)
      target := popped.step bind (by simp [issuedTickets])
  exact ⟨before, next, plug, bind, after, completed, receipt.origin⟩

theorem resume_focus_owned {base : CoreMachine.State}
    (ordered : CoreTranslationFuel.Postorder graph) (known : graph.node site = some node)
    (kind : node.kind = .resume handler owner post operand)
    (translated : CoreTranslation.translateFuel graph fuel owners site = .ok (.resume binder raw))
    (current : EnvCloses graph owners base.heap environment (.resume binder raw) (.resume binder code))
    (notValue : ¬ code.IsValue) (plain : PlainData) (context : plain.context = .resume binder)
    (ownership : CurrentOwnership graph owners {base with frames := framesOf annotations} plain.scope target)
    (older : PushedWithMaps graph base.heap annotations target) :
    ComponentMapped graph owners annotations
      { base with control := .evaluate site environment, frames := framesOf annotations }
      ⟨.resume binder code,plain.scope,target⟩ ∧
    CoreMachine.next graph { base with control := .evaluate site environment, frames := framesOf annotations } =
      .stepped { base with control := .evaluate operand environment, frames := .resume handler owner :: framesOf annotations, observations := base.observations ++ [.entered site] } ∧
    RawStep ⟨.resume binder code,plain.scope,target⟩ ⟨code,plain.scope,.push (.plain plain) target⟩ [] [] ∧
    ComponentMapped graph owners ((owners,.resume handler owner) :: annotations)
      { base with control := .evaluate operand environment, frames := .resume handler owner :: framesOf annotations, observations := base.observations ++ [.entered site] }
      ⟨code,plain.scope,.push (.plain plain) target⟩ ∧
    SavedResumeOrigin graph owners base.heap handler owner plain (framesOf annotations) ∧
    CurrentOwnership graph owners
      {base with control := .evaluate operand environment, frames := .resume handler owner :: framesOf annotations, observations := base.observations ++ [.entered site]}
      plain.scope (.push (.plain plain) target) := by
  obtain ⟨before, next, rawStep, after⟩ :=
    CoreResumeEntry.resume_focus_mapped ordered known kind translated current notValue plain context older
  obtain ⟨operandFuel, resolved, childTranslated⟩ := resume_translation_parts known kind translated
  obtain ⟨_, child, marker⟩ := resume_components current
  have related : ResumeRel graph owners base.heap (.resume handler owner) plain :=
    .operand known kind translated resolved marker context
  have events : CoreTicketHistory.capturedTickets (base.observations ++ [.entered site]) =
      CoreTicketHistory.capturedTickets base.observations ++ issuedTickets [] := by
    simp [CoreTicketHistory.capturedTickets, issuedTickets]
  exact ⟨before, next, rawStep, after, ⟨related, ownership.scopeOrigin⟩,
    ownership.tickets.step rawStep events, ownership.scopeOrigin.prepend_resume⟩

/-- The actual positive plug of the completed operand restores this saved
frame's scope. Core's pending resume frame remains present until return_resume;
the receipt below it is the exact current ownership input of that rule. -/
theorem SavedResumeOrigin.plug_current {base : CoreMachine.State}
    (receipt : SavedResumeOrigin graph owners base.heap handler owner plain below)
    (bounded : TicketBound base (.push (.plain plain) target))
    (context : plain.context = .resume binder)
    (value : ValueRel graph valueOwners base.heap coreValue operand)
    (calleeScope : Execution.Scope) :
    RawStep ⟨operand, calleeScope, .push (.plain plain) target⟩
      ⟨.resume binder operand, plain.scope, target⟩ [] [] ∧
    CurrentOwnership graph owners {base with frames := below} plain.scope target := by
  have raw : RawStep ⟨operand, calleeScope, .push (.plain plain) target⟩
      ⟨.resume binder operand, plain.scope, target⟩ [] [] := by
    simpa [context, ScopedExecution.Context.plug] using
      RawStep.plug plain operand value.closed calleeScope target
  exact ⟨raw, bounded.step raw (by simp [issuedTickets]), receipt.origin⟩

theorem SavedResumeOrigin.beta_survives {base : CoreMachine.State}
    (receipt : SavedResumeOrigin graph owners base.heap handler owner plain below) :
    SavedResumeOrigin graph owners
      ({base with control := .evaluate body (.binding parameter value saved), frames := coreTail} : CoreMachine.State).heap
      handler owner plain below := receipt

/-- The Source primitive's actual binder and the static Core lookup are joined
through the produced current scope origin. Older entries remain admissible. -/
theorem CurrentScopeOrigin.resolve_actual
    (origin : CurrentScopeOrigin graph owners scope whole)
    (sourceResolved : scope.resolve binder = some sourceOwner)
    (staticResolved : resolveOwner owners site requestedHandler requestedOwner = .ok binder)
    (found : findOwner requestedHandler requestedOwner whole =
      .ok ⟨front, requestedHandler, requestedOwner, occurrence, actualTicket, captured, outside⟩) :
    scope.resolve binder = some actualTicket := by
  cases origin with
  | inactive canonical => simp [Execution.Scope.resolve] at sourceResolved
  | @clause owners handler owner originOccurrence dynamicTicket saved physical originFront originOutside canonical path =>
    have binderSame : binder = CoreTranslation.ticket graph owner := by
      by_cases same : binder = CoreTranslation.ticket graph owner
      · exact same
      · simp [Execution.Scope.resolve, same] at sourceResolved
    subst binder
    obtain ⟨rfl, rfl⟩ := (CanonicalOwnerMap.clause canonical).resolve_head staticResolved
    cases saved with
    | none =>
      have impossible := path.lookup.symm.trans found
      cases impossible
    | some saved =>
      have cutSame := Except.ok.inj (path.lookup.symm.trans found)
      have ticketSame : dynamicTicket = actualTicket := congrArg CoreMachine.OwnerCut.ticket cutSame
      simp [Execution.Scope.resolve, ticketSame]

theorem ResumeRel.static_resolution
    (frame : ResumeRel graph owners heap (.resume handler owner) plain)
    (context : plain.context = .resume binder) :
    ∃ site, resolveOwner owners site handler owner = .ok binder := by
  cases frame with
  | operand known kind translated resolved marker storedContext =>
    have same := ScopedExecution.Context.resume.inj (storedContext.symm.trans context)
    subst_vars
    exact ⟨_, resolved⟩

open CoreCallableContractExecution CoreCallableContractAdmission CoreCallableContractRegistries
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows
open SourceScheduledCleanupInterfaces.Lexical.Recursive.CleanupRows.Contextual
open SourcePlannedChecks

section
variable [DeclarationPolicy]

theorem CurrentOwnership.resume_prerequisites
    {receiving : SourceDependencyCapture.Scope}
    {hints : SourceDependencyChecks.Lexical.ReturnHints receiving} {context : Context hints}
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.resume binder operand) plain.scope target result final context root)
    (ownership : CurrentOwnership graph frameOwners {base with frames := whole} plain.scope target)
    (reached : CoreAllocationHistory.Steps graph count (CoreMachine.initial graph)
      (resumeBefore base handler owner coreValue whole))
    (found : findOwner handler owner whole = .ok ⟨front, handler, owner, occurrence, actualTicket, captured, outside⟩)
    (frame : ResumeRel graph frameOwners base.heap (.resume handler owner) plain)
    (contextSame : plain.context = .resume binder)
    (value : ValueRel graph valueOwners base.heap coreValue operand) :
    target.erase.ticketNames.Nodup ∧ plain.scope.resolve binder = some actualTicket := by
  have history := CoreTicketHistory.initial_steps_history graph reached
  have names := ownership.tickets.names history
  obtain ⟨sourceOwner, contract, known, sourceResolved, remainder⟩ := site.resume_primitives value.closed
  obtain ⟨resumeSite, staticResolved⟩ := ResumeRel.static_resolution frame contextSame
  exact ⟨names, ownership.scopeOrigin.resolve_actual sourceResolved staticResolved found⟩
theorem resume_owned_from_history {ticket : Nat}
    {receiving : SourceDependencyCapture.Scope}
    {hints : SourceDependencyChecks.Lexical.ReturnHints receiving} {context : Context hints}
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.resume binder operand) plain.scope stack result final context
      (root : RecursiveRequirements.Requirements rootDemand))
    (ownership : CurrentOwnership graph frameOwners {base with frames := whole} plain.scope stack)
    (reached : CoreAllocationHistory.Steps graph count (CoreMachine.initial graph)
      (resumeBefore base handler staticOwner coreValue whole))
    (segment : GeneralSegment graph base.heap whole stack)
    (found : CoreMachine.findOwner handler staticOwner whole = .ok ⟨coreFront, handler, staticOwner, occurrence, ticket, captured, outside⟩)
    (frame : ResumeRel graph frameOwners base.heap (.resume handler staticOwner) plain)
    (contextSame : plain.context = .resume binder)
    (value : ValueRel graph owners base.heap coreValue operand)
    (runtimeScope : Execution.Scope) :
    CoreResumeReadiness.HandlersReady graph captured ∧
    ∃ frontTarget savedOwners data operationResult capturedTarget outsideTarget,
      GeneralOwnerCut graph base.heap handler staticOwner whole stack coreFront frontTarget savedOwners
        occurrence ticket data operationResult captured capturedTarget outside outsideTarget ∧
      GeneralStepWitness graph
        ⟨resumeBefore base handler staticOwner coreValue whole,
          .eval ⟨.resume binder operand, plain.scope, stack⟩, owners, [(frameOwners, .resume handler staticOwner)]⟩
        ⟨resumeAfter base handler staticOwner occurrence ticket coreValue captured coreFront outside,
          .eval ⟨operand, plain.scope, capturedTarget.append (frontTarget.append (.spent ticket data.answer data.scope outsideTarget))⟩,
          owners, []⟩ [] [.ticket ticket] ∧
      RawStep ⟨.resume binder operand, plain.scope, stack⟩
        ⟨operand, plain.scope, capturedTarget.append (frontTarget.append (.spent ticket data.answer data.scope outsideTarget))⟩
        [] [.ticket ticket] ∧
    ∃ contract : OwnerContract,
      globals.owners ticket = some contract ∧ result = contract.answer ∧
      ScopedPorts.eraseType operationResult = contract.input.port ∧
      ScopedPorts.eraseType data.answer = contract.answer.port ∧
    ∃ nextDemand, ∃ nextRoot : RecursiveRequirements.Requirements nextDemand,
      rootDemand = ticket :: nextDemand ∧
    ∃ nextAllowed, ∃ restored : Packed,
    ∃ _successor : Site globals outward world nextAllowed actions
        (OwnerPhaseTransitions.spend phases ticket) budget ambient installations operand plain.scope
        (capturedTarget.append (frontTarget.append (.spent ticket data.answer data.scope outsideTarget)))
        contract.input final restored.context nextRoot,
      (resumeAfter base handler staticOwner occurrence ticket coreValue captured coreFront outside).observations =
        base.observations ++ [.resumed ticket] ∧
      stack.erase.owners.Perm
        ((capturedTarget.append (frontTarget.append (.spent ticket data.answer data.scope outsideTarget))).erase.owners ++ [.ticket ticket]) := by
  obtain ⟨names, resolve⟩ := CurrentOwnership.resume_prerequisites site ownership reached found frame contextSame value
  exact CoreCallableResumeCorrespondence.Site.resume_correspondence site names segment found frame contextSame value resolve runtimeScope
theorem resume_owned_from_saved_history {ticket : Nat}
    {receiving : SourceDependencyCapture.Scope}
    {hints : SourceDependencyChecks.Lexical.ReturnHints receiving} {context : Context hints}
    (site : Site globals outward world allowed actions phases budget ambient installations
      (.resume binder operand) plain.scope stack result final context
      (root : RecursiveRequirements.Requirements rootDemand))
    (bounded : TicketBound base stack)
    (receipt : SavedResumeOrigin graph frameOwners base.heap handler staticOwner plain whole)
    (reached : CoreAllocationHistory.Steps graph count (CoreMachine.initial graph)
      (resumeBefore base handler staticOwner coreValue whole))
    (segment : GeneralSegment graph base.heap whole stack)
    (found : CoreMachine.findOwner handler staticOwner whole = .ok ⟨coreFront, handler, staticOwner, occurrence, ticket, captured, outside⟩)
    (contextSame : plain.context = .resume binder)
    (value : ValueRel graph owners base.heap coreValue operand)
    (runtimeScope : Execution.Scope) :
    CoreResumeReadiness.HandlersReady graph captured ∧
    ∃ frontTarget savedOwners data operationResult capturedTarget outsideTarget,
      GeneralOwnerCut graph base.heap handler staticOwner whole stack coreFront frontTarget savedOwners
        occurrence ticket data operationResult captured capturedTarget outside outsideTarget ∧
      GeneralStepWitness graph
        ⟨resumeBefore base handler staticOwner coreValue whole,
          .eval ⟨.resume binder operand, plain.scope, stack⟩, owners, [(frameOwners, .resume handler staticOwner)]⟩
        ⟨resumeAfter base handler staticOwner occurrence ticket coreValue captured coreFront outside,
          .eval ⟨operand, plain.scope, capturedTarget.append (frontTarget.append (.spent ticket data.answer data.scope outsideTarget))⟩,
          owners, []⟩ [] [.ticket ticket] ∧
      RawStep ⟨.resume binder operand, plain.scope, stack⟩
        ⟨operand, plain.scope, capturedTarget.append (frontTarget.append (.spent ticket data.answer data.scope outsideTarget))⟩
        [] [.ticket ticket] ∧
    ∃ contract : OwnerContract,
      globals.owners ticket = some contract ∧ result = contract.answer ∧
      ScopedPorts.eraseType operationResult = contract.input.port ∧
      ScopedPorts.eraseType data.answer = contract.answer.port ∧
    ∃ nextDemand, ∃ nextRoot : RecursiveRequirements.Requirements nextDemand,
      rootDemand = ticket :: nextDemand ∧
    ∃ nextAllowed, ∃ restored : Packed,
    ∃ _successor : Site globals outward world nextAllowed actions
        (OwnerPhaseTransitions.spend phases ticket) budget ambient installations operand plain.scope
        (capturedTarget.append (frontTarget.append (.spent ticket data.answer data.scope outsideTarget)))
        contract.input final restored.context nextRoot,
      (resumeAfter base handler staticOwner occurrence ticket coreValue captured coreFront outside).observations =
        base.observations ++ [.resumed ticket] ∧
      stack.erase.owners.Perm
        ((capturedTarget.append (frontTarget.append (.spent ticket data.answer data.scope outsideTarget))).erase.owners ++ [.ticket ticket]) := by
  have ownership : CurrentOwnership graph frameOwners {base with frames := whole} plain.scope stack :=
    ⟨bounded, receipt.origin⟩
  exact resume_owned_from_history site ownership reached segment found receipt.related contextSame value runtimeScope
end

#print axioms CanonicalOwnerMap.resolve_head
#print axioms OwnerPath.lookup
#print axioms TicketBound.names
#print axioms TicketBound.step
#print axioms CurrentOwnership.initial
#print axioms capture_owned
#print axioms CurrentScopeOrigin.prepend_plain
#print axioms SavedFrameOrigin.install
#print axioms SavedFrameOrigin.bind_static
#print axioms bind_focus_owned
#print axioms bind_return_owned
#print axioms CurrentScopeOrigin.prepend_resume
#print axioms resume_focus_owned
#print axioms SavedResumeOrigin.plug_current
#print axioms SavedResumeOrigin.beta_survives
#print axioms beta_owned
#print axioms SavedFrameOrigin.beta_survives
#print axioms CurrentScopeOrigin.resolve_actual
#print axioms ResumeRel.static_resolution
#print axioms CurrentOwnership.resume_prerequisites
#print axioms resume_owned_from_history
#print axioms resume_owned_from_saved_history
end Ash.OneShot.CoreCallableReachableResume
