import CoreResumeReadiness
import CoreNormalCleanupSteps

/-! Bounded C3.4 interface for current detected preparation. This computes
checks from the current Core operation, never from a supplied successor.
Ordinary host allocations must return. MEnv omits Rust instantiation maps;
cell acquisition and complete request-metadata preparation remain unrepresented.
Ghost identity counters are not Rust capacities. -/
namespace Ash.OneShot.CoreRuntimePreparation
open CoreMachine CoreSyntax

inductive Phase where
  | acquisition | capture | cleanup | teardown
  deriving DecidableEq, Repr

inductive Resource where
  | work | cleanupOwners | activationKeys | environmentBindings
  | frames | effectTrace | captureInspection
  | environmentDisposal | capturedDisposal | typeDisposal | kindDisposal
  deriving DecidableEq, Repr

inductive Cause where
  | configuredCapacity | allocatorRefused | storageReservationFailed | workExhausted
  deriving DecidableEq, Repr

structure Failure where
  cause : Cause
  phase : Phase
  resource : Resource
  requested : Nat
  available : Option Nat
  deriving DecidableEq, Repr

inductive Check where
  | charge : Phase → Nat → Check
  | admit : Phase → Resource → Nat → Check
  | reserve : Phase → Resource → Nat → Check
  | reserveControl : Phase → Resource → Nat → Nat → Check
  deriving DecidableEq, Repr

/-- Runtime-visible bindings in this singleton-wrapper fragment. Resource
metadata itself adds no ordinary binding; the handle binding does. -/
def environmentLen : CoreMachine.Environment → Nat
  | .empty => 0
  | .binding _ _ rest | .functionTemplate _ _ _ rest => environmentLen rest + 1
  | .resource _ _ rest => environmentLen rest

/-- Separate runtime ledgers supplied by the Rust boundary. `available` is
remaining quota for admit checks (cleanupOwners), and absolute representable
element maxima for reserveControl checks (frames/effectTrace/captureInspection).
reserveControl subtracts its computed current used count from those maxima. Their agreement with current concrete storage remains an
executable evidence obligation, not a property of mathematical Nat freshness. -/
structure Limits where
  workRemaining : Nat
  available : Resource → Nat
  traceEnabled : Bool := false
  effectTraceLen : Nat := 0
  wordMaximum : Nat := 2^64 - 1
  capturedCells : Nat := 0
  liveCleanups : Nat := 0
  storageOrdinal : Nat := 0

/-- Ordered opaque replies are allowed only at a concrete storage reservation.
The ordinal advances on every returned reservation, so identical later
requests may receive different replies. They
cannot create configured/work or invariant failure at arbitrary control. -/
inductive StorageReply where
  | returned | storageReservationFailed
  deriving DecidableEq, Repr

abbrev Host := Nat → Phase → Resource → Nat → StorageReply

def checkOne (host : Host) (limits : Limits) : Check → Except Failure Limits
  | .charge phase requested =>
      if requested ≤ limits.workRemaining then
        .ok { limits with workRemaining := limits.workRemaining - requested }
      else .error ⟨.workExhausted, phase, .work, requested, some limits.workRemaining⟩
  | .admit phase resource requested =>
      if requested ≤ limits.available resource then .ok limits
      else .error ⟨.configuredCapacity, phase, resource, requested, some (limits.available resource)⟩
  | .reserve phase resource requested =>
      match host limits.storageOrdinal phase resource requested with
      | .returned => .ok { limits with storageOrdinal := limits.storageOrdinal + 1 }
      | .storageReservationFailed => .error ⟨.storageReservationFailed, phase, resource, requested, none⟩
  | .reserveControl phase resource used requested =>
      let available := limits.available resource - used
      if requested ≤ available then
        match host limits.storageOrdinal phase resource requested with
        | .returned => .ok { limits with storageOrdinal := limits.storageOrdinal + 1 }
        | .storageReservationFailed => .error ⟨.storageReservationFailed, phase, resource, requested, none⟩
      else .error ⟨.configuredCapacity, phase, resource, requested, some available⟩

def checkAll (host : Host) : Limits → List Check → Except Failure Limits
  | limits, [] => .ok limits
  | limits, check :: rest => do
      let next ← checkOne host limits check
      checkAll host next rest

def traceReserve (limits : Limits) (requested : Nat) : List Check :=
  if limits.traceEnabled then [.reserveControl .capture .effectTrace limits.effectTraceLen requested] else []

/-- Rust iterates each capture vector outer-first, pushes nested captures,
then pops the pending vector. Core lists have the reverse orientation. -/
def addInspectionChildren : List CoreMachine.Frame → List (List CoreMachine.Frame) →
    List Check × List (List CoreMachine.Frame)
  | [], pending => ([], pending)
  | frame :: rest, pending =>
      match frame with
      | .clauseBoundary _ _ _ _ (some nested) =>
          let (checks, final) := addInspectionChildren rest (nested :: pending)
          (.reserveControl .capture .captureInspection pending.length 1 :: checks, final)
      | _ => addInspectionChildren rest pending

def inspectionChecks : Nat → List (List CoreMachine.Frame) → Except CoreMachine.Error (List Check)
  | 0, _ => .error .fuelExhausted
  | _ + 1, [] => .ok []
  | fuel + 1, capture :: pending => do
      let (children, pending) := addInspectionChildren capture.reverse pending
      let rest ← inspectionChecks fuel pending
      pure (.charge .capture (capture.length + 1) :: children ++ rest)

inductive Operation where
  | cleanupAcquire : NodeRef → CoreMachine.Environment → Operation
  | cleanupStart : NodeRef → CoreMachine.Environment → Nat → Operation
  | cleanupFinish : Nat → Operation
  | resume : OwnerCut → Operation
  | discard : OwnerCut → List CoreMachine.Frame → List Observation → List Check → Operation
  deriving Repr

/-- Recognize literal current node/control/head, and use the actual owner
lookup for resume. Unsupported families remain a separate coverage result. -/
def operation (graph : Graph) (state : CoreMachine.State) : Except CoreMachine.Error (Option Operation) :=
  match state.control with
  | .evaluate site environment =>
      match graph.node site with
      | some ⟨_, _, _, _, .cleanup callback _ _⟩ =>
          match environment.lookup callback.id with
          | some (.closure _ _ _) => .ok (some (.cleanupAcquire site environment))
          | _ => .error .cleanupCallback
      | _ => .ok none
  | .returned value =>
      match state.frames with
      | .cleanupBoundary action environment identity :: _ =>
          .ok (some (.cleanupStart action environment identity))
      | .cleanupCompletion identity _ :: _ =>
          match value with
          | .unit => .ok (some (.cleanupFinish identity))
          | _ => .error .cleanupResult
      | .resume handler owner :: rest => do
          let cut ← findOwner handler owner rest
          .ok (some (.resume cut))
      | _ => .ok none
  | .discard handler owner => do
      let cut ← findOwner handler owner state.frames
      let (closing, consumed) ← closeFuel (framesMass cut.capture + 1) cut.capture
      let inspection ← inspectionChecks (framesMass cut.capture + 2) [cut.capture]
      pure (some (.discard cut closing consumed inspection))

/-- Exact represented additional requests. Cleanup acquisition charges before
publication; ordinary resume has no work charge when registration is absent.
Resume's trace reservation requests saved length + 1, even for nonhandlers. -/
def checks (limits : Limits) : Operation → List Check
  | .cleanupAcquire _ environment =>
      [.charge .acquisition (min limits.wordMaximum (2 + environmentLen environment)),
       .admit .acquisition .cleanupOwners 1,
       .reserve .acquisition .frames 1]
  | .cleanupStart _ _ _ =>
      [.charge .cleanup 2, .reserve .cleanup .frames 1]
  | .cleanupFinish _ => []
  | .resume cut =>
      traceReserve limits (cut.capture.length + 1) ++
        [.reserveControl .capture .frames (cut.inside.length + 1 + cut.outside.length) cut.capture.length]
  | .discard cut closing _ inspection =>
      let count := framesMass cut.capture
      let owners := closing.length
      [.charge .capture 1, .reserveControl .capture .captureInspection 0 1] ++ inspection ++
        [.charge .capture (min limits.wordMaximum (count + owners + 1)),
         .reserveControl .capture .frames 0 count,
         .reserveControl .capture .frames 0 owners,
         .reserveControl .capture .frames
           (cut.inside.length + 1 + cut.outside.length) (owners + 1)] ++ traceReserve limits 1

/-- A stopped operation retains its published prefix, not an asserted
unchanged runtime state. In particular cleanup start has already popped its
boundary. Entry is observable before acquisition checks. -/
def unpublishedObservations (state : CoreMachine.State) (op : Operation) : List Observation :=
  match op with
  | .cleanupAcquire site _ => state.observations ++ [.entered site]
  | _ => state.observations

inductive Outcome where
  | unrepresented
  | invariant : CoreMachine.Error → Outcome
  | stopped : Failure → List Observation → Outcome
  | committed : CoreMachine.State → Outcome
  | projectionReady : OwnerCut → List CoreMachine.Frame → List Observation → Outcome
  | runtimeInvariant
  deriving Repr

/-- These current-ledger guards have no resource-failure interpretation.
Their production from a related concrete Rust state remains open. -/
def runtimeGuard (limits : Limits) : Operation → Bool
  | .resume cut => cut.capture.length ≤ limits.capturedCells &&
      limits.capturedCells ≤ limits.available .frames &&
      limits.available .frames < limits.wordMaximum &&
      cut.inside.length + 1 + cut.outside.length ≤ limits.available .frames &&
      limits.effectTraceLen ≤ limits.available .effectTrace &&
      limits.available .effectTrace ≤ limits.wordMaximum
  | .discard cut _ _ _ => framesMass cut.capture ≤ limits.capturedCells &&
      limits.capturedCells ≤ limits.available .frames &&
      limits.available .frames < limits.wordMaximum &&
      cut.inside.length + 1 + cut.outside.length ≤ limits.available .frames &&
      limits.effectTraceLen ≤ limits.available .effectTrace &&
      limits.available .effectTrace ≤ limits.wordMaximum
  | .cleanupStart _ _ _ | .cleanupFinish _ => limits.liveCleanups > 0
  | .cleanupAcquire _ environment => environmentLen environment ≤ limits.wordMaximum

/-- Fail-closed structural gate precedes modeled resource checks. On admitted
shapes this never turns a Core rejection into a capacity alternative. This
is not a claim about the order of invariant errors on malformed Rust input. -/
def prepareChecked (graph : Graph) (host : Host) (limits : Limits) (state : CoreMachine.State) : Outcome :=
  match operation graph state with
  | .error error => .invariant error
  | .ok none => .unrepresented
  | .ok (some op) =>
      match CoreMachine.next graph state with
      | .rejected error => .invariant error
      | .done _ => .unrepresented
      | .stepped after =>
          match checkAll host limits (checks limits op) with
          | .error failure => .stopped failure (unpublishedObservations state op)
          | .ok _ =>
              match op with
              | .discard cut closing _ _ => .projectionReady cut closing state.observations
              | _ => .committed after

def prepare (graph : Graph) (host : Host) (limits : Limits) (state : CoreMachine.State) : Outcome :=
  match operation graph state with
  | .ok (some op) =>
      if runtimeGuard limits op then prepareChecked graph host limits state else .runtimeInvariant
  | _ => prepareChecked graph host limits state

theorem successful_erasure (success : prepare graph host limits before = .committed after) :
    CoreMachine.next graph before = .stepped after := by
  unfold prepare at success
  cases recognized : operation graph before with
  | error error => simp [recognized, prepareChecked] at success
  | ok option =>
      cases option with
      | none => simp [recognized, prepareChecked] at success
      | some op =>
          simp only [recognized] at success
          split at success <;> try contradiction
          unfold prepareChecked at success
          simp only [recognized] at success
          cases actual : CoreMachine.next graph before with
          | rejected error => simp [actual] at success
          | done value => simp [actual] at success
          | stepped computed =>
              simp only [actual] at success
              cases checked : checkAll host limits (checks limits op) with
              | error failure => simp [checked] at success
              | ok remaining =>
                  simp only [checked] at success
                  cases op <;> simp only at success <;> try contradiction
                  all_goals cases success; rfl

private theorem checked_rejected_has_no_capacity_alternative
    (rejected : CoreMachine.next graph state = .rejected error) :
    ∀ failure observations, prepareChecked graph host limits state ≠ .stopped failure observations := by
  intro failure observations
  unfold prepareChecked
  cases recognized : operation graph state with
  | error error => simp
  | ok option =>
      cases option <;> simp [rejected]

theorem rejected_has_no_capacity_alternative
    (rejected : CoreMachine.next graph state = .rejected error) :
    ∀ failure observations, prepare graph host limits state ≠ .stopped failure observations := by
  intro failure observations
  unfold prepare
  cases recognized : operation graph state with
  | error error => exact checked_rejected_has_no_capacity_alternative rejected _ _
  | ok option =>
      cases option with
      | none => exact checked_rejected_has_no_capacity_alternative rejected _ _
      | some op =>
          dsimp only
          split
          · exact checked_rejected_has_no_capacity_alternative rejected _ _
          · simp

theorem stopped_observations
    {failure : Failure} {observations : List Observation}
    (recognized : operation graph state = .ok (some op))
    (stopped : prepare graph host limits state = .stopped failure observations) :
    observations = unpublishedObservations state op := by
  unfold prepare at stopped
  simp only [recognized] at stopped
  split at stopped <;> try contradiction
  unfold prepareChecked at stopped
  simp only [recognized] at stopped
  cases actual : CoreMachine.next graph state with
  | rejected error => simp [actual] at stopped
  | done value => simp [actual] at stopped
  | stepped after =>
      simp only [actual] at stopped
      cases checked : checkAll host limits (checks limits op) with
      | ok remaining =>
          simp only [checked] at stopped
          cases op <;> simp at stopped
      | error refused =>
          simp only [checked] at stopped
          exact (Outcome.stopped.inj stopped).2.symm

theorem projection_ready_origin
    (ready : prepare graph host limits state = .projectionReady cut closing observations) :
    ∃ consumed inspection,
      operation graph state = .ok (some (.discard cut closing consumed inspection)) ∧
      observations = state.observations := by
  unfold prepare at ready
  cases recognized : operation graph state with
  | error error => simp [recognized, prepareChecked] at ready
  | ok option =>
      cases option with
      | none => simp [recognized, prepareChecked] at ready
      | some op =>
          simp only [recognized] at ready
          split at ready <;> try contradiction
          unfold prepareChecked at ready
          simp only [recognized] at ready
          cases actual : CoreMachine.next graph state with
          | rejected error => simp [actual] at ready
          | done value => simp [actual] at ready
          | stepped after =>
              simp only [actual] at ready
              cases checked : checkAll host limits (checks limits op) with
              | error failure => simp [checked] at ready
              | ok remaining =>
                  simp only [checked] at ready
                  cases op <;> simp only at ready <;> try contradiction
                  cases ready
                  exact ⟨_, _, rfl, rfl⟩

/-- Ordinary restored handler readiness comes from the same related saved
segment; it is never a generic resource-failure permission. -/
theorem resume_handlers_ready
    {cut : CoreMachine.OwnerCut}
    (segment : CoreGeneralStack.GeneralSegment graph heap cut.capture target) :
    CoreResumeReadiness.HandlersReady graph cut.capture :=
  CoreResumeReadiness.GeneralSegment.handlers_ready segment

/-- Specific computed normal start endpoint, with arbitrary saved value. -/
theorem cleanup_start_next (base : CoreMachine.State) (action : NodeRef) (environment : CoreMachine.Environment)
    (identity : Nat) (saved : CoreMachine.Value) (rest : List CoreMachine.Frame) :
    CoreMachine.next graph { base with
      control := (.returned saved),
      frames := (.cleanupBoundary action environment identity :: rest) } =
      .stepped { base with
        control := (.evaluate action environment),
        frames := (.cleanupCompletion identity saved :: rest),
        observations := base.observations ++ [.cleanupStarted identity] } := rfl

theorem cleanup_finish_next (base : CoreMachine.State) (identity : Nat) (saved : CoreMachine.Value)
    (rest : List CoreMachine.Frame) :
    CoreMachine.next graph { base with
      control := (.returned .unit),
      frames := (.cleanupCompletion identity saved :: rest) } =
      .stepped { base with
        control := (.returned saved), frames := rest,
        observations := base.observations ++ [.cleanupFinished identity] } := rfl

theorem cleanup_acquire_next (base : CoreMachine.State)
    (known : graph.node site = some node)
    (kind : node.kind = .cleanup callback action body)
    (lookup : environment.lookup callback.id = some (.closure parameter functionBody captured)) :
    CoreMachine.next graph { base with
      control := .evaluate site environment } =
      .stepped { base with
        control := .evaluate body environment,
        frames := .cleanupBoundary action environment base.nextCleanup :: base.frames,
        nextCleanup := base.nextCleanup + 1,
        observations := (base.observations ++ [.entered site]) ++ [.cleanupArmed base.nextCleanup] } := by
  simp only [CoreMachine.next, known]
  cases node
  dsimp only at kind
  subst_vars
  simp only [lookup]

/-- Exact ordinary resume endpoint derives from the actual owner lookup. The
separate saved-handler readiness theorem excludes its post-take invariant
lookup failures on the current related domain. -/
theorem resume_next (base : CoreMachine.State)
    (found : findOwner handler owner rest = .ok cut) :
    CoreMachine.next graph { base with
      control := .returned value,
      frames := .resume handler owner :: rest } =
      .stepped { base with
        control := .returned value,
        frames := cut.capture ++ cut.inside ++
          .clauseBoundary cut.handler cut.owner cut.occurrence cut.ticket none :: cut.outside,
        observations := base.observations ++ [.resumed cut.ticket] } := by
  simp only [CoreMachine.next, returnResume, found]

/-- Checked finite activation increment in scoped cell acquisition. This
isolated operation is represented even though the omitted instantiation-map
checks prevent claiming a complete cell-acquisition footprint. -/
def activationIncrement (maximum current : Nat) : Except Failure Nat :=
  if current < maximum then .ok (current + 1)
  else .error ⟨.configuredCapacity, .acquisition, .activationKeys, 1, some 0⟩

theorem activation_exhausted (maximum : Nat) :
    activationIncrement maximum maximum =
      .error ⟨.configuredCapacity, .acquisition, .activationKeys, 1, some 0⟩ := by
  simp [activationIncrement]

/-- Current physical phase, not a Core state or source transition. Ownership
has been consumed; source discard is still unpublished. Rust can fail at its
disposal check after the current frame is popped and before it is classified.
The pending/closing fields expose partial traversal without rollback. -/
structure ProjectionCursor where
  before : CoreMachine.State
  cut : OwnerCut
  pending : List CoreMachine.Frame
  popped : Option CoreMachine.Frame := none
  closing : List CoreMachine.Frame := []

def beginProjection (graph : Graph) (host : Host) (limits : Limits)
    (state : CoreMachine.State) : Option ProjectionCursor :=
  match prepare graph host limits state with
  | .projectionReady cut _ _ => some ⟨state, cut, cut.capture, none, []⟩
  | _ => none

def ProjectionCursor.ownerFrames (cursor : ProjectionCursor) : List CoreMachine.Frame :=
  cursor.cut.inside ++
    [.clauseBoundary cursor.cut.handler cursor.cut.owner cursor.cut.occurrence cursor.cut.ticket none] ++
    cursor.cut.outside

def ProjectionCursor.published (cursor : ProjectionCursor) : List Observation :=
  cursor.before.observations

def popProjection (cursor : ProjectionCursor) : Option ProjectionCursor :=
  match cursor.popped, cursor.pending with
  | none, frame :: rest => some { cursor with pending := rest, popped := some frame }
  | _, _ => none

def advanceProjection (cursor : ProjectionCursor) : Except CoreMachine.Error (Option ProjectionCursor) :=
  match cursor.popped with
  | none => .ok none
  | some (.cleanupCompletion _ _) | some (.closeCompletion _) => .error .runningCloseBlocked
  | some (.clauseBoundary _ _ _ _ (some nested)) =>
      .ok (some { cursor with pending := nested ++ cursor.pending, popped := none })
  | some frame =>
      let retained := match frame with
        | .resourceBoundary _ _ _ | .cleanupBoundary _ _ _ => cursor.closing ++ [frame]
        | _ => cursor.closing
      .ok (some { cursor with popped := none, closing := retained })

theorem pop_projection_preserves_observations
    (popped : popProjection before = some after) : after.published = before.published := by
  unfold popProjection at popped
  split at popped <;> try contradiction
  cases popped
  rfl

theorem advance_projection_preserves_observations
    (advanced : advanceProjection before = .ok (some after)) :
    after.published = before.published := by
  unfold advanceProjection at advanced
  split at advanced <;> try contradiction
  all_goals cases advanced <;> rfl

structure ProjectionStop where
  cursor : ProjectionCursor
  failure : Failure
  detectedTeardown : failure.phase = .teardown

/-- Produced only at the current cursor and a detected teardown failure.
There is no desired successor or observation-prefix parameter. Connection to
actual Rust disposal reporting is a focused executable evidence obligation. -/
def stopProjection (cursor : ProjectionCursor) (failure : Failure)
    (detected : failure.phase = .teardown) : ProjectionStop := ⟨cursor, failure, detected⟩

theorem consumed_projection_observations (cursor : ProjectionCursor) (failure : Failure)
    (detected : failure.phase = .teardown) :
    (stopProjection cursor failure detected).cursor.published = cursor.before.observations := rfl

/-- This stop interface carries no completed Core successor. It does not
promise source cleanup completion, replay, host destruction or rollback.
Deriving full projected assembly from generated cursor history remains open. -/
def ProjectionStop.ownerFrames (stop : ProjectionStop) : List CoreMachine.Frame :=
  stop.cursor.ownerFrames

#print axioms successful_erasure
#print axioms rejected_has_no_capacity_alternative
#print axioms stopped_observations
#print axioms projection_ready_origin
#print axioms resume_handlers_ready
#print axioms cleanup_start_next
#print axioms cleanup_finish_next
#print axioms cleanup_acquire_next
#print axioms resume_next
#print axioms consumed_projection_observations
#print axioms activation_exhausted
#print axioms pop_projection_preserves_observations
#print axioms advance_projection_preserves_observations
end Ash.OneShot.CoreRuntimePreparation
