import CoreRuntimePreparation

/-! Activation-only preparation inputs retain their original finite entries.
This sidecar does not derive Rust maps from MEnv. Actual ledger/map origin
production is an executable boundary obligation. Host allocations must return;
no ordinary Arc/value clone is reclassified as a detected reservation. -/
namespace Ash.OneShot.CoreRuntimeMetadataPreparation
open CoreRuntimePreparation CoreMachine CoreSyntax

inductive RawType where
  | activation : Nat → RawType
  | unsupported
  deriving DecidableEq, Repr
structure RawMap where
  present : Bool
  types : List (Nat × RawType)
  rows : List Nat
  deriving DecidableEq, Repr
structure MapAnnotation where
  present : Bool
  entries : List (Nat × Nat)
  deriving DecidableEq, Repr

def acceptEntries : List (Nat × RawType) → Option (List (Nat × Nat))
  | [] => some []
  | (_, .unsupported) :: _ => none
  | (name, .activation key) :: rest => do
      let entries ← acceptEntries rest
      if entries.any (fun entry => entry.1 == name) then none
      else if key > 2^32 - 1 then none else some ((name,key) :: entries)

def RawMap.accept (raw : RawMap) : Option MapAnnotation := do
  if !raw.rows.isEmpty || (!raw.present && !raw.types.isEmpty) then none
  else pure ⟨raw.present, ← acceptEntries raw.types⟩

def lookup : List (Nat × Nat) → Nat → Option Nat
  | [], _ => none
  | (name,key) :: rest, requested => if name == requested then some key else lookup rest requested

def MapAnnotation.erases (map : MapAnnotation) (environment : CoreMachine.Environment) : Prop :=
  ∀ name, lookup map.entries name = environment.resourceKey name

def put (name key : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(name,key)]
  | (other,old) :: rest => if name == other then (name,key) :: rest else (other,old) :: put name key rest

def install (name key : Nat) (map : MapAnnotation) : MapAnnotation := ⟨true,put name key map.entries⟩

theorem lookup_put (entries : List (Nat × Nat)) :
    lookup (put name key entries) requested = if requested = name then some key else lookup entries requested := by
  induction entries with
  | nil =>
      by_cases h : requested = name
      · subst requested; simp [put,lookup]
      · simp [put,lookup,h,Ne.symm h]
  | cons entry rest ih =>
      rcases entry with ⟨other,old⟩
      by_cases h : name = other
      · subst other
        by_cases r : requested = name
        · subst requested; simp [put,lookup]
        · simp [put,lookup,r,Ne.symm r]
      · by_cases r : requested = name
        · subst requested; simp [put,lookup,h,Ne.symm h,ih]
        · simp [put,lookup,h,r,ih]

theorem installed_erasure (original : map.erases environment) :
    (install name key map).erases (.resource name key environment) := by
  intro requested
  simp only [install,lookup_put,CoreMachine.Environment.resourceKey,beq_iff_eq]
  by_cases same : requested = name
  · simp [same]
  · simp only [if_neg same]
    exact original requested

/-- Generic witness passthrough only. This unindexed Origin field does not
establish SAME C2 rich/storage lineage. Accepted raw-map/environment agreement
is indexed separately; an indexed C2 consumer remains an integration gap. -/
structure Attached (Origin : Type) (environment : CoreMachine.Environment) where
  origin : Origin
  raw : RawMap
  map : MapAnnotation
  accepted : raw.accept = some map
  agreement : map.erases environment


/-- Each check carries the actual optional Rust failure request field.
Old clone failure reports None; this is not the checked charge amount. -/
structure Request where
  check : Check
  failureRequested : Option Nat
  deriving DecidableEq, Repr

def charge (phase : Phase) (amount : Nat) : Request := ⟨.charge phase amount, some amount⟩
def reserve (phase : Phase) (resource : Resource) (amount : Nat) : Request :=
  ⟨.reserve phase resource amount, some amount⟩

def acquisitionMetadata (map : MapAnnotation) : List Request :=
  [charge .acquisition (map.entries.length + 1),
   reserve .acquisition .instantiationEntries (map.entries.length + 1),
   reserve .acquisition .instantiationEntries 0] ++
  map.entries.map (fun _ => ⟨.charge .acquisition 1, none⟩) ++
  [charge .acquisition 1, ⟨.charge .acquisition 1, none⟩]

def work : List Request → Nat
  | [] => 0
  | request :: rest => (match request.check with | .charge _ amount => amount | _ => 0) + work rest

theorem work_append (left right : List Request) : work (left ++ right) = work left + work right := by
  induction left with
  | nil => simp [work]
  | cons request rest ih => simp only [List.cons_append,work,ih]; omega

theorem clone_work (entries : List (Nat × Nat)) :
    work (entries.map (fun _ => (⟨.charge .acquisition 1, none⟩ : Request))) = entries.length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih => simp [work,ih]; omega

theorem acquisition_work (map : MapAnnotation) : work (acquisitionMetadata map) = 2 * map.entries.length + 3 := by
  simp only [acquisitionMetadata,work_append,clone_work,work,charge,reserve]
  omega

structure DetectedFailure where
  cause : Cause
  phase : Phase
  resource : Resource
  requested : Option Nat
  available : Option Nat
  deriving DecidableEq, Repr

def runRequests (host : Host) : Limits → List Request → Except DetectedFailure Limits
  | limits, [] => .ok limits
  | limits, request :: rest =>
      match checkOne host limits request.check with
      | .ok next => runRequests host next rest
      | .error failure => .error ⟨failure.cause,failure.phase,failure.resource,request.failureRequested,failure.available⟩

inductive MetadataError where
  | unsupportedMap | malformedMap | unbound : Nat → MetadataError
  | unsupportedEffect | sameIdHandler : NodeRef → MetadataError
  | invalidResource : NodeRef → MetadataError
  | invariant : CoreMachine.Error → MetadataError
  | unsupportedControl | ledgerGuard
  deriving Repr

/-- Literal cell effect is retained before instantiation. General types/rows
and same-ID source handler metadata remain explicitly unsupported. -/
def requestEffect (map : MapAnnotation) (literal : Instantiation.Effect) : Except MetadataError (Instantiation.Effect × List Request) :=
  match literal with
  | .cell (.bound name) =>
      match lookup map.entries name with
      | none => .error (.unbound name)
      | some key => .ok (.cell (.activation key),
          [charge .access 2,reserve .access .instantiationStorage 1,
           ⟨.charge .access 1, if map.present then some 1 else none⟩,
           reserve .access .instantiationStorage 1])
  | _ => .error .unsupportedEffect

theorem requested_erasure (original : map.erases environment)
    (accepted : requestEffect map literal = .ok (effect,requests)) :
    literal.instantiate environment.instantiation = effect := by
  cases literal with
  | user _ _ => simp [requestEffect] at accepted
  | cell name => cases name with
    | activation _ => simp [requestEffect] at accepted
    | bound name =>
      cases found : lookup map.entries name with
      | none => simp [requestEffect,found] at accepted
      | some key =>
          simp only [requestEffect,found,Except.ok.injEq,Prod.mk.injEq] at accepted
          rw [← accepted.1]
          have known := (original name).symm.trans found
          simp [Instantiation.Effect.instantiate,Instantiation.ResourceName.instantiate,
            CoreMachine.Environment.instantiation,known]

theorem request_work (accepted : requestEffect map literal = .ok (effect,requests)) : work requests = 3 := by
  cases literal with
  | user _ _ => simp [requestEffect] at accepted
  | cell name => cases name with
    | activation _ => simp [requestEffect] at accepted
    | bound name =>
      cases found : lookup map.entries name with
      | none => simp [requestEffect,found] at accepted
      | some key =>
          simp only [requestEffect,found,Except.ok.injEq,Prod.mk.injEq] at accepted
          rw [← accepted.2]
          rfl

/-- Core frame lists are already top first (Rust iterates Vec in reverse).
Every visited frame is charged. Validate resource node shape just as Rust
looks up its API; same-ID handler annotations are not silently skipped. -/
def scan (graph : Graph) (key : Nat) : List CoreMachine.Frame → Except MetadataError (CellCut × List Request)
  | [] => .error (.invariant (.unhandledEffect (.cell (.activation key)) 0))
  | frame :: rest => do
      match frame with
      | .resourceBoundary site found payload =>
          let some node := graph.node site | throw (.invalidResource site)
          match node.kind with
          | .resource _ _ _ _ =>
              if key == found then pure (⟨[],site,found,payload,rest⟩,[charge .access 1])
              else
                let (cut,requests) ← scan graph key rest
                pure ({cut with inside := frame :: cut.inside},charge .access 1 :: requests)
          | _ => throw (.invalidResource site)
      | .handlerBoundary site _ _ =>
          let some node := graph.node site | throw (.invariant (.invalidHandler site))
          match node.kind with
          | .handler _ (.cell _) _ _ => throw (.sameIdHandler site)
          | .handler _ (.user _ _) _ _ =>
              let (cut,requests) ← scan graph key rest
              pure ({cut with inside := frame :: cut.inside},charge .access 1 :: requests)
          | _ => throw (.invariant (.invalidHandler site))
      | _ =>
          let (cut,requests) ← scan graph key rest
          pure ({cut with inside := frame :: cut.inside},charge .access 1 :: requests)

/-- The successful selected endpoint is computed by the independent current
Core search. The restricted footprint walk above rejects missing literal API
metadata and same-ID handlers before this search; no future-success seed. -/
def selectedScan (graph : Graph) (key : Nat) (frames : List CoreMachine.Frame) : Except MetadataError (CellCut × List Request) := do
  let (_,requests) ← scan graph key frames
  match findInterpreter graph (.cell (.activation key)) frames with
  | .ok (.cell cut) => pure (cut,requests)
  | .ok (.handler _ site _ _ _) => throw (.sameIdHandler site)
  | .error error => throw (.invariant error)

theorem scan_selected (accepted : selectedScan graph key frames = .ok (cut,requests)) :
    findInterpreter graph (.cell (.activation key)) frames = .ok (.cell cut) := by
  unfold selectedScan at accepted
  cases walked : scan graph key frames <;> simp only [walked] at accepted
  case error => contradiction
  case ok value =>
    cases actual : findInterpreter graph (.cell (.activation key)) frames with
    | error error => simp [actual,Except.bind,Bind.bind] at accepted
    | ok selection =>
        cases selection with
        | handler _ _ _ _ _ => simp [actual,Except.bind,Bind.bind] at accepted
        | cell selected =>
            simp only [actual,Except.pure,Except.bind,Bind.bind,Pure.pure,Except.ok.injEq,Prod.mk.injEq] at accepted
            rw [← accepted.1]

structure Ledger where
  limits : Limits
  liveResources : Nat
  resourceLimit : Nat
  environmentLength : Nat
  disposalReturned : Bool

structure Produced where
  requests : List Request
  map : MapAnnotation
  effect : Option Instantiation.Effect
  cut : Option CellCut
  deriving Repr

def traceRequests (limits : Limits) (phase : Phase) (amount : Nat) : List Request :=
  if limits.traceEnabled then [reserve phase .effectTrace amount] else []

/-- Current literal shape and current finite ledger guards only. The actual
map attachment to MEnv and rich C2 origin is a separate input/proof interface. -/
def produce (graph : Graph) (ledger : Ledger) (raw : RawMap) (state : CoreMachine.State) : Except MetadataError Produced := do
  let some map := raw.accept | throw .unsupportedMap
  if !ledger.disposalReturned || ledger.environmentLength > ledger.limits.wordMaximum ||
      ledger.liveResources > ledger.resourceLimit || ledger.resourceLimit > ledger.limits.wordMaximum ||
      ledger.limits.workRemaining > ledger.limits.wordMaximum || state.nextActivation > 2^32 - 1 then throw .ledgerGuard
  match state.control, state.frames with
  | .returned (.integer _), .resourceInitializer site identity handle body _environment :: _ =>
      let some node := graph.node site | throw (.invalidResource site)
      match node.kind with
      | .resource declared declaredHandle _ declaredBody =>
          if identity != declared || handle.id != declaredHandle.id || body != declaredBody then throw (.invalidResource site)
          if map.entries.length + 1 > ledger.limits.wordMaximum then throw .ledgerGuard
          pure ⟨[
            ⟨.admit .acquisition .resourceOwners 1,some 1⟩,
            ⟨.admit .acquisition .activationKeys 1,some 1⟩,
            reserve .acquisition .frames 1] ++ traceRequests ledger.limits .acquisition 1 ++
            acquisitionMetadata map ++
            [⟨.admit .acquisition .environmentBindings 1,some 1⟩],
            install identity state.nextActivation map,none,none⟩
      | _ => throw (.invalidResource site)
  | .returned _, .request literal _ _ :: rest =>
      let (effect,requests) ← requestEffect map literal
      match effect with
      | .cell (.activation key) =>
          let (cut,scanRequests) ← selectedScan graph key rest
          pure ⟨requests ++ scanRequests,map,some effect,some cut⟩
      | _ => throw .unsupportedEffect
  | _, _ => throw .unsupportedControl

/-- Quotas derive from current owner count/key/physical length; source tracing
and the allocator are opaque only at actual reservations. -/
def currentLimits (ledger : Ledger) (state : CoreMachine.State) : Limits :=
  {ledger.limits with available := fun resource => match resource with
    | .resourceOwners => ledger.resourceLimit - ledger.liveResources
    | .activationKeys => (2^32 - 1) - state.nextActivation
    | .environmentBindings => ledger.limits.wordMaximum - ledger.environmentLength
    | _ => ledger.limits.available resource}

def savedEnvironment (state : CoreMachine.State) : Option CoreMachine.Environment :=
  match state.control,state.frames with
  | .returned _, .resourceInitializer _ _ _ _ environment :: _ => some environment
  | .returned _, .request _ _ environment :: _ => some environment
  | _, _ => none

/-- Typed map boundary with a generic unindexed witness passthrough.
Erasure and physical-length agreement are current obligations, not generated
from a semantic lookup function. Production from the runtime observer remains
open, especially the private map-presence bit. -/
structure CurrentAttachment (Origin : Type) (ledger : Ledger) (state : CoreMachine.State) where
  environment : CoreMachine.Environment
  saved : savedEnvironment state = some environment
  original : Attached Origin environment
  physicalLength : ledger.environmentLength = environmentLen environment

inductive Outcome where
  | rejected : MetadataError → Outcome
  | stopped : DetectedFailure → List Observation → Outcome
  | committed : CoreMachine.State → Produced → Limits → Outcome

/-- Core next is computed from this current operation. Malformed shape gates
have no claimed Rust error-precedence equivalence. Metadata stop observations
retain the published prefix, including any popped request frame in Rust. -/
def prepare (graph : Graph) (host : Host) (ledger : Ledger) (raw : RawMap) (state : CoreMachine.State) : Outcome :=
  match produce graph ledger raw state with
  | .error error => .rejected error
  | .ok produced =>
      match CoreMachine.next graph state with
      | .rejected error => .rejected (.invariant error)
      | .done _ => .rejected .unsupportedControl
      | .stepped after =>
          match runRequests host (currentLimits ledger state) produced.requests with
          | .error failure => .stopped failure state.observations
          | .ok remaining => .committed after produced remaining

def prepareAttached (graph : Graph) (host : Host) (ledger : Ledger) (state : CoreMachine.State)
    (attachment : CurrentAttachment Origin ledger state) : Outcome :=
  prepare graph host ledger attachment.original.raw state

theorem successful_erasure (success : prepare graph host ledger raw before = .committed after metadata remaining) :
    CoreMachine.next graph before = .stepped after := by
  unfold prepare at success
  cases produced : produce graph ledger raw before <;> simp only [produced] at success
  case error => contradiction
  case ok value =>
    cases actual : CoreMachine.next graph before <;> simp only [actual] at success
    case rejected => contradiction
    case done => contradiction
    case stepped computed =>
      cases checked : runRequests host (currentLimits ledger before) value.requests <;> simp [checked] at success
      rcases success with ⟨rfl,_,_⟩
      rfl

theorem successful_producer (success : prepare graph host ledger raw before = .committed after metadata remaining) :
    produce graph ledger raw before = .ok metadata := by
  unfold prepare at success
  cases produced : produce graph ledger raw before <;> simp only [produced] at success
  case error => contradiction
  case ok value =>
    cases actual : CoreMachine.next graph before <;> simp only [actual] at success
    case rejected => contradiction
    case done => contradiction
    case stepped computed =>
      cases checked : runRequests host (currentLimits ledger before) value.requests <;> simp [checked] at success
      rw [success.2.1]

theorem produced_acquisition
    (rawKnown : raw.accept = some map)
    (current : before.control = .returned (.integer payload))
    (head : before.frames = .resourceInitializer site identity handle body environment :: rest)
    (accepted : produce graph ledger raw before = .ok metadata) :
    metadata.map = install identity before.nextActivation map := by
  unfold produce at accepted
  simp only [rawKnown,current,head] at accepted
  simp only [Bind.bind,Except.bind,Pure.pure,Except.pure] at accepted
  split at accepted <;> try contradiction
  cases nodeKnown : graph.node site with
  | none => simp [nodeKnown] at accepted
  | some node =>
    simp only [nodeKnown] at accepted
    cases kind : node.kind <;> simp only [kind] at accepted <;> try contradiction
    case resource declared declaredHandle initializer declaredBody =>
      split at accepted <;> try contradiction
      split at accepted <;> try contradiction
      cases accepted
      rfl

theorem acquisition_connected
    (rawKnown : raw.accept = some map) (original : map.erases environment)
    (current : before.control = .returned (.integer payload))
    (head : before.frames = .resourceInitializer site identity handle body environment :: rest)
    (success : prepare graph host ledger raw before = .committed after metadata remaining) :
    after.control = .evaluate body (.binding handle.id (.handle before.nextActivation)
      (.resource identity before.nextActivation environment)) ∧
    metadata.map.erases (.binding handle.id (.handle before.nextActivation)
      (.resource identity before.nextActivation environment)) := by
  have produced := produced_acquisition rawKnown current head (successful_producer success)
  have actual := successful_erasure success
  simp only [CoreMachine.next,current,head] at actual
  cases actual
  constructor
  · rfl
  · rw [produced]
    exact installed_erasure original

theorem produced_request
    (rawKnown : raw.accept = some map)
    (current : before.control = .returned value)
    (head : before.frames = .request literal operationNumber environment :: rest)
    (accepted : produce graph ledger raw before = .ok metadata) :
    ∃ key requests cut scanRequests,
      requestEffect map literal = .ok (.cell (.activation key),requests) ∧
      selectedScan graph key rest = .ok (cut,scanRequests) ∧
      metadata.map = map ∧ metadata.effect = some (.cell (.activation key)) ∧ metadata.cut = some cut := by
  unfold produce at accepted
  simp only [rawKnown,current,head,Bind.bind,Except.bind,Pure.pure,Except.pure] at accepted
  split at accepted <;> try contradiction
  cases requested : requestEffect map literal with
  | error error => simp [requested] at accepted
  | ok pair =>
    rcases pair with ⟨effect,requests⟩
    simp only [requested] at accepted
    cases effect <;> try contradiction
    case cell name =>
      cases name <;> try contradiction
      case activation key =>
        cases selected : selectedScan graph key rest with
        | error error => simp [selected] at accepted
        | ok pair =>
          rcases pair with ⟨cut,scanRequests⟩
          simp only [selected,Except.ok.injEq] at accepted
          cases accepted
          exact ⟨key,requests,cut,scanRequests,rfl,selected,rfl,rfl,rfl⟩

theorem request_connected
    (rawKnown : raw.accept = some map) (original : map.erases environment)
    (current : before.control = .returned value)
    (head : before.frames = .request literal operationNumber environment :: rest)
    (success : prepare graph host ledger raw before = .committed after metadata remaining) :
    ∃ key cut,
      literal.instantiate environment.instantiation = .cell (.activation key) ∧
      metadata.map = map ∧ metadata.effect = some (.cell (.activation key)) ∧ metadata.cut = some cut ∧
      findInterpreter graph (.cell (.activation key)) rest = .ok (.cell cut) ∧
      interpretCell {before with frames := rest} cut operationNumber value = .stepped after := by
  obtain ⟨key,requests,cut,scanRequests,requested,selected,mapResult,effectResult,cutResult⟩ :=
    produced_request rawKnown current head (successful_producer success)
  have realized := requested_erasure original requested
  have found := scan_selected selected
  refine ⟨key,cut,realized,mapResult,effectResult,cutResult,found,?_⟩
  have actual := successful_erasure success
  simp only [CoreMachine.next,current,head,CoreMachine.request,realized,found] at actual
  exact actual

theorem attached_acquisition_connected
    (attachment : CurrentAttachment Origin ledger before)
    (current : before.control = .returned (.integer payload))
    (head : before.frames = .resourceInitializer site identity handle body environment :: rest)
    (success : prepareAttached graph host ledger before attachment = .committed after metadata remaining) :
    after.control = .evaluate body (.binding handle.id (.handle before.nextActivation)
      (.resource identity before.nextActivation environment)) ∧
    metadata.map.erases (.binding handle.id (.handle before.nextActivation)
      (.resource identity before.nextActivation environment)) := by
  have same := attachment.saved
  simp only [savedEnvironment,current,head,Option.some.injEq] at same
  apply acquisition_connected attachment.original.accepted _ current head success
  simpa only [same] using attachment.original.agreement

theorem attached_request_connected
    (attachment : CurrentAttachment Origin ledger before)
    (current : before.control = .returned value)
    (head : before.frames = .request literal operationNumber environment :: rest)
    (success : prepareAttached graph host ledger before attachment = .committed after metadata remaining) :
    ∃ key cut,
      literal.instantiate environment.instantiation = .cell (.activation key) ∧
      metadata.map = attachment.original.map ∧ metadata.effect = some (.cell (.activation key)) ∧ metadata.cut = some cut ∧
      findInterpreter graph (.cell (.activation key)) rest = .ok (.cell cut) ∧
      interpretCell {before with frames := rest} cut operationNumber value = .stepped after := by
  have same := attachment.saved
  simp only [savedEnvironment,current,head,Option.some.injEq] at same
  apply request_connected attachment.original.accepted _ current head success
  simpa only [same] using attachment.original.agreement

theorem stopped_observations {failure : DetectedFailure} (stop : prepare graph host ledger raw before = .stopped failure observations) :
    observations = before.observations := by
  unfold prepare at stop
  cases produced : produce graph ledger raw before <;> simp only [produced] at stop
  case error => contradiction
  case ok value =>
    cases actual : CoreMachine.next graph before <;> simp only [actual] at stop
    case rejected => contradiction
    case done => contradiction
    case stepped computed =>
      cases checked : runRequests host (currentLimits ledger before) value.requests <;> simp [checked] at stop
      exact stop.2.symm

#print axioms attached_acquisition_connected
#print axioms attached_request_connected
#print axioms produced_request
#print axioms request_connected
#print axioms produced_acquisition
#print axioms acquisition_connected
#print axioms successful_producer
#print axioms requested_erasure
#print axioms installed_erasure
#print axioms scan_selected
#print axioms acquisition_work
#print axioms request_work
#print axioms successful_erasure
#print axioms stopped_observations
end Ash.OneShot.CoreRuntimeMetadataPreparation
