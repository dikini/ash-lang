import CoreCallableReceiverRefinement

/-! Finite request-payload evidence at the actual selected handler cut.

Origins name static resource code and value contexts; they are not public
operation ports or resource activations. C2 must construct the checked finite
records and prove their realization by the current operand and captured prefix.
Rust checking success alone does not supply these Lean proofs. This leaf derives
receiver membership from those current facts, without a successor admission
premise or a supplied payload-fits-tail field. -/
namespace Ash.OneShot.CorePayloadReceiver
open ScopedExpressions ScopedExecution
open SourceScheduledCleanupInterfaces.Lexical.Recursive
open CoreCallableReceiverRefinement (ClauseInputSupport)

/-- The acquisition occurrence tracked by finite resource analysis. -/
structure ResourceOrigin where
  code : Nat
  valueContext : Nat
  deriving DecidableEq

/-- A finite value-analysis port for the actual operation request. -/
structure RequestPort where
  code : Nat
  valueContext : Nat
  deriving DecidableEq

/-- Finite analysis data. The port is selected through the table below. -/
structure RequestRecord where
  dependencyOrigins : List ResourceOrigin
  crossedOrigins : List ResourceOrigin

abbrev RequestTable := List (RequestPort × RequestRecord)

def requestAt : RequestTable → RequestPort → Option RequestRecord
  | [], _ => none
  | (key, record) :: rest, port => if port = key then some record else requestAt rest port

/-- One selected finite request record with checked origin separation.
C2 still must connect this table lookup to the actual request/Site context. -/
structure CheckedRequest (table : RequestTable) (port : RequestPort) where
  record : RequestRecord
  selected : requestAt table port = some record
  separate : (record.dependencyOrigins.all (fun origin => decide (origin ∉ record.crossedOrigins))) = true

/-- Executable finite record selection and separation check. Failure supplies
no certificate; success retains the exact selected record and its proof. -/
def checkRequest (table : RequestTable) (port : RequestPort) : Option (CheckedRequest table port) :=
  match found : requestAt table port with
  | none => none
  | some record =>
      if separate : (record.dependencyOrigins.all (fun origin => decide (origin ∉ record.crossedOrigins))) = true then
        some ⟨record, found, separate⟩
      else none

/-- Current activations are interpreted through one finite, deterministic map.
The operand and selected prefix below must use this SAME map. -/
abbrev ActivationOrigins := List (Nat × ResourceOrigin)

def originAt : ActivationOrigins → Nat → Option ResourceOrigin
  | [], _ => none
  | (activation, origin) :: rest, identity =>
      if identity = activation then some origin else originAt rest identity

/-- Actual closed payload support and its provenance in the checked request
port. Ambient resources do not need to be absent from the captured prefix. -/
structure PayloadRealizes {table : RequestTable} {port : RequestPort} (checked : CheckedRequest table port)
    (origins : ActivationOrigins) (operand : Code) (bound ambient : List Nat) : Prop where
  closed : ClosedValue operand
  supported : SourceSupport.Bounds ScopedPorts.Support.empty operand.dependencies bound
  dependencies : ∀ identity, identity ∈ bound → identity ∉ ambient →
    ∃ origin, originAt origins identity = some origin ∧ origin ∈ checked.record.dependencyOrigins

/-- Provenance of resources actually made dormant by this SAME selected
prefix. A saved dormant capture contributes no active visible resources. -/
structure CapturedRealizes {table : RequestTable} {port : RequestPort} (checked : CheckedRequest table port)
    (origins : ActivationOrigins) (captured : Stack) (ambient : List Nat) : Prop where
  crossed : ∀ identity, identity ∈ captured.erase.visible → identity ∉ ambient →
    ∃ origin, originAt origins identity = some origin ∧ origin ∈ checked.record.crossedOrigins

/-- Disjoint checked origins exclude a non-ambient payload dependency from the
actual selected prefix, using deterministic current activation lookup. -/
theorem prefix_avoidance
    (payload : PayloadRealizes checked origins operand bound ambient)
    (captured : CapturedRealizes checked origins cap ambient)
    (member : identity ∈ bound) (external : identity ∉ ambient) :
    identity ∉ cap.erase.visible := by
  intro inside
  obtain ⟨dependency, dependencyAt, dependencyMember⟩ := payload.dependencies identity member external
  obtain ⟨crossed, crossedAt, crossedMember⟩ := captured.crossed identity inside external
  have same : dependency = crossed := Option.some.inj (dependencyAt.symm.trans crossedAt)
  have absent : dependency ∉ checked.record.crossedOrigins :=
    of_decide_eq_true (List.all_eq_true.mp checked.separate dependency dependencyMember)
  exact absent (same.symm ▸ crossedMember)

/-- The connected capture boundary: present operand support and checked origin
separation derive support at the receiver outside the actual handler cut. -/
theorem receiver_support
    (payload : PayloadRealizes checked origins operand bound ambient)
    (captured : CapturedRealizes checked origins cap ambient)
    (current : bound ⊆ whole.erase.visible ++ ambient)
    (cut : HandlerCut requested whole cap tail handler) :
    ClauseInputSupport operand bound (tail.erase.visible ++ ambient) := by
  refine ⟨payload.supported, ?_⟩
  intro identity member
  by_cases external : identity ∈ ambient
  · exact List.mem_append_right _ external
  · have present := current member
    rw [handler_cut_reconstructs cut, erase_append, Ash.OneShot.visible_append] at present
    rcases List.mem_append.mp present with active | ambientMember
    · rcases List.mem_append.mp active with inside | outside
      · exact False.elim (prefix_avoidance payload captured member external inside)
      · exact List.mem_append_left _ outside
    · exact False.elim (external ambientMember)

/-- The annotated clause receiver is the physical post-cut tail, rather than
its current whole-stack receiver or the issued-resource world. -/
theorem annotated_receiver_support
    (payload : PayloadRealizes checked origins operand bound ambient)
    (captured : CapturedRealizes checked origins cap ambient)
    (current : bound ⊆ wholeScope.visibleResources ++ ambient)
    (wholeRealizes : SourceDependencyCapture.Realizes tables families wholeScope whole)
    (tailRealizes : SourceDependencyCapture.Realizes tables families tailScope tail)
    (cut : HandlerCut requested whole cap tail handler) :
    ClauseInputSupport operand bound (tailScope.visibleResources ++ ambient) := by
  rw [wholeRealizes.visible_resources] at current
  rw [tailRealizes.visible_resources]
  exact receiver_support payload captured current cut

/-- Widen an established payload bound to a declaration's conservative bound
while retaining the same actual receiver. -/
theorem formal_support_mono
    (supported : ClauseInputSupport operand bound receiver)
    (larger : bound ⊆ formalBound) (received : formalBound ⊆ receiver) :
    ClauseInputSupport operand formalBound receiver :=
  ⟨SourceSupport.bounds_iff.mpr ((SourceSupport.bounds_iff.mp supported.actual).trans larger), received⟩

/-- A clause whose formal payload bound covers its receiver accepts the actual
payload only after the checked request/cut bridge has derived membership. -/
theorem receiver_formal_support
    (payload : PayloadRealizes checked origins operand bound ambient)
    (captured : CapturedRealizes checked origins cap ambient)
    (current : bound ⊆ whole.erase.visible ++ ambient)
    (cut : HandlerCut requested whole cap tail handler) :
    ClauseInputSupport operand (tail.erase.visible ++ ambient) (tail.erase.visible ++ ambient) := by
  have received := receiver_support payload captured current cut
  exact formal_support_mono received received.received (fun _ member => member)

end Ash.OneShot.CorePayloadReceiver
#print axioms Ash.OneShot.CorePayloadReceiver.checkRequest
#print axioms Ash.OneShot.CorePayloadReceiver.prefix_avoidance
#print axioms Ash.OneShot.CorePayloadReceiver.receiver_support
#print axioms Ash.OneShot.CorePayloadReceiver.annotated_receiver_support
#print axioms Ash.OneShot.CorePayloadReceiver.formal_support_mono
#print axioms Ash.OneShot.CorePayloadReceiver.receiver_formal_support
