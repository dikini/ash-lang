import SourceBoundRecords

/-! Concrete code evidence at every retained position. The existing source
tree supplies the records, including callbacks and dormant captures. A separate
structural judgment fixes each record's actual receiving suffix. This is
positional code coverage, not derivation of future contextual AtUse judgments. -/
namespace Ash.OneShot.SourceBoundSnapshots
open SourceContextualHints (Hints)
open SourceDependencyCapture (Scope)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourcePlanBounds (Annotation ofCode)
open SourceScheduledCapabilityAnnotations (Code DeclarationPolicy)

variable [DeclarationPolicy]

/-- A concrete source annotation and its current validity, with exact bound
projection. The receiver is recorded as data and checked separately at its site. -/
structure CodeRecord (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) {plan : Plan dependencies}
    (bounds : Annotation world plan) where
  receiver : SourceScheduledSavedPlans.Saved
  source : Code world plan receiver.forest
  origin : ofCode source = bounds
  valid : source.Valid outward actions phases

def CodeRecord.of_source {hints : Hints scope} {forest : Forest hints}
    {source : Code world plan forest} (ready : source.Valid outward actions phases) :
    CodeRecord outward actions phases (ofCode source) := ⟨⟨_, _, forest⟩, source, rfl, ready⟩

/-- Every record is attached to its actual receiving continuation. Dormant
saved code receives its waiting suffix; callbacks receive the running marker.
There is no optional or missing record constructor. -/
inductive Retained.Records.AtReceivers (outward : List Instance) (actions : Syntax.UsageTickets)
    (phases : OwnerPhaseTransitions.Phases) :
    {scope outsideScope : Scope} → {hints : Hints scope} → {outsideHints : Hints outsideScope} →
    {forest : Forest hints} → {bounds : Retained world forest} →
    bounds.Records (CodeRecord outward actions phases) → Forest outsideHints → Prop where
  | nil : AtReceivers outward actions phases .nil outside
  | plain {restHints : Hints restScope} {rest : Forest restHints}
      {tail : Retained world rest} {records : tail.Records (CodeRecord outward actions phases)}
      {record : CodeRecord outward actions phases code}
      (located : record.receiver = ⟨_, _, rest.append outside⟩)
      (remaining : AtReceivers outward actions phases records outside) :
      AtReceivers outward actions phases (.plain record records) outside
  | handler {tail : Retained world rest} {records : tail.Records (CodeRecord outward actions phases)} :
      AtReceivers outward actions phases records outside →
      AtReceivers outward actions phases
        (bounds := .handler (effect := effect) (table := table) (families := families) (required := required) tail)
        (.handler records) outside
  | cell {tail : Retained world rest} {records : tail.Records (CodeRecord outward actions phases)} :
      AtReceivers outward actions phases records outside →
      AtReceivers outward actions phases (bounds := .cell (identity := identity) tail) (.cell records) outside
  | cleanup {restHints : Hints restScope} {rest : Forest restHints}
      {tail : Retained world rest} {records : tail.Records (CodeRecord outward actions phases)}
      {record : CodeRecord outward actions phases code}
      (located : record.receiver = ⟨_, _, Forest.running (rest.append outside)⟩)
      (remaining : AtReceivers outward actions phases records outside) :
      AtReceivers outward actions phases (bounds := .cleanup (needs := needs) code tail) (.cleanup record records) outside
  | running : AtReceivers outward actions phases records outside →
      AtReceivers outward actions phases (.running records) outside
  | live {restHints : Hints restScope} {rest : Forest restHints}
      {tail : Retained world rest} {waiting : tail.Records (CodeRecord outward actions phases)}
      {captured : Retained world savedForest} {saved : captured.Records (CodeRecord outward actions phases)}
      (inside : AtReceivers outward actions phases saved (rest.append outside))
      (remaining : AtReceivers outward actions phases waiting outside) :
      AtReceivers outward actions phases (bounds := .live (owner := owner) captured tail) (.live saved waiting) outside
  | spent {tail : Retained world rest} {records : tail.Records (CodeRecord outward actions phases)} :
      AtReceivers outward actions phases records outside →
      AtReceivers outward actions phases (bounds := .spent (owner := owner) tail) (.spent records) outside

end Ash.OneShot.SourceBoundSnapshots

namespace Ash.OneShot.SourceScheduledRetainedInterfaces
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceBoundSnapshots (CodeRecord)
open SourceBoundSnapshots.Retained.Records (AtReceivers)

variable [SourceScheduledCapabilityAnnotations.DeclarationPolicy]

/-- Operation interfaces supply concrete code records at every retained
position, with their existing suffix checks. No continuation use is inferred
from an operation-only annotation. -/
theorem Interfaces.code_records
    {hints : Hints scope} {forest : Forest hints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (source : Interfaces world forest) (ready : source.check outsideScope = true) :
    ∃ records : (SourceBoundSnapshots.Retained.absent (world := world) forest).Records (CodeRecord outward actions phases),
      AtReceivers outward actions phases records outside := by
  induction source generalizing outsideScope with
  | nil => exact ⟨.nil, .nil⟩
  | plain rest required footprint declared tail ih =>
      obtain ⟨supplied, remaining⟩ := Bool.and_eq_true_iff.mp ready
      obtain ⟨records, located⟩ := ih remaining
      exact ⟨.plain ⟨⟨_, _, rest.append outside⟩, .operations required footprint declared, rfl, supplied⟩ records,
        .plain rfl located⟩
  | handler rest tail ih =>
      obtain ⟨_, remaining⟩ := Bool.and_eq_true_iff.mp ready
      obtain ⟨records, located⟩ := ih remaining
      exact ⟨.handler records, .handler located⟩
  | cell tail ih =>
      obtain ⟨records, located⟩ := ih ready
      exact ⟨.cell records, .cell located⟩
  | cleanup rest required footprint declared tail ih =>
      obtain ⟨supplied, remaining⟩ := Bool.and_eq_true_iff.mp ready
      obtain ⟨records, located⟩ := ih remaining
      exact ⟨.cleanup ⟨⟨_, _, .running (rest.append outside)⟩, .operations required footprint declared, rfl, supplied⟩ records,
        .cleanup rfl located⟩
  | running tail ih =>
      obtain ⟨records, located⟩ := ih ready
      exact ⟨.running records, .running located⟩
  | live rest saved tail ihSaved ihTail =>
      obtain ⟨insideReady, remaining⟩ := Bool.and_eq_true_iff.mp ready
      obtain ⟨inside, insideLocated⟩ := ihSaved (outside := rest.append outside) insideReady
      obtain ⟨records, located⟩ := ihTail remaining
      exact ⟨.live inside records, .live insideLocated located⟩
  | spent tail ih =>
      obtain ⟨records, located⟩ := ih ready
      exact ⟨.spent records, .spent located⟩

end Ash.OneShot.SourceScheduledRetainedInterfaces

namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceBoundSnapshots (CodeRecord)
open SourceBoundSnapshots.Retained (ofCapability)
open SourceBoundSnapshots.Retained.Records (AtReceivers)

variable [DeclarationPolicy]

/-- Valid recursive source yields records for every ordinary body, callback
and dormant capture, at its exact receiving suffix and original bound index.
Existing code source is retained directly; only operation interfaces are
materialized as operation code. -/
theorem Retained.code_records
    {hints : Hints scope} {forest : Forest hints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (source : Retained world forest outside) (ready : source.Valid outward actions phases) :
    ∃ records : (ofCapability source).Records (CodeRecord outward actions phases),
      AtReceivers outward actions phases records outside := by
  induction forest generalizing outsideScope with
  | nil => cases source with
    | operations interfaces => exact interfaces.code_records ready
  | plain plan rest ih => cases source with
    | operations interfaces => exact interfaces.code_records ready
    | plain code tail =>
      obtain ⟨records, located⟩ := ih tail ready.2
      exact ⟨.plain (CodeRecord.of_source ready.1) records, .plain rfl located⟩
  | handler rest ih => cases source with
    | operations interfaces => exact interfaces.code_records ready
    | handler tail =>
      obtain ⟨records, located⟩ := ih tail ready.2
      exact ⟨.handler records, .handler located⟩
  | cell rest ih => cases source with
    | operations interfaces => exact interfaces.code_records ready
    | cell tail =>
      obtain ⟨records, located⟩ := ih tail ready
      exact ⟨.cell records, .cell located⟩
  | cleanup plan rest ih => cases source with
    | operations interfaces => exact interfaces.code_records ready
    | cleanup code tail =>
      obtain ⟨records, located⟩ := ih tail ready.2
      exact ⟨.cleanup (CodeRecord.of_source ready.1) records, .cleanup rfl located⟩
  | running rest ih => cases source with
    | operations interfaces => exact interfaces.code_records ready
    | running tail =>
      obtain ⟨records, located⟩ := ih tail ready
      exact ⟨.running records, .running located⟩
  | live saved rest ihSaved ihTail => cases source with
    | operations interfaces => exact interfaces.code_records ready
    | live inside tail =>
      obtain ⟨savedRecords, savedLocated⟩ := ihSaved inside ready.1
      obtain ⟨records, located⟩ := ihTail tail ready.2
      exact ⟨.live savedRecords records, .live savedLocated located⟩
  | spent rest ih => cases source with
    | operations interfaces => exact interfaces.code_records ready
    | spent tail =>
      obtain ⟨records, located⟩ := ih tail ready
      exact ⟨.spent records, .spent located⟩

/-- Attach complete positional coverage to the actual bound value identified
by an existing source/snapshot equality. -/
theorem Retained.code_records_at
    {hints : Hints scope} {forest : Forest hints}
    {outsideHints : Hints outsideScope} {outside : Forest outsideHints}
    (source : Retained world forest outside) (ready : source.Valid outward actions phases)
    {bounds : SourceBoundSnapshots.Retained world forest} (origin : ofCapability source = bounds) :
    ∃ records : bounds.Records (CodeRecord outward actions phases),
      AtReceivers outward actions phases records outside := by
  cases origin
  exact source.code_records ready

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceBoundSnapshots.CodeRecord.of_source
#print axioms Ash.OneShot.SourceScheduledRetainedInterfaces.Interfaces.code_records
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.code_records

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.code_records_at
