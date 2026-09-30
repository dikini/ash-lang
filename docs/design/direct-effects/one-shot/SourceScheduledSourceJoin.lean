import SourceScheduledAdmissionFactors
import SourceScheduledRetainedRecomposition

/-! Join actual source annotations without first assuming their validation.
Reassociation only transports dependent indices; source checks and persistent
metadata are properties of that one constructed result. -/
namespace Ash.OneShot.SourceScheduledSourceJoin
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)

/-- Type-valued version of the existing receiver predicate congruence. -/
def receiverCast
    (family : ∀ {scope} {hints : Hints scope}, Forest hints → Type)
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {first : Forest firstHints} {second : Forest secondHints}
    (sameScope : firstScope = secondScope) (sameHints : HEq firstHints secondHints)
    (sameForest : HEq first second) (source : family first) : family second := by
  cases sameScope
  cases sameHints
  cases sameForest
  exact source

theorem receiverCast_heq
    (family : ∀ {scope} {hints : Hints scope}, Forest hints → Type)
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {first : Forest firstHints} {second : Forest secondHints}
    (sameScope : firstScope = secondScope) (sameHints : HEq firstHints secondHints)
    (sameForest : HEq first second) (source : family first) :
    HEq (receiverCast family sameScope sameHints sameForest source) source := by
  cases sameScope; cases sameHints; cases sameForest; rfl

theorem receiverCast_observe
    (family : ∀ {scope} {hints : Hints scope}, Forest hints → Type)
    (observe : ∀ {scope} {hints : Hints scope} (forest : Forest hints), family forest → α)
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {first : Forest firstHints} {second : Forest secondHints}
    (sameScope : firstScope = secondScope) (sameHints : HEq firstHints secondHints)
    (sameForest : HEq first second) (source : family first) :
    observe second (receiverCast family sameScope sameHints sameForest source) = observe first source := by
  cases sameScope; cases sameHints; cases sameForest; rfl

end Ash.OneShot.SourceScheduledSourceJoin

namespace Ash.OneShot.SourceScheduledCapabilityAnnotations
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourceScheduledRetainedInterfaces (Interfaces)
open SourceScheduledSourceJoin (receiverCast receiverCast_observe receiverCast_heq)
open SourceDependencyChecks (scope_append_assoc)
open SourcePlannedRecomposition (hints_append_assoc)
open SourceScheduledRecomposition (forest_append_assoc)
open SourceBoundSnapshots.Retained (ofCapability)
open SourcePlanBounds (ofCode)

variable [DeclarationPolicy]

def Code.assocReceiver {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} (first : Forest firstHints) (second : Forest secondHints)
    (outside : Forest outsideHints) {plan : Plan dependencies}
    (source : Code world plan (first.append (second.append outside))) :
    Code world plan ((first.append second).append outside) :=
  receiverCast (fun forest => Code world plan forest)
    (scope_append_assoc _ _ _).symm (hints_append_assoc _ _ _).symm
    (forest_append_assoc first second outside).symm source

def Code.runningAssocReceiver {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} (first : Forest firstHints) (second : Forest secondHints)
    (outside : Forest outsideHints) {plan : Plan dependencies}
    (source : Code world plan (.running (first.append (second.append outside)))) :
    Code world plan (.running ((first.append second).append outside)) :=
  receiverCast (fun forest => Code world plan (.running forest))
    (scope_append_assoc _ _ _).symm (hints_append_assoc _ _ _).symm
    (forest_append_assoc first second outside).symm source

def Retained.assocReceiver {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} (first : Forest firstHints) (second : Forest secondHints)
    (outside : Forest outsideHints) {saved : Forest savedHints}
    (source : Retained world saved (first.append (second.append outside))) :
    Retained world saved ((first.append second).append outside) :=
  receiverCast (fun forest => Retained world saved forest)
    (scope_append_assoc _ _ _).symm (hints_append_assoc _ _ _).symm
    (forest_append_assoc first second outside).symm source

@[simp] theorem Code.assocReceiver_interpretations
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} (first : Forest firstHints) (second : Forest secondHints)
    (outside : Forest outsideHints) {plan : Plan dependencies} (source : Code world plan (first.append (second.append outside))) :
    (source.assocReceiver first second outside).InterpretationChecks outward = source.InterpretationChecks outward :=
  receiverCast_observe (fun forest => Code world plan forest) (fun _ source => source.InterpretationChecks outward) _ _ _ source

@[simp] theorem Code.assocReceiver_continuations
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} (first : Forest firstHints) (second : Forest secondHints)
    (outside : Forest outsideHints) {plan : Plan dependencies} (source : Code world plan (first.append (second.append outside))) :
    (source.assocReceiver first second outside).ContinuationChecks actions phases = source.ContinuationChecks actions phases :=
  receiverCast_observe (fun forest => Code world plan forest) (fun _ source => source.ContinuationChecks actions phases) _ _ _ source

@[simp] theorem Code.assocReceiver_bounds
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} (first : Forest firstHints) (second : Forest secondHints)
    (outside : Forest outsideHints) {plan : Plan dependencies} (source : Code world plan (first.append (second.append outside))) :
    ofCode (source.assocReceiver first second outside) = ofCode source :=
  receiverCast_observe (fun forest => Code world plan forest) (fun _ source => ofCode source) _ _ _ source

theorem Code.assocReceiver_heq
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} (first : Forest firstHints) (second : Forest secondHints)
    (outside : Forest outsideHints) {plan : Plan dependencies} (source : Code world plan (first.append (second.append outside))) :
    HEq (source.assocReceiver first second outside) source :=
  receiverCast_heq (fun forest => Code world plan forest) _ _ _ source

@[simp] theorem Code.runningAssocReceiver_interpretations
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} (first : Forest firstHints) (second : Forest secondHints)
    (outside : Forest outsideHints) {plan : Plan dependencies} (source : Code world plan (.running (first.append (second.append outside)))) :
    (source.runningAssocReceiver first second outside).InterpretationChecks outward = source.InterpretationChecks outward :=
  receiverCast_observe (fun forest => Code world plan (.running forest)) (fun _ source => source.InterpretationChecks outward) _ _ _ source

@[simp] theorem Code.runningAssocReceiver_continuations
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} (first : Forest firstHints) (second : Forest secondHints)
    (outside : Forest outsideHints) {plan : Plan dependencies} (source : Code world plan (.running (first.append (second.append outside)))) :
    (source.runningAssocReceiver first second outside).ContinuationChecks actions phases = source.ContinuationChecks actions phases :=
  receiverCast_observe (fun forest => Code world plan (.running forest)) (fun _ source => source.ContinuationChecks actions phases) _ _ _ source

@[simp] theorem Code.runningAssocReceiver_bounds
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} (first : Forest firstHints) (second : Forest secondHints)
    (outside : Forest outsideHints) {plan : Plan dependencies} (source : Code world plan (.running (first.append (second.append outside)))) :
    ofCode (source.runningAssocReceiver first second outside) = ofCode source :=
  receiverCast_observe (fun forest => Code world plan (.running forest)) (fun _ source => ofCode source) _ _ _ source

theorem Code.runningAssocReceiver_heq
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} (first : Forest firstHints) (second : Forest secondHints)
    (outside : Forest outsideHints) {plan : Plan dependencies} (source : Code world plan (.running (first.append (second.append outside)))) :
    HEq (source.runningAssocReceiver first second outside) source :=
  receiverCast_heq (fun forest => Code world plan (.running forest)) _ _ _ source

@[simp] theorem Retained.assocReceiver_interpretations
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} (first : Forest firstHints) (second : Forest secondHints)
    (outside : Forest outsideHints) {saved : Forest savedHints} (source : Retained world saved (first.append (second.append outside))) :
    (source.assocReceiver first second outside).InterpretationChecks outward = source.InterpretationChecks outward :=
  receiverCast_observe (fun forest => Retained world saved forest) (fun _ source => source.InterpretationChecks outward) _ _ _ source

@[simp] theorem Retained.assocReceiver_continuations
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} (first : Forest firstHints) (second : Forest secondHints)
    (outside : Forest outsideHints) {saved : Forest savedHints} (source : Retained world saved (first.append (second.append outside))) :
    (source.assocReceiver first second outside).ContinuationChecks actions phases = source.ContinuationChecks actions phases :=
  receiverCast_observe (fun forest => Retained world saved forest) (fun _ source => source.ContinuationChecks actions phases) _ _ _ source

@[simp] theorem Retained.assocReceiver_bounds
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} (first : Forest firstHints) (second : Forest secondHints)
    (outside : Forest outsideHints) {saved : Forest savedHints} (source : Retained world saved (first.append (second.append outside))) :
    ofCapability (source.assocReceiver first second outside) = ofCapability source :=
  receiverCast_observe (fun forest => Retained world saved forest) (fun _ source => ofCapability source) _ _ _ source

theorem Retained.assocReceiver_heq
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} (first : Forest firstHints) (second : Forest secondHints)
    (outside : Forest outsideHints) {saved : Forest savedHints} (source : Retained world saved (first.append (second.append outside))) :
    HEq (source.assocReceiver first second outside) source :=
  receiverCast_heq (fun forest => Retained world saved forest) _ _ _ source

/-- Expand a compact prefix only as far as needed to keep the original suffix.
No operation capability, permission, or successful source judgment is an input. -/
def prependSource {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} {first : Forest firstHints} {second : Forest secondHints}
    {outside : Forest outsideHints} (inside : Interfaces world first) (tail : Retained world second outside) :
    Retained world (first.append second) outside :=
  match inside with
  | .nil => tail
  | .plain _ required footprint declared rest =>
      .plain (.operations required footprint declared) (prependSource rest tail)
  | .handler _ rest => .handler (prependSource rest tail)
  | .cell rest => .cell (prependSource rest tail)
  | .cleanup _ required footprint declared rest =>
      .cleanup (.operations required footprint declared) (prependSource rest tail)
  | .running rest => .running (prependSource rest tail)
  | .live _ saved rest => .live (.operations saved) (prependSource rest tail)
  | .spent rest => .spent (prependSource rest tail)

/-- Construct the joined annotation from the two actual source trees. Current,
callback and dormant code is retained by index transport, not reconstruction. -/
def Retained.joinSource {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} {first : Forest firstHints} {second : Forest secondHints}
    {outside : Forest outsideHints}
    (inside : Retained world first (second.append outside)) (tail : Retained world second outside) :
    Retained world (first.append second) outside :=
  match inside with
  | .operations interfaces => prependSource interfaces tail
  | .plain (rest := rest) code next =>
      .plain (code.assocReceiver rest second outside) (next.joinSource tail)
  | .handler next => .handler (next.joinSource tail)
  | .cell next => .cell (next.joinSource tail)
  | .cleanup (rest := rest) code next =>
      .cleanup (code.runningAssocReceiver rest second outside) (next.joinSource tail)
  | .running next => .running (next.joinSource tail)
  | .live (rest := rest) saved next =>
      .live (saved.assocReceiver rest second outside) (next.joinSource tail)
  | .spent next => .spent (next.joinSource tail)

theorem prependSource_interpretations
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} {first : Forest firstHints} {second : Forest secondHints}
    {outside : Forest outsideHints} (inside : Interfaces world first) (tail : Retained world second outside) :
    (prependSource inside tail).InterpretationChecks outward ↔
      inside.check (secondScope.append outsideScope) = true ∧ tail.InterpretationChecks outward := by
  induction inside <;>
    simp_all [prependSource, Retained.InterpretationChecks, Code.InterpretationChecks,
      Interfaces.check, Bool.and_eq_true, scope_append_assoc, and_assoc] <;> intros <;> rfl

theorem prependSource_continuations
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} {first : Forest firstHints} {second : Forest secondHints}
    {outside : Forest outsideHints} (inside : Interfaces world first) (tail : Retained world second outside) :
    (prependSource inside tail).ContinuationChecks actions phases ↔ tail.ContinuationChecks actions phases := by
  induction inside <;>
    simp_all [prependSource, Retained.ContinuationChecks, Code.ContinuationChecks] <;> rfl

theorem prependSource_bounds
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} {first : Forest firstHints} {second : Forest secondHints}
    {outside : Forest outsideHints} (inside : Interfaces world first) (tail : Retained world second outside) :
    ofCapability (prependSource inside tail) =
      (SourceBoundSnapshots.Retained.absent first).append (ofCapability tail) := by
  induction inside <;>
    simp_all [prependSource, ofCapability, SourceBoundSnapshots.Retained.absent,
      SourceBoundSnapshots.Retained.append, ofCode, Forest.append, Hints.append,
      SourceDependencyCapture.Scope.append]

theorem Retained.joinSource_interpretations
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} {first : Forest firstHints} {second : Forest secondHints}
    {outside : Forest outsideHints}
    (inside : Retained world first (second.append outside)) (tail : Retained world second outside) :
    (inside.joinSource tail).InterpretationChecks outward ↔
      inside.InterpretationChecks outward ∧ tail.InterpretationChecks outward := by
  induction first <;> cases inside <;>
    simp_all [Retained.joinSource, Retained.InterpretationChecks, prependSource_interpretations,
      scope_append_assoc, and_assoc]

theorem Retained.joinSource_continuations
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} {first : Forest firstHints} {second : Forest secondHints}
    {outside : Forest outsideHints}
    (inside : Retained world first (second.append outside)) (tail : Retained world second outside) :
    (inside.joinSource tail).ContinuationChecks actions phases ↔
      inside.ContinuationChecks actions phases ∧ tail.ContinuationChecks actions phases := by
  induction first <;> cases inside <;>
    simp_all [Retained.joinSource, Retained.ContinuationChecks, prependSource_continuations, and_assoc]

theorem Retained.joinSource_bounds
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} {first : Forest firstHints} {second : Forest secondHints}
    {outside : Forest outsideHints}
    (inside : Retained world first (second.append outside)) (tail : Retained world second outside) :
    ofCapability (inside.joinSource tail) = (ofCapability inside).append (ofCapability tail) := by
  induction first <;> cases inside <;>
    simp_all [Retained.joinSource, ofCapability, prependSource_bounds, SourceBoundSnapshots.Retained.append] <;> rfl

/-- Full validation is an exact consequence of the independent equivalences;
there is one source result even when one of the input checks fails. -/
theorem Retained.joinSource_valid
    {firstHints : Hints firstScope} {secondHints : Hints secondScope}
    {outsideHints : Hints outsideScope} {first : Forest firstHints} {second : Forest secondHints}
    {outside : Forest outsideHints}
    (inside : Retained world first (second.append outside)) (tail : Retained world second outside) :
    (inside.joinSource tail).Valid outward actions phases ↔
      inside.Valid outward actions phases ∧ tail.Valid outward actions phases := by
  simp only [Retained.valid_iff_factors, Retained.joinSource_interpretations, Retained.joinSource_continuations]
  simp only [and_assoc, and_left_comm, and_comm]

end Ash.OneShot.SourceScheduledCapabilityAnnotations

#print axioms Ash.OneShot.SourceScheduledSourceJoin.receiverCast_heq
#print axioms Ash.OneShot.SourceScheduledSourceJoin.receiverCast_observe

#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.assocReceiver_interpretations
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.assocReceiver_continuations
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.assocReceiver_bounds
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.assocReceiver_heq
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.runningAssocReceiver_interpretations
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.runningAssocReceiver_continuations
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.runningAssocReceiver_bounds
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Code.runningAssocReceiver_heq
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.assocReceiver_interpretations
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.assocReceiver_continuations
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.assocReceiver_bounds
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.assocReceiver_heq
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.prependSource_interpretations
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.prependSource_continuations
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.prependSource_bounds
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.joinSource_interpretations
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.joinSource_continuations
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.joinSource_bounds
#print axioms Ash.OneShot.SourceScheduledCapabilityAnnotations.Retained.joinSource_valid
