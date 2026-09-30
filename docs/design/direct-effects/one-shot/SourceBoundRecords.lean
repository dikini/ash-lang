import SourceBoundCapture

/-! Retain actual source-record values beside persistent bound annotations.
Payloads may contain queued contextual derivations. This data layer neither
infers a payload from an annotation nor asserts validity at a new receiver.
The existing bound forest, append and operational movement relations fix all
positions. Only the record traversal is new. -/
namespace Ash.OneShot.SourceBoundSnapshots
open SourceContextualHints (Hints)
open SourceRetainedPlans (Forest)
open SourceDeclarationPlans (Plan)
open SourcePlanBounds (Annotation)

universe u

abbrev RecordFamily (world : List Nat) :=
  {dependencies : SourceDependencyAnnotations.Dependencies} →
  {plan : Plan dependencies} → Annotation world plan → Type u

inductive RecordPosition where
  | pending | callback

/-- Include the payload value itself, not merely the annotation to which it
was attached. The traversal observes both ordered position and multiplicity. -/
structure RecordEntry (Payload : RecordFamily.{u} world) where
  position : RecordPosition
  dependencies : SourceDependencyAnnotations.Dependencies
  plan : Plan dependencies
  bounds : Annotation world plan
  payload : Payload bounds

/-- Every original code position carries its own chosen payload. A caller may
use optional records, but this traversal never creates or removes such a value
when moving a retained code position. -/
inductive Retained.Records (Payload : RecordFamily.{u} world) :
    {scope : SourceDependencyCapture.Scope} → {hints : Hints scope} → {forest : Forest hints} →
    Retained world forest → Type u where
  | nil : Records Payload .nil
  | plain (payload : Payload bounds) : Records Payload tail → Records Payload (.plain bounds tail)
  | handler : Records Payload tail → Records Payload (.handler tail)
  | cell : Records Payload tail → Records Payload (.cell tail)
  | cleanup (payload : Payload bounds) : Records Payload tail → Records Payload (.cleanup bounds tail)
  | running : Records Payload tail → Records Payload (.running tail)
  | live : Records Payload saved → Records Payload tail → Records Payload (.live saved tail)
  | spent : Records Payload tail → Records Payload (.spent tail)

variable {Payload : RecordFamily.{u} world}

def Retained.Records.entries {bounds : Retained world forest} (records : bounds.Records Payload) :
    List (RecordEntry Payload) :=
  match records with
  | .nil => []
  | .plain (bounds := code) payload tail => ⟨.pending, _, _, code, payload⟩ :: tail.entries
  | .handler tail | .cell tail | .running tail | .spent tail => tail.entries
  | .cleanup (bounds := code) payload tail => ⟨.callback, _, _, code, payload⟩ :: tail.entries
  | .live saved tail => saved.entries ++ tail.entries

def Retained.Records.append {first : Retained world front} {second : Retained world tail}
    (before : first.Records Payload) (after : second.Records Payload) : (first.append second).Records Payload :=
  match before with
  | .nil => after
  | .plain source rest => .plain source (rest.append after)
  | .handler rest => .handler (rest.append after)
  | .cell rest => .cell (rest.append after)
  | .cleanup source rest => .cleanup source (rest.append after)
  | .running rest => .running (rest.append after)
  | .live saved rest => .live saved (rest.append after)
  | .spent rest => .spent (rest.append after)

theorem Retained.Records.append_entries {first : Retained world front} {second : Retained world tail}
    (before : first.Records Payload) (after : second.Records Payload) :
    (before.append after).entries = before.entries ++ after.entries := by
  induction before <;> simp_all only [Records.append, entries, List.nil_append, List.cons_append, List.append_assoc] <;> rfl

/-- Split payloads at a boundary already fixed by the original bound data.
Dormant branches remain attached to their live frame; no new cut is chosen. -/
noncomputable def Retained.Records.of_append {first : Retained world front} {second : Retained world tail}
    (records : (first.append second).Records Payload) : first.Records Payload × second.Records Payload := by
  induction first with
  | nil => exact ⟨.nil, records⟩
  | plain code rest ih => cases records with
    | plain payload next =>
        let pieces := ih next
        exact ⟨.plain payload pieces.1, pieces.2⟩
  | handler rest ih => cases records with
    | handler next => let pieces := ih next; exact ⟨.handler pieces.1, pieces.2⟩
  | cell rest ih => cases records with
    | cell next => let pieces := ih next; exact ⟨.cell pieces.1, pieces.2⟩
  | cleanup code rest ih => cases records with
    | cleanup payload next => let pieces := ih next; exact ⟨.cleanup payload pieces.1, pieces.2⟩
  | running rest ih => cases records with
    | running next => let pieces := ih next; exact ⟨.running pieces.1, pieces.2⟩
  | live saved rest ihSaved ih => cases records with
    | live dormant next => let pieces := ih next; exact ⟨.live dormant pieces.1, pieces.2⟩
  | spent rest ih => cases records with
    | spent next => let pieces := ih next; exact ⟨.spent pieces.1, pieces.2⟩

/-- Rejoining restores the original data tree, not only its flattened list. -/
theorem Retained.Records.of_append_join {first : Retained world front} {second : Retained world tail}
    (records : (first.append second).Records Payload) :
    records.of_append.1.append records.of_append.2 = records := by
  induction first with
  | nil => rfl
  | plain code rest ih => cases records with
    | plain payload next => exact congrArg (Records.plain payload) (ih next)
  | handler rest ih => cases records with
    | handler next => exact congrArg Records.handler (ih next)
  | cell rest ih => cases records with
    | cell next => exact congrArg Records.cell (ih next)
  | cleanup code rest ih => cases records with
    | cleanup payload next => exact congrArg (Records.cleanup payload) (ih next)
  | running rest ih => cases records with
    | running next => exact congrArg Records.running (ih next)
  | live saved rest ihSaved ih => cases records with
    | live dormant next => exact congrArg (Records.live dormant) (ih next)
  | spent rest ih => cases records with
    | spent next => exact congrArg Records.spent (ih next)

/-- The ordered concatenation contains the same original record values,
including their proof-bearing source data, with no deduplication. -/
theorem Retained.Records.of_append_entries {first : Retained world front} {second : Retained world tail}
    (records : (first.append second).Records Payload) :
    records.of_append.1.entries ++ records.of_append.2.entries = records.entries :=
  (records.of_append.1.append_entries records.of_append.2).symm.trans
    (congrArg Retained.Records.entries records.of_append_join)

/-- Exact capture of decorated source positions. Current code is supplied by
clause selection; all pending records move at the same original bound cut. -/
inductive RecordCapture (owner : Nat) (Payload : RecordFamily.{u} world) :
    {before after : Snapshot world} → before.pending.Records Payload → after.pending.Records Payload → Prop where
  | cut {beforePlan : Plan beforeDependencies} {afterPlan : Plan afterDependencies}
      {saved : Forest savedHints} {waiting : Forest waitingHints}
      {captured : Retained world saved} {tail : Retained world waiting}
      (before : Annotation world beforePlan) (after : Annotation world afterPlan)
      (inside : captured.Records Payload) (outside : tail.Records Payload) :
      RecordCapture owner Payload
        (before := ⟨_, beforePlan, before, _, _, saved.append waiting, captured.append tail⟩)
        (after := ⟨_, afterPlan, after, _, _, .live (owner := owner) saved waiting, .live captured tail⟩)
        (inside.append outside) (.live inside outside)

/-- Exact restoration: saved records precede caller records and the original
waiting tail. The selected live boundary becomes spent, including when the
saved or caller forest contains other dormant captures. -/
inductive RecordResumption (owner : Nat) (Payload : RecordFamily.{u} world) :
    {before after : Snapshot world} → before.pending.Records Payload → after.pending.Records Payload → Prop where
  | cut {plan : Plan dependencies}
      {front : Forest frontHints} {saved : Forest savedHints} {tail : Forest tailHints}
      {before : Retained world front} {captured : Retained world saved} {after : Retained world tail}
      (current : Annotation world plan)
      (caller : before.Records Payload) (inside : captured.Records Payload) (outside : after.Records Payload) :
      RecordResumption owner Payload
        (before := ⟨_, plan, current, _, _, _, before.append (.live (owner := owner) captured after)⟩)
        (after := Snapshot.value (captured.append (before.append (.spent (owner := owner) after))))
        (caller.append (.live inside outside)) (inside.append (caller.append (.spent outside)))

theorem RecordCapture.entries {before after : Snapshot world}
    {records : before.pending.Records Payload} {next : after.pending.Records Payload}
    (step : RecordCapture owner Payload records next) : next.entries = records.entries := by
  cases step with
  | cut before after inside outside => exact (inside.append_entries outside).symm

theorem RecordResumption.entries {before after : Snapshot world}
    {records : before.pending.Records Payload} {next : after.pending.Records Payload}
    (step : RecordResumption owner Payload records next) : records.entries.Perm next.entries := by
  cases step with
  | cut current caller inside outside =>
      dsimp only [Snapshot.value]
      simp only [Retained.Records.append_entries, Retained.Records.entries]
      simpa only [List.append_assoc] using
        (List.perm_append_comm (l₁ := caller.entries) (l₂ := inside.entries)).append_right outside.entries

/-- The operational capture fixes the split. Reuse exact record splitting;
no payload or future source judgment is chosen at the successor. -/
theorem Captured.carry_records {before after : Snapshot world}
    (step : Captured owner before after) (records : before.pending.Records Payload) :
    ∃ next : after.pending.Records Payload, RecordCapture owner Payload records next := by
  cases step with
  | cut before after captured tail =>
      have joined := records.of_append_join
      generalize known : records.of_append = pieces at *
      rcases pieces with ⟨inside, outside⟩
      refine ⟨.live inside outside, ?_⟩
      rw [← joined]
      exact .cut before after inside outside

/-- The exact operational resumption determines record restoration. This
preserves original source data, not validity under the changed receiver. -/
theorem Resumed.carry_records {before after : Snapshot world}
    (step : Resumed owner before after) (records : before.pending.Records Payload) :
    ∃ next : after.pending.Records Payload, RecordResumption owner Payload records next := by
  cases step with
  | cut current front saved tail =>
      dsimp only [Snapshot.value]
      have joined := records.of_append_join
      generalize known : records.of_append = pieces at *
      rcases pieces with ⟨caller, rest⟩
      cases rest with
      | live captured waiting =>
          refine ⟨captured.append (caller.append (.spent waiting)), ?_⟩
          rw [← joined]
          exact .cut current caller captured waiting

end Ash.OneShot.SourceBoundSnapshots

#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Records.append_entries
#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Records.of_append_entries
#print axioms Ash.OneShot.SourceBoundSnapshots.Retained.Records.of_append_join
#print axioms Ash.OneShot.SourceBoundSnapshots.Captured.carry_records
#print axioms Ash.OneShot.SourceBoundSnapshots.Resumed.carry_records

#print axioms Ash.OneShot.SourceBoundSnapshots.RecordCapture.entries
#print axioms Ash.OneShot.SourceBoundSnapshots.RecordResumption.entries
